module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0127

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepLaws
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private lemma beta_baseChange {E : Type} [Field E] [NumberField E] {n : ℕ}
    (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E))
    (hβ : ∀ (v : Fin n → 𝓞 E) i, β (1 ⊗ₜ v) i = (v i : E)) (b : 𝓞 E)
    (z : ℚ ⊗[ℤ] (Fin n → 𝓞 E)) :
    β ((DistribSMul.toLinearMap ℤ (Fin n → 𝓞 E) b).baseChange ℚ z) = (b : E) • β z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]
  | tmul q v =>
    have h1 : ∀ w : Fin n → 𝓞 E, q ⊗ₜ[ℤ] w = q • ((1 : ℚ) ⊗ₜ[ℤ] w) := by
      intro w
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h2 : (DistribSMul.toLinearMap ℤ (Fin n → 𝓞 E) b).baseChange ℚ (q ⊗ₜ[ℤ] v)
        = q ⊗ₜ[ℤ] (b • v) := by
      rw [LinearMap.baseChange_tmul]
      rfl
    rw [h2, h1 (b • v), h1 v, map_smul, map_smul]
    funext i
    simp only [Pi.smul_apply, hβ]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingOfIntegers.coe_eq_algebraMap, Rat.smul_def, mul_left_comm, Algebra.smul_def]

theorem UpperTheory.Gal.W2.Seed.pRepLaws :
    RepLaws := by
  rintro E _ _ _ A n rep ⟨β, hβ, hr⟩
  have hβ1 : ∀ v : Fin n → 𝓞 E, β (1 ⊗ₜ v) = fun i => (v i : E) := fun v => funext (hβ v)
  have hsc : ∀ c : 𝓞 E, rep (algebraMap E (Matrix (Fin n) (Fin n) E) c)
      = (DistribSMul.toLinearMap ℤ (Fin n → 𝓞 E) c).baseChange ℚ := by
    intro c
    refine LinearMap.ext fun z => β.injective ?_
    rw [hr, beta_baseChange β hβ c z, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  refine ⟨?_, ?_, hsc, ?_⟩
  · intro x y hxy
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    obtain ⟨z, rfl⟩ := β.surjective w
    simp only [Matrix.toLin'_apply]
    rw [← hr, ← hr, hxy]
  · intro M
    constructor
    · rintro ⟨x, rfl⟩ b
      rw [← hsc, ← map_mul, ← map_mul, Algebra.commutes]
    · intro hM
      let F0 : (Fin n → E) →ₗ[ℚ] (Fin n → E) := β.toLinearMap ∘ₗ M ∘ₗ β.symm.toLinearMap
      have hF0 : ∀ (b : 𝓞 E) w, F0 ((b : E) • w) = (b : E) • F0 w := by
        intro b w
        obtain ⟨z, rfl⟩ := β.surjective w
        have h := congrArg (fun N => β (N z)) (hM b)
        simp only [Module.End.mul_apply] at h
        rw [beta_baseChange β hβ] at h
        simp only [F0, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        rw [← beta_baseChange β hβ, LinearEquiv.symm_apply_apply, h]
      have hF : ∀ (e : E) w, F0 (e • w) = e • F0 w := by
        intro e w
        obtain ⟨b, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
        have hd0 : (algebraMap (𝓞 E) E d) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
        apply smul_right_injective (Fin n → E) hd0
        change algebraMap (𝓞 E) E d • F0 _ = algebraMap (𝓞 E) E d • _
        rw [smul_smul, mul_div_cancel₀ _ hd0]
        have h2 := hF0 d ((algebraMap (𝓞 E) E b / algebraMap (𝓞 E) E d) • w)
        have h3 := hF0 b w
        change F0 (algebraMap (𝓞 E) E d • _) = algebraMap (𝓞 E) E d • _ at h2
        change F0 (algebraMap (𝓞 E) E b • _) = algebraMap (𝓞 E) E b • _ at h3
        rw [← h2, smul_smul, mul_div_cancel₀ _ hd0, h3]
      let F : (Fin n → E) →ₗ[E] (Fin n → E) :=
        { toFun := F0, map_add' := F0.map_add, map_smul' := hF }
      refine ⟨Matrix.toLin'.symm F, ?_⟩
      refine LinearMap.ext fun z => β.injective ?_
      rw [hr]
      have hx : (Matrix.toLin'.symm F) *ᵥ β z = F (β z) := by
        rw [← Matrix.toLin'_apply, LinearEquiv.apply_symm_apply]
      rw [hx]
      simp [F, F0]
  · intro x v
    apply β.injective
    rw [hr, hβ1, hβ1]
    funext i
    exact (RingHom.map_mulVec (algebraMap (𝓞 E) E) x v i).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSetupEx
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

private noncomputable def repOf {E V : Type} [Field E] [Algebra ℚ E] [AddCommGroup V] [Module ℚ V] {n : ℕ}
    (β : V ≃ₗ[ℚ] (Fin n → E)) : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ V :=
  AlgHom.ofLinearMap
    { toFun := fun x => β.symm.toLinearMap ∘ₗ (x.mulVecLin.restrictScalars ℚ) ∘ₗ β.toLinearMap
      map_add' := fun x y => by
        ext v
        simp [Matrix.add_mulVec]
      map_smul' := fun c x => by
        ext v
        simp [Matrix.smul_mulVec] }
    (by ext v; simp)
    (fun x y => by ext v; simp [Matrix.mulVec_mulVec])

private theorem repOf_apply {E V : Type} [Field E] [Algebra ℚ E] [AddCommGroup V] [Module ℚ V] {n : ℕ}
    (β : V ≃ₗ[ℚ] (Fin n → E)) (x : Matrix (Fin n) (Fin n) E) (z : V) : β (repOf β x z) = x *ᵥ β z := by
  simp [repOf]

end UpperTheory.Gal.W2.Seed

theorem UpperTheory.Gal.W2.Seed.pSetupEx :
    FormOKSt → FormPerfSt → SigSt → DomSt → AtPEx → RepEx → RepLaws → RepAdj → Orient → SetupEx := by
  intro hF hFP hS hD hP hR hL hA hO E _ _ _ A n p _ hn hg
  have facts : A.Facts n := ⟨hn, hF E A n, hD E A n hn⟩
  have hs : A.SigOK n := hS E A n hn
  have perf : A.FormPerf n p := hFP E A n p hg.2
  obtain ⟨P⟩ := hP E A p hg.1
  obtain ⟨β, hβ⟩ := hR E n
  have hok : RepOK A n (repOf β) := ⟨β, hβ, repOf_apply β⟩
  obtain ⟨r1, r2, r3, r4⟩ := hL E A n (repOf β) hok
  have radj := hA E A n (repOf β) hok
  obtain ⟨J, j1, j2, j3, j4⟩ := hO E A n hn hs p P (repOf β) hok
  have hsig : ∀ v : InfinitePlace E, sigPos (A.herm n) v.embedding = 1 ↔
      ∃ _ : Fin 1, v = InfinitePlace.mk (P.iotaC.comp P.s) := fun v => by
    have hv := hs v.embedding
    rw [InfinitePlace.mk_embedding] at hv
    have hc : P.iotaC.comp P.s = A.τ₀ := RingHom.ext P.s_C
    rw [hc]
    constructor
    · intro h
      by_cases hv0 : v = InfinitePlace.mk A.τ₀
      · exact ⟨0, hv0⟩
      · have h0 := (hv.2 hv0).1
        omega
    · rintro ⟨_, h⟩
      exact (hv.1 h).1
  refine ⟨⟨facts, hs, hg, perf, P, ?_, ?_, ?_⟩⟩
  · exact
      { e := RingEquiv.refl E
        n_eq := rfl
        rep := repOf β
        rep_inj := r1
        rep_range := r2
        rep_F := fun c => r3 c
        adj := radj
        ρp := P.ρp
        ρp_eq := P.ρp_eq
        s := fun _ => P.s
        s_C := fun _ x => P.s_C x
        w := fun _ => P.w
        s_P := fun _ x => P.s_P x
        sig := hsig
        orient := ⟨J, j1, j2, j3, j4⟩ }
  · intro x; rfl
  · exact r4
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSigSt
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private theorem UpperTheory.Gal.W2.Seed.card_signs {n : ℕ} (hn : 1 ≤ n) (r : Fin n → ℝ)
    (h0 : ∀ i : Fin n, (i : ℕ) = 0 → 0 < r i) (h1 : ∀ i : Fin n, (i : ℕ) ≠ 0 → r i < 0) :
    Fintype.card {i // 0 < r i} = 1 ∧ Fintype.card {i // r i < 0} = n - 1 := by
  have hiff : ∀ i : Fin n, r i < 0 ↔ ¬ 0 < r i := by
    intro i
    by_cases hi : (i : ℕ) = 0
    · have hp := h0 i hi
      exact ⟨fun h => by linarith, fun h => absurd hp h⟩
    · have hq := h1 i hi
      exact ⟨fun _ h' => by linarith, fun _ => hq⟩
  have hc1 : Fintype.card {i // 0 < r i} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨0, hn⟩, h0 _ rfl⟩, fun ⟨j, hj⟩ => ?_⟩
    apply Subtype.ext
    apply Fin.ext
    by_contra hne
    exact absurd hj (not_lt.mpr (le_of_lt (h1 j hne)))
  refine ⟨hc1, ?_⟩
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hiff), Fintype.card_subtype_compl, hc1,
    Fintype.card_fin]

theorem UpperTheory.Gal.W2.Seed.pSigSt :
    HdSign → SigSt := by
  intro hS E _ _ _ A n hn τ
  have hdiag : gramAt (A.H n) τ = diagonal (fun i => ((τ (A.hd n i : E)).re : ℂ)) := by
    ext i j
    simp only [gramAt, Arith.H, transpose_apply, map_apply, diagonal_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, if_pos rfl, Complex.ext_iff]
      simp [(hS E A n τ i).1]
    · simp [h, Ne.symm h]
  have aux : ∀ (r : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian),
      M = diagonal (fun i => (r i : ℂ)) →
      sigPosH hM = Fintype.card {i // 0 < r i} ∧ sigNegH hM = Fintype.card {i // r i < 0} := by
    rintro r M hM rfl
    exact sigPosH_sigNegH_diagonal n r hM
  obtain ⟨hp, hneg⟩ := aux _ _ (isHermitian_gramAt (A.herm n) τ) hdiag
  refine ⟨fun hτ => ?_, fun hτ => ?_⟩
  · have hcs := card_signs hn _ (fun i hi => (hS E A n τ i).2.2.1 ⟨hτ, hi⟩)
      (fun i hi => (hS E A n τ i).2.2.2 (fun h => hi h.2))
    exact ⟨hp.trans hcs.1, hneg.trans hcs.2⟩
  · have hall : ∀ i : Fin n, (τ (A.hd n i : E)).re < 0 := fun i =>
      (hS E A n τ i).2.2.2 (fun h => hτ h.1)
    refine ⟨hp.trans ?_, hneg.trans ?_⟩
    · rw [Fintype.card_eq_zero_iff]
      exact ⟨fun ⟨i, hi⟩ => absurd hi (not_lt.mpr (le_of_lt (hall i)))⟩
    · rw [Fintype.card_congr (Equiv.subtypeUnivEquiv hall), Fintype.card_fin]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTraceType
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem tau_bar (A : Arith E) (τ : E →+* ℂ) :
    τ ((algebraMap (𝓞 E) E) (A.bar A.ω)) = (starRingEnd ℂ) (τ (A.ω : E)) := by
  show τ ((A.bar A.ω : 𝓞 E) : E) = _
  rw [A.bar_eq, IsCMField.complexEmbedding_complexConj]

private theorem tau_add (A : Arith E) (τ : E →+* ℂ) :
    τ (A.ω : E) + (starRingEnd ℂ) (τ (A.ω : E)) = (A.tr : ℂ) := by
  have h1 := congrArg (fun x : 𝓞 E => τ (x : E)) A.tr_eq
  simp only [map_add (f := _), map_intCast] at h1
  rw [tau_bar A τ] at h1
  exact h1

private theorem tau_mul (A : Arith E) (τ : E →+* ℂ) :
    τ (A.ω : E) * (starRingEnd ℂ) (τ (A.ω : E)) = (A.nm : ℂ) := by
  have h1 := congrArg (fun x : 𝓞 E => τ (x : E)) A.nm_eq
  simp only [map_mul, map_intCast] at h1
  rw [tau_bar A τ] at h1
  exact h1

private theorem tau_im (A : Arith E) (τ : E →+* ℂ) : (τ (A.ω : E)).im ≠ 0 := by
  intro h
  have hc : (starRingEnd ℂ) (τ (A.ω : E)) = τ (A.ω : E) := Complex.conj_eq_iff_im.2 h
  have h1 := tau_add A τ
  have h2 := tau_mul A τ
  rw [hc] at h1 h2
  have h3 : ((A.tr ^ 2 - 4 * A.nm : ℤ) : ℂ) = 0 := by
    push_cast
    rw [← h1, ← h2]
    ring
  have h4 : A.tr ^ 2 - 4 * A.nm = 0 := by exact_mod_cast h3
  have := A.disc_neg
  linarith

private theorem tau_cases (A : Arith E) (τ : E →+* ℂ) :
    τ (A.ω : E) = A.τ₀ (A.ω : E) ∨ τ (A.ω : E) = (starRingEnd ℂ) (A.τ₀ (A.ω : E)) := by
  have h : (τ (A.ω : E) - A.τ₀ (A.ω : E)) * (τ (A.ω : E) - (starRingEnd ℂ) (A.τ₀ (A.ω : E))) = 0 := by
    linear_combination τ (A.ω : E) * tau_add A τ - tau_mul A τ - τ (A.ω : E) * tau_add A A.τ₀ + tau_mul A A.τ₀
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (sub_eq_zero.1 h)

private theorem rho_ne (A : Arith E) : A.τ₀ (A.ω : E) ≠ (starRingEnd ℂ) (A.τ₀ (A.ω : E)) :=
  fun h => tau_im A A.τ₀ (Complex.conj_eq_iff_im.1 h.symm)

private theorem conj_mem (A : Arith E) (τ : E →+* ℂ) :
    (ComplexEmbedding.conjugate τ) (A.ω : E) = (starRingEnd ℂ) (τ (A.ω : E)) :=
  ComplexEmbedding.conjugate_coe_eq τ _

private theorem sum_conj (A : Arith E) [Fintype (Phi A)]
    [DecidablePred fun τ : E →+* ℂ => τ (A.ω : E) = (starRingEnd ℂ) (A.τ₀ (A.ω : E))]
    (f : (E →+* ℂ) → ℂ) :
    ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (A.ω : E) = (starRingEnd ℂ) (A.τ₀ (A.ω : E))), f τ =
      ∑ τ : Phi A, f (ComplexEmbedding.conjugate τ.1) := by
  classical
  refine Eq.trans ?_ (Finset.sum_subtype
    (Finset.univ.filter (fun τ : E →+* ℂ => τ (A.ω : E) = A.τ₀ (A.ω : E))) (by simp)
    (fun τ => f (ComplexEmbedding.conjugate τ)))
  refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
  · intro τ hτ
    have hτ' := (Finset.mem_filter.1 hτ).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [conj_mem, hτ', Complex.conj_conj]
  · intro τ hτ
    have hτ' := (Finset.mem_filter.1 hτ).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [conj_mem, hτ']
  · intro τ _
    exact star_star τ
  · intro τ _
    exact star_star τ
  · intro τ _
    rw [show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ from star_star τ]

private theorem trace_eq (x : E) :
    (((Algebra.trace ℚ E x : ℚ) : ℂ)) = ∑ τ : E →+* ℂ, τ x := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := x)
  rw [eq_ratCast] at h
  rw [h]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)

end UpperTheory.Gal.W2.Seed

open Classical in
theorem UpperTheory.Gal.W2.Seed.pTraceType :
    TraceType := by
  intro E _ _ _ A
  have h2 := fun f => sum_conj A f
  refine ⟨fun x => ?_, h2, fun v => ?_, tau_im A A.τ₀⟩
  · apply Complex.ofReal_injective
    have h1 : ((((Algebra.trace ℚ E x : ℚ) : ℝ)) : ℂ) = ((Algebra.trace ℚ E x : ℚ) : ℂ) := by push_cast; rfl
    rw [h1, trace_eq x,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ : E →+* ℂ => τ (A.ω : E) = A.τ₀ (A.ω : E))]
    have h3 : Finset.univ.filter (fun τ : E →+* ℂ => ¬ τ (A.ω : E) = A.τ₀ (A.ω : E)) =
        Finset.univ.filter (fun τ : E →+* ℂ => τ (A.ω : E) = (starRingEnd ℂ) (A.τ₀ (A.ω : E))) := by
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        exact (tau_cases A τ).resolve_left h
      · intro h h'
        exact rho_ne A (h'.symm.trans h)
    have h4 : ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (A.ω : E) = A.τ₀ (A.ω : E)), τ x =
        ∑ τ : Phi A, τ.1 x := Finset.sum_subtype _ (by simp) _
    rw [h3, h2 (fun τ => τ x), h4, ← Finset.sum_add_distrib, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]
  · have hmem : ∃ τ : Phi A, InfinitePlace.mk τ.1 = v := by
      rcases tau_cases A v.embedding with h | h
      · exact ⟨⟨v.embedding, h⟩, v.mk_embedding⟩
      · refine ⟨⟨ComplexEmbedding.conjugate v.embedding, ?_⟩, ?_⟩
        · rw [conj_mem, h, Complex.conj_conj]
        · rw [InfinitePlace.mk_conjugate_eq, v.mk_embedding]
    obtain ⟨τ, hτ⟩ := hmem
    refine ⟨τ, hτ, fun σ hσ => ?_⟩
    rcases InfinitePlace.mk_eq_iff.1 (hσ.trans hτ.symm) with h | h
    · exact Subtype.ext h
    · exfalso
      have h5 : τ.1 (A.ω : E) = (starRingEnd ℂ) (σ.1 (A.ω : E)) := by rw [← h, conj_mem]
      rw [τ.2, σ.2] at h5
      exact rho_ne A h5
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PUnitMod
section
noncomputable section

open NumberField

namespace UpperTheory.Gal.W2.Seed

private theorem norm_cast_eq_one {E : Type} [Field E] [NumberField E] (M : ℕ) (b : 𝓞 E) :
    ((Algebra.norm ℤ (1 + (M : 𝓞 E) * b) : ℤ) : ZMod M) = 1 := by
  classical
  let bs := Module.Free.chooseBasis ℤ (𝓞 E)
  rw [Algebra.norm_eq_matrix_det bs, ← eq_intCast (Int.castRingHom (ZMod M)), RingHom.map_det]
  simp only [map_add (f := _), map_one, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero,
    Matrix.det_one, CharP.cast_eq_zero]

theorem pUnitMod : UnitMod := by
  intro E _ _ M c b _ h
  refine ⟨(Algebra.norm ℤ c).natAbs, ?_, ?_⟩
  · rw [← ZMod.isUnit_iff_coprime]
    have key := norm_cast_eq_one (E := E) M b
    rw [← h] at key
    rcases Int.natAbs_eq (Algebra.norm ℤ c) with hn | hn
    · rw [hn, Int.cast_natCast] at key
      rw [key]
      exact isUnit_one
    · rw [hn, Int.cast_neg, Int.cast_natCast, neg_eq_iff_eq_neg] at key
      rw [key]
      exact isUnit_one.neg
  · have hm := Ideal.absNorm_mem (Ideal.span ({c} : Set (𝓞 E)))
    rw [Ideal.absNorm_span_singleton, Ideal.mem_span_singleton] at hm
    obtain ⟨c', hc'⟩ := hm
    exact ⟨c', hc'.symm⟩

end UpperTheory.Gal.W2.Seed
end
end

