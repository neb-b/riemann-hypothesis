module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsBasisCols
section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.MatSat

theorem exists_basis_cols {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (A : Matrix (β ⊕ γ) β O) (hA : Function.Injective A.mulVecLin) :
    ∃ (P : Matrix (β ⊕ γ) (β ⊕ γ) O) (a : β → O) (s u : Matrix β β O),
      IsUnit P.det ∧ (∀ j, a j ≠ 0) ∧ A * s = P.toCols₁ * Matrix.diagonal a ∧
        A = P.toCols₁ * u := by
  classical
  obtain ⟨n, S⟩ := Submodule.smithNormalForm (Pi.basisFun O (β ⊕ γ)) (LinearMap.range A.mulVecLin)
  obtain ⟨φ⟩ : Nonempty (Fin n ≃ β) :=
    ⟨S.bN.indexEquiv ((Pi.basisFun O β).map (LinearEquiv.ofInjective A.mulVecLin hA))⟩
  obtain ⟨f', hf'⟩ : ∃ f' : β ↪ β ⊕ γ, ∀ b, f' b = S.f (φ.symm b) :=
    ⟨φ.symm.toEmbedding.trans S.f, fun _ => rfl⟩
  have hcard : Fintype.card γ = Fintype.card ((Set.range f')ᶜ : Set (β ⊕ γ)) := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective f'.injective, Fintype.card_sum]
    omega
  obtain ⟨e, he⟩ : ∃ e : β ⊕ γ ≃ β ⊕ γ, ∀ b, e (Sum.inl b) = f' b :=
    ⟨(Equiv.sumCongr (Equiv.ofInjective f' f'.injective) (Fintype.equivOfCardEq hcard)).trans
      (Equiv.Set.sumCompl (Set.range f')), fun b => by simp⟩
  obtain ⟨P, hPdef⟩ : ∃ P : Matrix (β ⊕ γ) (β ⊕ γ) O,
      P = (Pi.basisFun O (β ⊕ γ)).toMatrix (S.bM.reindex e.symm) := ⟨_, rfl⟩
  have hPdet : IsUnit P.det := by
    letI := (Pi.basisFun O (β ⊕ γ)).invertibleToMatrix (S.bM.reindex e.symm)
    rw [hPdef]
    exact Matrix.isUnit_det_of_invertible _
  have hP1 : ∀ i b, P.toCols₁ i b = S.bM (f' b) i := by
    intro i b
    show P i (Sum.inl b) = _
    rw [hPdef, Module.Basis.toMatrix_apply, Pi.basisFun_repr, Module.Basis.reindex_apply,
      Equiv.symm_symm, he]
  have hpre : ∀ b, ∃ v : β → O, A *ᵥ v = (S.bN (φ.symm b) : β ⊕ γ → O) := by
    intro b
    obtain ⟨v, hv⟩ := LinearMap.mem_range.1 (S.bN (φ.symm b)).2
    exact ⟨v, hv⟩
  choose pre hpre using hpre
  obtain ⟨s, hs⟩ : ∃ s : Matrix β β O, ∀ i b, s i b = pre b i :=
    ⟨Matrix.of fun i b => pre b i, fun _ _ => rfl⟩
  have ha : ∀ b, S.a (φ.symm b) ≠ 0 := by
    intro b h
    have h1 := S.snf (φ.symm b)
    rw [h, zero_smul] at h1
    exact S.bN.ne_zero _ ((Submodule.coe_eq_zero).1 h1)
  obtain ⟨u, hu⟩ : ∃ u : Matrix β β O, ∀ b' b, u b' b =
      S.bN.repr ⟨A.mulVecLin (Pi.single b 1), LinearMap.mem_range_self _ _⟩ (φ.symm b') *
        S.a (φ.symm b') :=
    ⟨Matrix.of fun b' b => S.bN.repr ⟨A.mulVecLin (Pi.single b 1), LinearMap.mem_range_self _ _⟩
      (φ.symm b') * S.a (φ.symm b'), fun _ _ => rfl⟩
  refine ⟨P, fun b => S.a (φ.symm b), s, u, hPdet, ha, ?_, ?_⟩
  · ext i b
    rw [Matrix.mul_diagonal, hP1, Matrix.mul_apply]
    have h1 := congrFun (hpre b) i
    simp only [Matrix.mulVec, dotProduct] at h1
    simp only [hs]
    rw [h1, S.snf, hf']
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · ext i b
    have hw := S.bN.sum_repr ⟨A.mulVecLin (Pi.single b 1), LinearMap.mem_range_self _ _⟩
    have hw' := congrArg (fun v : LinearMap.range A.mulVecLin => (v : β ⊕ γ → O) i) hw
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, S.snf] at hw'
    have hcol : (A.mulVecLin (Pi.single b 1)) i = A i b := by
      simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [Matrix.mul_apply]
    refine hcol.symm.trans (hw'.symm.trans ?_)
    simp only [hP1, hu, hf']
    refine Fintype.sum_equiv φ _ _ fun k => ?_
    simp only [Equiv.symm_apply_apply]
    ring

theorem exists_saturation {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] {β γ : Type} [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] (C : Matrix (β ⊕ γ) β K)
    (hC : ∃ L : Matrix β (β ⊕ γ) K, L * C = 1) :
    ∃ (t : GL β K) (C₀ : Matrix (β ⊕ γ) β O) (D : Matrix (β ⊕ γ) γ O),
      C * (t : Matrix β β K) = C₀.map (algebraMap O K) ∧
        IsUnit (Matrix.fromCols C₀ D).det := by
  classical
  obtain ⟨L, hL⟩ := hC
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
    (fun p : (β ⊕ γ) × β => C p.1 p.2)
  have hb' : ∀ p : (β ⊕ γ) × β, ∃ x : O,
      algebraMap O K x = algebraMap O K (b : O) * C p.1 p.2 := by
    intro p
    obtain ⟨x, hx⟩ := RingHom.mem_rangeS.1 (hb p)
    exact ⟨x, by rw [hx, Algebra.smul_def]⟩
  choose c hc using hb'
  have hbne : algebraMap O K (b : O) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : Matrix (β ⊕ γ) β O,
      C₁.map (algebraMap O K) = algebraMap O K (b : O) • C :=
    ⟨Matrix.of fun i j => c (i, j), by ext i j; simp [hc]⟩
  have hinj : Function.Injective C₁.mulVecLin := by
    intro v w hvw
    have h1 : C₁ *ᵥ v = C₁ *ᵥ w := hvw
    have h2 : ∀ x : β → O, (algebraMap O K) ∘ (C₁ *ᵥ x) =
        algebraMap O K (b : O) • (C *ᵥ ((algebraMap O K) ∘ x)) := by
      intro x
      funext i
      rw [Function.comp_apply, RingHom.map_mulVec, hC₁]
      first
      | rw [Matrix.smul_mulVec]
      | simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    have e1 := h2 v
    have e2 := h2 w
    rw [h1] at e1
    have h3 : C *ᵥ ((algebraMap O K) ∘ v) = C *ᵥ ((algebraMap O K) ∘ w) :=
      smul_right_injective (β ⊕ γ → K) hbne (e1.symm.trans e2)
    have h4 : (algebraMap O K) ∘ v = (algebraMap O K) ∘ w := by
      have := congrArg (fun z => L *ᵥ z) h3
      simpa only [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec] using this
    funext i
    exact IsFractionRing.injective O K (congrFun h4 i)
  obtain ⟨P, a, s, u, hP, -, -, hu⟩ := exists_basis_cols C₁ hinj
  have hCw : C = (P.toCols₁.map (algebraMap O K)) *
      ((algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K)) := by
    have e1 : algebraMap O K (b : O) • C = (P.toCols₁.map (algebraMap O K)) * (u.map (algebraMap O K)) := by
      rw [← hC₁, hu, Matrix.map_mul]
    rw [Matrix.mul_smul, ← e1, smul_smul, inv_mul_cancel₀ hbne, one_smul]
  have hLw : (L * P.toCols₁.map (algebraMap O K)) *
      ((algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K)) = 1 := by
    rw [Matrix.mul_assoc, ← hCw, hL]
  have hwL : ((algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K)) *
      (L * P.toCols₁.map (algebraMap O K)) = 1 := by
    first
    | exact mul_eq_one_comm.1 hLw
    | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) |>.1 hLw
  refine ⟨⟨L * P.toCols₁.map (algebraMap O K),
    (algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K), hLw, hwL⟩, P.toCols₁, P.toCols₂, ?_, ?_⟩
  · show C * (L * P.toCols₁.map (algebraMap O K)) = P.toCols₁.map (algebraMap O K)
    rw [hCw, Matrix.mul_assoc, hwL, Matrix.mul_one]
  · rw [Matrix.fromCols_toCols]
    exact hP

end GlobalTheory.CompanionTheory.MatSat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsEqMulApplyZero
section
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal

namespace GlobalTheory.CompanionTheory.WeilCoinv

theorem exists_dotProduct_ne_one {k : Type} [Field k] {κ : Type} [Fintype κ] {ψ : AddChar k ℂ} (hψ : ψ ≠ 1)
    {x : κ → k} (hx : x ≠ 0) : ∃ y : κ → k, ψ (x ⬝ᵥ y) ≠ 1 := by
  classical
  obtain ⟨t, ht⟩ := AddChar.ne_one_iff.mp hψ
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hi' : x i ≠ 0 := hi
  refine ⟨Pi.single i (t / x i), ?_⟩
  have hxt : x i * (t / x i) = t := by field_simp
  rw [dotProduct_single, hxt]
  exact ht

theorem exists_eq_mul_apply_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (κ : Type) [Fintype κ] (ψ : AddChar k ℂ),
    Continuous ψ → ψ ≠ 1 → ∀ l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ,
    (∀ y, ∀ φ ∈ SB (κ → k), l (schr ψ (0, y) φ) = l φ) → ∃ a : ℂ, ∀ φ ∈ SB (κ → k), l φ = a * φ 0 := by
  intro k _ _ _ _ _ κ _ ψ hψc hψ l hl
  classical
  haveI : NonarchimedeanAddGroup k := GlobalTheory.WeilM.nonarch_field k
  haveI : NonarchimedeanAddGroup (κ → k) := GlobalTheory.WeilM.nonarch_pi k κ
  have hψlc : IsLocallyConstant ψ := GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψc
  have hχ : ∀ y : κ → k, IsLocallyConstant (fun x : κ → k => ψ (x ⬝ᵥ y)) := fun y =>
    hψlc.comp_continuous (continuous_id.dotProduct continuous_const)
  have key : ∀ t : Finset (κ → k), ∀ φ ∈ SB (κ → k),
      (∀ x, φ x ≠ 0 → ∃ y ∈ t, ψ (x ⬝ᵥ y) ≠ 1) → l φ = 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro φ _ h
      have hz : φ = 0 := funext fun x => by
        by_contra hx
        obtain ⟨y, hy, -⟩ := h x hx
        simp at hy
      rw [hz, map_zero]
    | @insert y t hyt ih =>
      intro φ hφ h
      obtain ⟨hφl, hφc⟩ := hφ
      obtain ⟨φ₁, hφ₁⟩ : ∃ f : (κ → k) → ℂ, f = fun x => if ψ (x ⬝ᵥ y) = 1 then φ x else 0 := ⟨_, rfl⟩
      obtain ⟨g, hg⟩ : ∃ f : (κ → k) → ℂ,
          f = fun x => if ψ (x ⬝ᵥ y) = 1 then 0 else φ x / (ψ (x ⬝ᵥ y) - 1) := ⟨_, rfl⟩
      have hφ₁SB : φ₁ ∈ SB (κ → k) := by
        refine ⟨?_, hφc.mono ?_⟩
        · rw [hφ₁]
          exact (hχ y).comp₂ hφl (fun a b => if a = 1 then b else 0)
        · intro x hx
          rw [Function.mem_support] at hx ⊢
          intro h0
          apply hx
          simp [hφ₁, h0]
      have hgSB : g ∈ SB (κ → k) := by
        refine ⟨?_, hφc.mono ?_⟩
        · rw [hg]
          exact (hχ y).comp₂ hφl (fun a b => if a = 1 then 0 else b / (a - 1))
        · intro x hx
          rw [Function.mem_support] at hx ⊢
          intro h0
          apply hx
          simp [hg, h0]
      have hsch : schr ψ ((0 : κ → k), y) g = fun x => ψ (x ⬝ᵥ y) * g x := by
        funext x
        simp [GlobalTheory.WeilM.schr]
      have hdiff : φ = φ₁ + (schr ψ ((0 : κ → k), y) g - g) := by
        rw [hsch]
        funext x
        simp only [Pi.add_apply, Pi.sub_apply, hφ₁, hg]
        split_ifs with h1
        · simp
        · have hne : ψ (x ⬝ᵥ y) - 1 ≠ 0 := sub_ne_zero.mpr h1
          rw [zero_add, ← sub_one_mul]
          field_simp
      rw [hdiff, map_add (f := _), map_sub, hl y g hgSB, sub_self, add_zero]
      refine ih φ₁ hφ₁SB ?_
      intro x hx
      have hx1 : ψ (x ⬝ᵥ y) = 1 := by
        by_contra hne
        apply hx
        simp [hφ₁, hne]
      have hx2 : φ x ≠ 0 := by
        intro h0
        apply hx
        simp [hφ₁, h0]
      obtain ⟨y', hy', hy'ne⟩ := h x hx2
      rcases Finset.mem_insert.mp hy' with rfl | hy't
      · exact absurd hx1 hy'ne
      · exact ⟨y', hy't, hy'ne⟩
  have vanish : ∀ φ ∈ SB (κ → k), φ 0 = 0 → l φ = 0 := by
    intro φ hφ h0
    obtain ⟨hφl, hφc⟩ := hφ
    have hsupp : IsClosed (Function.support φ) := (hφl.isOpen_fiber 0).isClosed_compl
    have hK : IsCompact (Function.support φ) := by
      have hc := hφc.isCompact
      rwa [tsupport, hsupp.closure_eq] at hc
    have hcov : Function.support φ ⊆ ⋃ y : κ → k, {x | ψ (x ⬝ᵥ y) ≠ 1} := by
      intro x hx
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact hx h0
      obtain ⟨y, hy⟩ := exists_dotProduct_ne_one hψ hx0
      exact Set.mem_iUnion.mpr ⟨y, hy⟩
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y : κ → k => {x | ψ (x ⬝ᵥ y) ≠ 1})
      (fun y => ((hχ y).isClosed_fiber 1).isOpen_compl) hcov
    refine key t φ ⟨hφl, hφc⟩ ?_
    intro x hx
    have hxt := ht hx
    simp only [Set.mem_iUnion] at hxt
    obtain ⟨y, hy, hxy⟩ := hxt
    exact ⟨y, hy, hxy⟩
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : κ → k)
  obtain ⟨O, hO⟩ := NonarchimedeanAddGroup.is_nonarchimedean C hC0
  have hOc : IsCompact (O : Set (κ → k)) := hC.of_isClosed_subset O.isClosed hO
  have hO0 : (0 : κ → k) ∈ O := O.zero_mem
  obtain ⟨φ₀, hφ₀d⟩ : ∃ f : (κ → k) → ℂ, f = fun x => if x ∈ O then 1 else 0 := ⟨_, rfl⟩
  have hφ₀ : φ₀ ∈ SB (κ → k) := by
    refine ⟨?_, HasCompactSupport.intro' hOc O.isClosed fun x hx => ?_⟩
    · rw [IsLocallyConstant.iff_exists_open]
      intro x
      by_cases hx : x ∈ O
      · refine ⟨O, O.isOpen, hx, fun x' hx' => ?_⟩
        have hx'' : x' ∈ O := hx'
        simp [hφ₀d, hx, hx'']
      · refine ⟨(O : Set (κ → k))ᶜ, O.isClosed.isOpen_compl, hx, fun x' hx' => ?_⟩
        have hx'' : x' ∉ O := hx'
        simp [hφ₀d, hx, hx'']
    · have hx' : x ∉ O := hx
      simp [hφ₀d, hx']
  refine ⟨l φ₀, fun φ hφ => ?_⟩
  have h1 : φ - φ 0 • φ₀ ∈ SB (κ → k) := Submodule.sub_mem _ hφ (Submodule.smul_mem _ _ hφ₀)
  have h2 : (φ - φ 0 • φ₀) 0 = 0 := by simp [hφ₀d, hO0]
  have h3 := vanish _ h1 h2
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h3
  rw [h3, mul_comm]

end GlobalTheory.CompanionTheory.WeilCoinv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsSkewOfDiagonal
section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.CommonTransversal

theorem exists_skew_isUnit_det {F : Type} [Field F] (σ : F →+* F) {β : Type} [Fintype β]
    [DecidableEq β] (a b : Matrix β β F) (hσ : ∀ z, σ (σ z) = z) (hz : ∃ z, σ z ≠ z)
    (h : a * (b.map σ)ᵀ + b * (a.map σ)ᵀ = 0)
    (hv : ∀ v : β → F, Matrix.vecMul v a = 0 → Matrix.vecMul v b = 0 → v = 0) :
    ∃ s : Matrix β β F, (s.map σ)ᵀ = -s ∧ IsUnit (a + b * s).det := by
  classical
  obtain ⟨L, L', D, hD⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec a
  obtain ⟨P, hP⟩ : ∃ P, P = (L.map Matrix.TransvectionStruct.toMatrix).prod := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (L'.map Matrix.TransvectionStruct.toMatrix).prod := ⟨_, rfl⟩
  rw [← hP, ← hQ] at hD
  have hP1 : P.det = 1 := by rw [hP]; exact Matrix.TransvectionStruct.det_toMatrix_prod L
  have hQ1 : Q.det = 1 := by rw [hQ]; exact Matrix.TransvectionStruct.det_toMatrix_prod L'
  have hst1 : ∀ M : Matrix β β F, M.det = 1 → ((M.map σ)ᵀ).det = 1 := by
    intro M hM
    rw [Matrix.det_transpose]
    have e : (M.map σ).det = σ M.det := (RingHom.map_det σ M).symm
    rw [e, hM, map_one]
  have cancel : ∀ (M : Matrix β β F) (x : β → F), M.det = 1 → x ᵥ* M = 0 → x = 0 := by
    intro M x hM hx
    have hu : IsUnit M.det := by rw [hM]; exact isUnit_one
    calc x = x ᵥ* (M * M⁻¹) := by rw [Matrix.mul_nonsing_inv (A := M) hu, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, hx, Matrix.zero_vecMul]
  obtain ⟨z, hz⟩ := hz
  obtain ⟨c, hcdef⟩ : ∃ c, c = z - σ z := ⟨_, rfl⟩
  have hc : c ≠ 0 := by rw [hcdef]; exact sub_ne_zero.2 (Ne.symm hz)
  have hσc : σ c = -c := by rw [hcdef, map_sub, hσ]; ring
  obtain ⟨s0, hs0⟩ : ∃ s0 : Matrix β β F, s0 = diagonal (fun i => if D i = 0 then c else 0) :=
    ⟨_, rfl⟩
  have hss : (s0.map σ)ᵀ = -s0 := by
    rw [hs0, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.diagonal_neg]
    congr 1
    funext i
    split_ifs <;> simp [hσc]
  have hQQ : ((((Q.map σ)ᵀ).map σ)ᵀ) = Q := by
    ext i j
    simp [hσ]
  have hsta : (a.map σ)ᵀ = (Q.map σ)ᵀ * diagonal (fun i => σ (D i)) * (P.map σ)ᵀ := by
    rw [hD, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.mul_assoc]
  refine ⟨(Q.map σ)ᵀ * s0 * Q, ?_, ?_⟩
  · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, hss, hQQ,
      Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc]
  · rw [isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨v, hv0, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    apply hv0
    have e1 : a + b * ((Q.map σ)ᵀ * s0 * Q) = (P * diagonal D + b * (Q.map σ)ᵀ * s0) * Q := by
      rw [hD]
      simp only [Matrix.add_mul, Matrix.mul_assoc]
    have h0 : v ᵥ* (P * diagonal D + b * (Q.map σ)ᵀ * s0) = 0 :=
      cancel Q _ hQ1 (by rw [Matrix.vecMul_vecMul, ← e1]; exact hvM)
    have h0' : (v ᵥ* P) ᵥ* diagonal D + ((v ᵥ* b) ᵥ* (Q.map σ)ᵀ) ᵥ* s0 = 0 := by
      simpa only [Matrix.vecMul_vecMul, Matrix.vecMul_add] using h0
    have hE : ∀ j, (v ᵥ* P) j * D j +
        ((v ᵥ* b) ᵥ* (Q.map σ)ᵀ) j * (if D j = 0 then c else 0) = 0 := by
      intro j
      have e := congr_fun h0' j
      rw [Pi.add_apply, Matrix.vecMul_diagonal, hs0, Matrix.vecMul_diagonal] at e
      exact e
    have hwD : (v ᵥ* P) ᵥ* diagonal D = 0 := by
      funext j
      rw [Matrix.vecMul_diagonal, Pi.zero_apply]
      by_cases hDj : D j = 0
      · rw [hDj, mul_zero]
      · have e := hE j
        rw [if_neg hDj, mul_zero, add_zero] at e
        rw [(mul_eq_zero.1 e).resolve_right hDj, zero_mul]
    have hva : v ᵥ* a = 0 := by
      rw [hD, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hwD, Matrix.zero_vecMul]
    have hc1 : v ᵥ* (a * (b.map σ)ᵀ + b * (a.map σ)ᵀ) = 0 := by rw [h, Matrix.vecMul_zero]
    rw [Matrix.vecMul_add, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hva, Matrix.zero_vecMul,
      zero_add, hsta, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul] at hc1
    have hud : ((v ᵥ* b) ᵥ* (Q.map σ)ᵀ) ᵥ* diagonal (fun i => σ (D i)) = 0 :=
      cancel _ _ (hst1 P hP1) hc1
    have hu : (v ᵥ* b) ᵥ* (Q.map σ)ᵀ = 0 := by
      funext j
      rw [Pi.zero_apply]
      by_cases hDj : D j = 0
      · have e := hE j
        rw [if_pos hDj, hDj, mul_zero, zero_add] at e
        exact (mul_eq_zero.1 e).resolve_right hc
      · have e := congr_fun hud j
        rw [Matrix.vecMul_diagonal, Pi.zero_apply] at e
        exact (mul_eq_zero.1 e).resolve_right ((map_ne_zero σ).2 hDj)
    exact hv v hva (cancel _ _ (hst1 Q hQ1) hu)

end GlobalTheory.CompanionTheory.CommonTransversal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.GoodCharIsLocallyConstant
section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.SchrLaw

theorem goodChar_isLocallyConstant {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ} (h : GoodChar ψ O u) : IsLocallyConstant (ψ : R → ℂ) := by
  have hone : ∀ z : R, ((u⁻¹ : Rˣ) : R) * z ∈ O → ψ z = 1 := by
    intro z hz
    have hu : ∀ y ∈ O, ψ ((u : R) * y) = 1 :=
      (h.ann (u : R)).2 (by rw [Units.inv_mul]; exact O.one_mem)
    have := hu _ hz
    rwa [Units.mul_inv_cancel_left] at this
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨{y | ((u⁻¹ : Rˣ) : R) * (y - x) ∈ O}, ?_, ?_, ?_⟩
  · exact h.isOpen.preimage (continuous_const.mul (continuous_id.sub continuous_const))
  · simp only [Set.mem_ofPred_eq, sub_self, mul_zero]
    exact O.zero_mem
  · intro y hy
    have hy' : y = x + (y - x) := by abel
    rw [hy', AddChar.map_add_eq_mul, hone _ hy, mul_one]

theorem schr_law : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (μ : @Measure (κ → R) (borel _)) (w w' : W) (φ φ' : (κ → R) → ℂ), GoodChar ψ O u → @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → d.rho ψ w (d.rho ψ w' φ) = ψ (⅟(2 : R) * B w w') • d.rho ψ (w + w') φ ∧ d.rho ψ 0 φ = φ ∧ (φ ∈ SB (κ → R) → d.rho ψ w φ ∈ SB (κ → R)) ∧ pair μ (d.rho ψ w φ) (d.rho ψ w φ') = pair μ φ φ' := by
  intro R _ _ _ _ _ _ ψ O u W _ _ B κ _ d μ w w' φ φ' hψ hμ
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self _
  have hloc : IsLocallyConstant (ψ : R → ℂ) := goodChar_isLocallyConstant hψ
  have hdot : ∀ b : κ → R, Continuous fun x : κ → R => x ⬝ᵥ b := fun b =>
    continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext x
    simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, map_add (f := _), Prod.fst_add, Prod.snd_add, d.form]
    rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x]
    congr 2
    simp only [add_dotProduct, dotProduct_add]
    linear_combination (-((d.e w).1 ⬝ᵥ (d.e w').2)) * h2
  · funext x
    simp [Darboux.rho, schr]
  · intro hφ
    change IsLocallyConstant _ ∧ HasCompactSupport _ at hφ
    change IsLocallyConstant _ ∧ HasCompactSupport _
    refine ⟨?_, ?_⟩
    · exact (hloc.comp_continuous ((hdot _).add continuous_const)).mul
        (hφ.1.comp_continuous (continuous_id.add continuous_const))
    · exact (hφ.2.comp_homeomorph (Homeomorph.addRight (d.e w).1)).mul_left
  · let _ : MeasurableSpace (κ → R) := borel _
    have : BorelSpace (κ → R) := ⟨rfl⟩
    have : μ.IsAddHaarMeasure := hμ
    have hpt : ∀ x, (starRingEnd ℂ) (d.rho ψ w φ x) * d.rho ψ w φ' x =
        (starRingEnd ℂ) (φ ((d.e w).1 + x)) * φ' ((d.e w).1 + x) := by
      intro x
      simp only [Darboux.rho, schr, map_mul]
      have hn : (starRingEnd ℂ) (ψ (x ⬝ᵥ (d.e w).2 + ⅟(2 : R) * ((d.e w).1 ⬝ᵥ (d.e w).2))) *
          ψ (x ⬝ᵥ (d.e w).2 + ⅟(2 : R) * ((d.e w).1 ⬝ᵥ (d.e w).2)) = 1 := by
        rw [Complex.conj_mul', hψ.norm_one]
        simp
      rw [add_comm (d.e w).1 x]
      linear_combination ((starRingEnd ℂ) (φ (x + (d.e w).1)) * φ' (x + (d.e w).1)) * hn
    unfold pair
    simp_rw [hpt]
    exact integral_add_left_eq_self (fun x => (starRingEnd ℂ) (φ x) * φ' x) (d.e w).1

end GlobalTheory.CompanionTheory.SchrLaw
end

