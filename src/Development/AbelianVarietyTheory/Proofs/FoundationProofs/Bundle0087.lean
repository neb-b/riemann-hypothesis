module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0052
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormalizedIntertwinerCompOfAdjacentLattices
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem idx_congr_of_inf_eq {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    {A B C : Submodule R X} (h : A ⊓ C = B ⊓ C) : idx A C = idx B C := by
  unfold idx
  rw [← AddSubgroup.inf_relIndex_right A.toAddSubgroup, ← AddSubgroup.inf_relIndex_right B.toAddSubgroup]
  have : A.toAddSubgroup ⊓ C.toAddSubgroup = B.toAddSubgroup ⊓ C.toAddSubgroup := by
    ext x
    have := SetLike.ext_iff.1 h x
    simpa using this
  rw [this]

theorem normOp_comp_of_adj : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → Adj A B → idx A C ≠ 0 → ∀ v, Fixes W A v → normOp lam W B C (normOp lam W A B v) = normOp lam W A C v := by
  intro R X M _ _ _ _ _ σ w γ W h lam hl A B C hA hB hC hadj hAC v hv
  obtain ⟨x, hx, P, hP, hfin, hann, hle⟩ := id hadj
  obtain ⟨hAB, hBA, -, hsB, hsA⟩ := _root_.GlobalTheory.FinWeil.adjacent_selfDual_simple h A B hA hB x hx P hP hfin hann hle
  have hn : Nat.card (R ⧸ P) ≠ 0 := Nat.card_pos.ne'
  have hAB0 : idx A B ≠ 0 := hAB ▸ hn
  have hBA0 : idx B A ≠ 0 := hBA ▸ hn
  have hBC0 : idx B C ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hBA0 hAC
  have hsq : lam (idx A B) ^ 2 = (idx A B : ℂ) := by
    rw [hAB]; exact (hl.2 P hP hfin).1
  have lAB := hl.1 _ hAB0
  have lBC := hl.1 _ hBC0
  have lAC := hl.1 _ hAC
  have homBC := ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h B C hC).2.1 hBC0).2.2
  have homAC := ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h A C hC).2.1 hAC).2.2
  have fixB := ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h A B hB).2.1 hAB0).2.1 v hv
  unfold normOp
  rw [homBC, smul_smul]
  by_cases h1 : B ⊓ C ≤ A
  · by_cases h2 : A ⊓ C ≤ B
    · have he : A ⊓ C = B ⊓ C :=
        le_antisymm (le_inf h2 inf_le_right) (le_inf h1 inf_le_right)
      rw [_root_.GlobalTheory.FinWeil.sumOp_comp_of_adj_of_inf_eq h lam hl A B C hA hB hC hadj hAC he v hv, smul_smul, ← idx_congr_of_inf_eq he]
      congr 1
      field_simp
    · have hT : A ⊓ B ⊔ A ⊓ C = A := by
        rcases hsA (A ⊓ B ⊔ A ⊓ C) le_sup_left (sup_le inf_le_left inf_le_left) with h3 | h3
        · exact absurd (le_sup_right.trans h3) h2
        · exact h3
      obtain ⟨hi, hs⟩ := _root_.GlobalTheory.FinWeil.sumOp_comp_of_between h B A C hB hA hC hBA0 hAC hT.ge
      rw [← hs _ fixB, (_root_.GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul h A B hA hB hAB0).2 v hv, homAC, smul_smul, hi,
        hBA.trans hAB.symm, map_mul, ← hsq]
      congr 1
      field_simp
  · have hT : A ⊓ B ⊔ B ⊓ C = B := by
      rcases hsB (A ⊓ B ⊔ B ⊓ C) le_sup_left (sup_le inf_le_right inf_le_left) with h3 | h3
      · exact absurd (le_sup_right.trans h3) h1
      · exact h3
    obtain ⟨hi, hs⟩ := _root_.GlobalTheory.FinWeil.sumOp_comp_of_between h A B C hA hB hC hAB0 hBC0 (by rw [inf_comm B A]; exact hT.ge)
    rw [hs v hv, hi, map_mul]
    congr 1
    field_simp

end GlobalTheory.FinWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneSubPrimeDivZetaSubOneMulIsUnit
section
open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.K5

theorem one_sub_p_div_zeta_mul_isUnit : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (j : ℕ), 1 ≤ j → ∀ y : Ω, IsInt (p := p) y →
  1 - (p : Ω) / (T.ζ j - 1) * y ≠ 0 ∧ IsInt (p := p) (1 - (p : Ω) / (T.ζ j - 1) * y)⁻¹ := by
  intro p hp hp2 Ω _ _ _ T j hj y hy
  classical
  set A := integralClosure (O0 p) Ω
  have hpj : 1 < p ^ j := Nat.one_lt_pow (by omega) hp.out.one_lt
  have hζ1 : T.ζ j ≠ 1 := (T.prim j).ne_one hpj
  have hτ0 : T.ζ j - 1 ≠ 0 := sub_ne_zero.2 hζ1
  have hζint : IsIntegral (O0 p) (T.ζ j) := by
    refine IsIntegral.of_pow (n := p ^ j) (by omega) ?_
    rw [(T.prim j).pow_eq_one]; exact isIntegral_one
  have htot : 2 ≤ Nat.totient (p ^ j) := by
    rw [Nat.totient_prime_pow hp.out (by omega)]
    have : 3 ≤ p := by have := hp.out.two_le; omega
    have h1 : 1 ≤ p ^ (j - 1) := Nat.one_le_pow _ _ hp.out.pos
    calc 2 = 1 * 2 := by ring
      _ ≤ p ^ (j - 1) * (p - 1) := Nat.mul_le_mul h1 (by omega)
  have hdiv : IsIntegral (O0 p) ((p : Ω) / (T.ζ j - 1) ^ 2) :=
    GlobalTheory.K5.PDiv.pdiv p Ω T j 2 hj htot
  have hw : IsIntegral (O0 p) ((p : Ω) / (T.ζ j - 1) ^ 2 * y) := hdiv.mul hy
  let ζ' : A := ⟨T.ζ j, hζint⟩
  let τ : A := ζ' - 1
  let w : A := ⟨_, hw⟩
  let u : A := 1 - τ * w
  have hu : (u : Ω) = 1 - (p : Ω) / (T.ζ j - 1) * y := by
    simp only [u, τ, w, ζ', Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_one]
    field_simp
  obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
  have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr

  have hτM : ∀ M : Ideal A, M.IsMaximal → τ ∈ M := by
    intro M hM
    have hc : (M.comap (algebraMap (O0 p) A)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal M
    have hpM : (p : A) ∈ M := by
      have h1 : M.comap (algebraMap (O0 p) A) = IsLocalRing.maximalIdeal (O0 p) :=
        IsLocalRing.eq_maximalIdeal hc
      have h2 : (p : O0 p) ∈ M.comap (algebraMap (O0 p) A) := by
        rw [h1, hmax]; exact Ideal.mem_span_singleton_self _
      simpa using h2
    have : M.IsPrime := hM.isPrime
    have : Nontrivial (A ⧸ M) := Ideal.Quotient.nontrivial_iff.2 hM.ne_top
    have : CharP (A ⧸ M) p := by
      rw [CharP.charP_iff_prime_eq_zero hp.out]
      rw [← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq_zero_iff_mem]; exact hpM
    have hζp : ζ' ^ (p ^ j) = 1 := Subtype.ext (by simp [ζ', (T.prim j).pow_eq_one])
    have h3 : (Ideal.Quotient.mk M τ) ^ (p ^ j) = 0 := by
      let q := Ideal.Quotient.mk M
      change (q (ζ' - 1)) ^ (p ^ j) = 0
      rw [q.map_sub, q.map_one, sub_pow_char_pow (p := p) (q ζ') 1 j,
        ← q.map_pow, hζp, q.map_one, one_pow, sub_self]
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact pow_eq_zero_iff (by omega) |>.1 h3
  have hunit : IsUnit u := by
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {u})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    have h1 : u ∈ M := hle (Ideal.mem_span_singleton_self _)
    have h2 : τ * w ∈ M := M.mul_mem_right _ (hτM M hM)
    have : (1 : A) ∈ M := by
      have := M.add_mem h1 h2; simpa [u] using this
    exact hM.ne_top ((Ideal.eq_top_iff_one _).2 this)
  obtain ⟨v, hv⟩ := hunit
  have hval : (u : Ω) * (((v⁻¹ : Aˣ) : A) : Ω) = 1 := by
    rw [← hv, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
  rw [← hu]
  refine ⟨left_ne_zero_of_mul_eq_one hval, ?_⟩
  rw [← eq_inv_of_mul_eq_one_right hval]
  exact ((v⁻¹ : Aˣ) : A).2

end GlobalTheory.K5
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrderedCharacterFamilySplitsOrConstantOnUnits
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem apply_eq_one_of_triv_one_unit {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {χ : kˣ →* ℂˣ} (h : Triv χ 1) (u : kˣ) (hu : valuation k (u : k) = 1) : χ u = 1 := by
  apply h u hu
  calc valuation k ((u : k) - 1) ≤ max (valuation k (u : k)) (valuation k 1) := Valuation.map_sub _ _ _
    _ = valuation k 1 := by simp [hu]

theorem cut_or_const : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → (∃ r : ℕ, 0 < r ∧ r < n ∧ Cut ψ r) ∨ ∃ χ : kˣ →* ℂˣ, ((∀ i, IsSmoothChar (ψ i)) → IsSmoothChar χ) ∧ Agree ψ (fun _ => χ) := by
  intro k _ _ _ _ n ψ hord
  by_cases hc : ∃ m : ℕ, ∃ h : m + 1 < n, ¬ Triv (ψ ⟨m, by omega⟩ / ψ ⟨m + 1, h⟩) 1
  · obtain ⟨m, hm, hnt⟩ := hc
    refine Or.inl ⟨m + 1, by omega, hm, ?_⟩
    intro i j hi hj htr
    have h1 : i ≤ (⟨m, by omega⟩ : Fin n) := by rw [Fin.le_def]; simp; omega
    have h2 : (⟨m, by omega⟩ : Fin n) ≤ ⟨m + 1, hm⟩ := by rw [Fin.le_def]; simp
    have h3 : (⟨m + 1, hm⟩ : Fin n) ≤ j := by rw [Fin.le_def]; simp; omega
    exact hnt (hord i _ _ j h1 h2 h3 1 htr)
  · push_neg at hc
    right
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine ⟨1, fun _ => ?_, fun i => i.elim0⟩
      show IsOpen ((1 : kˣ →* ℂˣ).ker : Set kˣ)
      simp
    · refine ⟨ψ ⟨0, hn⟩, fun hs => hs _, ?_⟩
      have key : ∀ m (hm : m < n) (u : kˣ), valuation k (u : k) = 1 → ψ ⟨m, hm⟩ u = ψ ⟨0, hn⟩ u := by
        intro m
        induction m with
        | zero => intro _ _ _; rfl
        | succ m ih =>
          intro hm u hu
          have h1 := apply_eq_one_of_triv_one_unit (hc m hm) u hu
          rw [MonoidHom.div_apply, div_eq_one] at h1
          rw [← h1, ih (by omega) u hu]
      intro i u hu
      exact key i.1 i.2 u hu

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeriodMapEquivariant
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.HeckeEqv

theorem toGL_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    toGL (A * B) = toGL A * toGL B := by
  have hAB : (A * B).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hA hB
  ext i j
  simp [toGL, hA, hB, hAB, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem toGL_mat (γ : SL(2, ℤ)) : toGL (mat γ) = Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  have h : (mat γ).det ≠ 0 := by simp [mat]
  ext i j
  simp [toGL, h, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.SpecialLinearGroup.mapGL]

theorem toGL_smul_mat (γ : SL(2, ℤ)) (τ : ℍ) : toGL (mat γ) • τ = γ • τ := by
  rw [toGL_mat]; rfl

theorem mem_of_natDegree_le {w : ℕ} {p : ℂ[X]} (h : p.natDegree ≤ w) : p ∈ degreeLT ℂ (w + 1) := by
  rw [mem_degreeLT]
  exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le h)

theorem eichler_mem (w : ℕ) (f : ℍ → ℂ) (τ : ℍ) : eichler w f τ ∈ degreeLT ℂ (w + 1) := by
  refine Submodule.sum_mem _ fun j hj => mem_of_natDegree_le ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))

theorem polySlash_mem (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) : slP w g p ∈ degreeLT ℂ (w + 1) := by
  simp only [slP, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
  refine Submodule.sum_mem _ fun i hi => ?_
  refine Submodule.smul_mem _ _ (mem_of_natDegree_le ?_)
  have hi' : i ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  refine natDegree_mul_le.trans ?_
  have h1 := (natDegree_pow_le (p := C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) (n := i)).trans
    (Nat.mul_le_mul_left i (natDegree_linear_le))
  have h2 := (natDegree_pow_le (p := C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) (n := w - i)).trans
    (Nat.mul_le_mul_left (w - i) (natDegree_linear_le))
  omega

theorem hecke_eqv (Γ : Subgroup SL(2, ℤ)) (k : ℕ) (hk2 : 2 ≤ k) (f : ModularForm Γ (k : ℤ))
    {ι : Type} [Fintype ι] (δ : ι → Matrix (Fin 2) (Fin 2) ℤ) (hδ : ∀ i, 0 < (δ i).det)
    (hπ : ∀ γ : Γ, ∃ π : Equiv.Perm ι, ∀ i, ∃ γ' : Γ, δ i * mat γ = mat γ' * δ (π i)) :
    per Γ (k - 2) (hkF (k : ℤ) δ ⇑f) - hk Γ (k - 2) δ (per Γ (k - 2) ⇑f) ∈ B1 Γ (k - 2) := by
  have hfd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ⇑f := f.holo'
  have hdet : ∀ i, (δ i).det ≠ 0 := fun i => (hδ i).ne'
  have hpc := (_root_.GlobalTheory.HeckeFamilyMatrices.PerCoc.per_mem_Z1_and_eq_slP_eichler_sub Γ k hk2 f).2
  set w := k - 2 with hw
  set F := eichler w ⇑f with hF
  set c : ι → ℂ[X] := fun i => slP w (δ i) (F (toGL (δ i) • UpperHalfPlane.I)) with hc
  set C := ∑ i, c i with hCdef
  have hC : -C ∈ degreeLT ℂ (w + 1) :=
    Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => polySlash_mem _ _ _)
  refine ⟨⟨-C, hC⟩, ?_⟩
  funext γ
  have hγdet : (mat (γ : SL(2, ℤ))).det ≠ 0 := by simp [mat]
  obtain ⟨hex⟩ : Nonempty (∃ π : Equiv.Perm ι, ∀ i, ∃ γ' : Γ, δ i * mat γ = mat γ' * δ (π i)) := ⟨hπ γ⟩
  have e2 : hk Γ w δ (per Γ w ⇑f) γ =
      ∑ i, slP w (δ (hex.choose i)) (per Γ w ⇑f (hex.choose_spec i).choose) := by
    simp only [hk, LinearMap.pi_apply, dif_pos hex, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply]
  have e1 : per Γ w (hkF (k : ℤ) δ ⇑f) γ =
      ∑ i, (slP w (δ i * mat γ) (F (toGL (δ i * mat γ) • UpperHalfPlane.I)) - slP w (mat γ) (c i)) := by
    simp only [per, hkF]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [GlobalTheory.T.eichlerIntegralFromI_finset_sum w _ (fun i => hfd.slash _ _), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := _root_.GlobalTheory.EichlerChangeGL.polySlash_eichler_toGL_smul k hk2 ⇑f hfd (δ i) (hδ i) ((γ : SL(2, ℤ)) • UpperHalfPlane.I)
    rw [eq_sub_of_add_eq h.symm, map_sub, _root_.GlobalTheory.HeckeFamilyMatrices.SlashAction.polySlash_matrix_mul w (δ i) (mat γ) _ (eichler_mem _ _ _),
      toGL_mul _ _ (hdet i) hγdet, mul_smul, toGL_smul_mat]
  have e3 : ∀ i, slP w (δ i * mat γ) (F (toGL (δ i * mat γ) • UpperHalfPlane.I)) =
      slP w (δ (hex.choose i)) (per Γ w ⇑f (hex.choose_spec i).choose) + c (hex.choose i) := by
    intro i
    set γ' := (hex.choose_spec i).choose
    have hγ' : δ i * mat γ = mat γ' * δ (hex.choose i) := (hex.choose_spec i).choose_spec
    have hγ'det : (mat (γ' : SL(2, ℤ))).det ≠ 0 := by simp [mat]
    rw [hγ', toGL_mul _ _ hγ'det (hdet _), mul_smul, toGL_smul_mat,
      _root_.GlobalTheory.HeckeFamilyMatrices.SlashAction.polySlash_matrix_mul w (mat γ') (δ (hex.choose i)) _ (eichler_mem _ _ _),
      hpc γ' (toGL (δ (hex.choose i)) • UpperHalfPlane.I), map_sub]
    simp only [hc]
    abel
  have hsum : ∑ i, c (hex.choose i) = C := Equiv.sum_comp hex.choose c
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.pi_apply, LinearMap.sub_apply,
    LinearMap.id_apply, Pi.sub_apply]
  rw [e1, e2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e3, Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum, ← map_sum, map_neg]
  abel

theorem tqFam_det (q : ℕ) (hq : q.Prime) (σ : SL(2, ℤ)) (i : Fin (q + 1)) : 0 < (tqFam q σ i).det := by
  have hq0 : (0 : ℤ) < q := by exact_mod_cast hq.pos
  unfold tqFam
  split_ifs
  · simpa [Matrix.det_fin_two_of] using hq0
  · simpa [Matrix.det_mul, mat, dg, Matrix.det_fin_two_of] using hq0

theorem ulFam_det (l : ℕ) (hl : l.Prime) (i : Fin l) : 0 < (ulFam l i).det := by
  have hl0 : (0 : ℤ) < l := by exact_mod_cast hl.pos
  simpa [ulFam, Matrix.det_fin_two_of] using hl0

theorem period_map_equivariant : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ f : ModularForm (Lev N l) (k : ℤ),
  (∀ (q : ℕ) (σ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → IsDiam N l (q : ZMod N) σ →
    per (Lev N l) (k - 2) (TqF (k : ℤ) q σ ⇑f) - TqZ (Lev N l) (k - 2) q σ (per (Lev N l) (k - 2) ⇑f) ∈ B1 (Lev N l) (k - 2)) ∧
  per (Lev N l) (k - 2) (UlF (k : ℤ) l ⇑f) - UlZ (Lev N l) (k - 2) l (per (Lev N l) (k - 2) ⇑f) ∈ B1 (Lev N l) (k - 2) ∧
  (∀ (d : ZMod N) (σ : SL(2, ℤ)), IsDiam N l d σ →
    per (Lev N l) (k - 2) (DdF (k : ℤ) σ ⇑f) - DdZ (Lev N l) (k - 2) σ (per (Lev N l) (k - 2) ⇑f) ∈ B1 (Lev N l) (k - 2)) := by
  intro N l k hN hl hlN hk f
  refine ⟨fun q σ hq hqN hσ => ?_, ?_, fun d σ hσ => ?_⟩
  · exact hecke_eqv _ k (by omega) f (tqFam q σ) (tqFam_det q hq σ)
      (_root_.GlobalTheory.TqPerm.tqFam_perm N l q hN hl hlN hq hqN σ hσ)
  · exact hecke_eqv _ k (by omega) f (ulFam l) (ulFam_det l hl) (_root_.GlobalTheory.HeckeFamilyMatrices.ulFam_perm N l hN hl hlN)
  · exact hecke_eqv _ k (by omega) f (fun _ : Unit => mat σ) (fun _ => by simp [mat])
      (fun γ => ⟨Equiv.refl _, fun _ => _root_.GlobalTheory.HeckeFamilyMatrices.diam_normalises_lev N l d σ hσ γ⟩)

end GlobalTheory.HeckeFamilyMatrices.HeckeEqv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterRankOnePerturbation
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem det_leadingBlock_one_add_vecMulVec_rankOne {k : Type} [Field k] {n : ℕ} (p q : Fin n → k) (a : Fin n) (c : k)
    (hpq : ∀ i, p i * q i = if i = a then c else 0) (m : Fin n) :
    ((1 + Matrix.vecMulVec p q).toSquareBlockProp fun i => i ≤ m).det = if a ≤ m then 1 + c else 1 := by
  have hM : ((1 + Matrix.vecMulVec p q).toSquareBlockProp fun i => i ≤ m) =
      1 + Matrix.replicateCol Unit (fun i : {i // i ≤ m} => p i) * Matrix.replicateRow Unit (fun i : {i // i ≤ m} => q i) := by
    ext i j
    simp [Matrix.toSquareBlockProp_def, Matrix.one_apply, Subtype.ext_iff, Matrix.vecMulVec_apply, Matrix.mul_apply]
  rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hs : (fun i : {i // i ≤ m} => q i) ⬝ᵥ (fun i : {i // i ≤ m} => p i) = ∑ i : {i // i ≤ m}, (if (i : Fin n) = a then c else 0) := by
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, hpq]
  rw [hs]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro e; exact hb (Subtype.ext e)
    · simp
  · rw [Finset.sum_eq_zero]
    · simp
    · intro b _
      rw [if_neg]
      intro e; exact h (e ▸ b.2)

theorem rankOne_ev_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ) :
    ev χ (1 : k) = 1 := by
  unfold ev
  rw [dif_pos (by simp)]
  have : Units.mk0 (1 : k) one_ne_zero = 1 := by ext; simp
  simp [this]

theorem rankOne_ev_unit {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ)
    (u : kˣ) (hu : valuation k (u : k) = 1) : ev χ (u : k) = (χ u : ℂ) := by
  unfold ev
  rw [dif_pos hu]
  simp

theorem rankOne_telescope {G : Type} [CommGroup G] (n : ℕ) (F : ℕ → G) (hF : F n = 1) (a : ℕ) (ha : a < n) :
    ∏ i ∈ Finset.range n, (if a ≤ i then F i / F (i + 1) else 1) = F a := by
  rw [← Finset.prod_filter]
  have hfil : (Finset.range n).filter (fun i => a ≤ i) = Finset.Ico a n := by
    ext i; simp [Finset.mem_Ico, and_comm]
  rw [hfil]
  have h2 : ∀ i, F i / F (i + 1) = (F (i + 1))⁻¹ / (F i)⁻¹ := fun i => by
    rw [div_eq_mul_inv, div_eq_mul_inv, inv_inv, mul_comm]
  simp_rw [h2]
  rw [Finset.prod_Ico_div (f := fun i => (F i)⁻¹) ha.le, hF]
  simp

theorem theta_rankOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (g : GL (Fin n) k) (p q : Fin n → k) (a : Fin n) (u : kˣ), valuation k (u : k) = 1 → g.val = 1 + Matrix.vecMulVec p q → (∀ i, p i * q i = if i = a then (u : k) - 1 else 0) → theta ψ g = (ψ a u : ℂ) := by
  intro k _ _ _ _ n ψ g p q a u hu hg hpq
  have hmin : ∀ m, minor g m = if a ≤ m then (u : k) else 1 := by
    intro m
    unfold minor
    rw [hg, det_leadingBlock_one_add_vecMulVec_rankOne p q a _ hpq m]
    simp
  let F : ℕ → ℂˣ := fun j => if h : j < n then ψ ⟨j, h⟩ u else 1
  have hterm : ∀ m : Fin n, ev (ψ m / nxt ψ m) (minor g m) = ((if a ≤ m then F m / F (m + 1) else 1 : ℂˣ) : ℂ) := by
    intro m
    rw [hmin]
    split_ifs with h
    · rw [rankOne_ev_unit _ _ hu]
      congr 1
      simp only [F, MonoidHom.div_apply, dif_pos m.2]
      congr 1
      unfold nxt
      split_ifs <;> rfl
    · rw [rankOne_ev_one]; simp
  unfold theta
  simp_rw [hterm, Fin.le_iff_val_le_val]
  rw [← Units.coe_prod, Fin.prod_univ_eq_prod_range (fun i => if (a : ℕ) ≤ i then F i / F (i + 1) else 1) n]
  · rw [rankOne_telescope n F (by simp [F]) a a.2]
    simp [F]

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeConstantFamilyDetCharacter
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

noncomputable section
namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem valuation_det_of_mem_KO' {n : Type} [Fintype n] [DecidableEq n] {g : GL n k} (hg : g ∈ KO k n) :
    valuation k g.val.det = 1 := by
  obtain ⟨h, rfl⟩ := hg
  have hu : IsUnit (h.val.det) := (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
  have := (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.1 hu
  change valuation k ((algebraMap 𝒪[k] k).mapMatrix h.val).det = 1
  rw [← RingHom.map_det]
  exact this

private theorem ev_one' (x : k) : ev (1 : kˣ →* ℂˣ) x = 1 := by
  unfold ev; split_ifs <;> simp

private theorem minor_last {n : ℕ} (g : GL (Fin (n + 1)) k) : minor g (Fin.last n) = g.val.det := by
  unfold minor Matrix.toSquareBlockProp Matrix.toBlock
  have := Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (p := fun i : Fin (n + 1) => i ≤ Fin.last n)
    (fun i => Fin.le_last i)) g.val
  rw [← this]; rfl

theorem const_family (n : ℕ) (χ : kˣ →* ℂˣ) :
    grp (fun _ : Fin n => χ) = (KO k (Fin n) : Set (GL (Fin n) k)) ∧
      ∀ g ∈ KO k (Fin n), theta (fun _ : Fin n => χ) g = (detChar (Fin n) χ g : ℂ) := by
  refine ⟨?_, ?_⟩
  · ext g
    simp only [grp, Set.mem_setOf_eq, SetLike.mem_coe, div_self', and_iff_left_iff_imp]
    intro _ i j _ u _ _
    rfl
  · intro g hg
    cases n with
    | zero =>
      simp [theta, detChar_apply]
      have h0 : Matrix.GeneralLinearGroup.det g = 1 := Units.ext (by simp [Matrix.det_isEmpty])
      rw [h0, map_one, Units.val_one]
    | succ n =>
      unfold theta
      rw [Fin.prod_univ_castSucc]
      have h1 : ∀ i : Fin n, ev (χ / nxt (fun _ : Fin (n+1) => χ) i.castSucc) (minor g i.castSucc) = 1 := by
        intro i
        have : nxt (fun _ : Fin (n+1) => χ) i.castSucc = χ := by
          unfold nxt; rw [dite_eq_left (by simp)]
        rw [this, div_self']; exact ev_one' _
      have h2 : nxt (fun _ : Fin (n+1) => χ) (Fin.last n) = 1 := by
        unfold nxt; rw [dite_eq_right (by simp)]
      simp only [h1, Finset.prod_const_one, one_mul, h2, div_one, minor_last]
      have hv := valuation_det_of_mem_KO' hg
      unfold ev
      rw [dite_eq_left hv, detChar_apply]
      congr 2
      ext; simp

theorem const_family_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (χ : kˣ →* ℂˣ), grp (fun _ : Fin n => χ) = (KO k (Fin n) : Set (GL (Fin n) k)) ∧ ∀ g ∈ KO k (Fin n), theta (fun _ : Fin n => χ) g = (detChar (Fin n) χ g : ℂ) :=
  fun _ _ _ _ _ n χ => const_family n χ

end GlobalTheory.PsType
end
end

