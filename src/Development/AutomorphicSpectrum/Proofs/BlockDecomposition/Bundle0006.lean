module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdaptedMajorant
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.WittMajorant

variable {n : ℕ}

private theorem conj_mul (U V D E : Matrix (Fin n) (Fin n) ℂ) (h : V * U = 1) :
    (U * D * V) * (U * E * V) = U * (D * E) * V := by
  calc (U * D * V) * (U * E * V) = U * D * (V * U) * E * V := by
        simp only [Matrix.mul_assoc]
    _ = U * (D * E) * V := by
        rw [h]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem exists_abs_sign {R : Matrix (Fin n) (Fin n) ℂ} (hR : R.IsHermitian) :
    ∃ A S : Matrix (Fin n) (Fin n) ℂ,
      A.PosSemidef ∧ A = S * R ∧ A = R * S ∧ S * S * R = R := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hR.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUU : Uᴴ * U = 1 := by
    have := Unitary.star_mul_self_of_mem hR.eigenvectorUnitary.2
    simpa [star_eq_conjTranspose] using this
  have hspec : R = U * diagonal (fun i => ((hR.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have := hR.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, Function.comp_def] using this
  set d : Fin n → ℂ := fun i => ((hR.eigenvalues i : ℝ) : ℂ) with hd
  set a : Fin n → ℂ := fun i => ((|hR.eigenvalues i| : ℝ) : ℂ) with ha
  set s : Fin n → ℂ := fun i => (((SignType.sign (hR.eigenvalues i) : SignType) : ℝ) : ℂ) with hs
  have hsd : ∀ i, s i * d i = a i := by
    intro i
    simp only [hs, hd, ha]
    rw [← Complex.ofReal_mul, sign_mul_self]
  have hds : ∀ i, d i * s i = a i := fun i => by rw [mul_comm, hsd]
  have hssd : ∀ i, s i * s i * d i = d i := by
    intro i
    simp only [hs, hd]
    rcases lt_trichotomy (hR.eigenvalues i) 0 with h | h | h
    · simp [sign_neg h]
    · simp [h]
    · simp [sign_pos h]
  refine ⟨U * diagonal a * Uᴴ, U * diagonal s * Uᴴ, ?_, ?_, ?_, ?_⟩
  · have h0 : (diagonal a).PosSemidef := by
      rw [posSemidef_diagonal_iff]
      intro i
      simp only [ha]
      exact_mod_cast abs_nonneg _
    have := h0.conjTranspose_mul_mul_same Uᴴ
    simpa using this
  · conv_rhs => rw [hspec]
    rw [conj_mul _ _ _ _ hUU, diagonal_mul_diagonal]
    simp only [hsd]
  · conv_rhs => rw [hspec]
    rw [conj_mul _ _ _ _ hUU, diagonal_mul_diagonal]
    simp only [hds]
  · conv_lhs => rw [hspec]
    rw [conj_mul _ _ _ _ hUU, conj_mul _ _ _ _ hUU, diagonal_mul_diagonal, diagonal_mul_diagonal]
    simp only [hssd]
    exact hspec.symm

theorem exists_adapted_majorant (n r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin r) ℂ) (hJ : J.IsHermitian) (hdet : IsUnit J.det)
    (hXX : Xᴴ * J * X = 0) (hYY : Yᴴ * J * Y = 0) (hXY : Xᴴ * J * Y = 1) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, P.PosDef ∧ P * J⁻¹ * P = J ∧ P * X = J * Y := by
  have hJi : J⁻¹ * J = 1 := nonsing_inv_mul J hdet
  have hJi' : J * J⁻¹ = 1 := mul_nonsing_inv J hdet
  have hYX : Yᴴ * J * X = 1 := by
    have := congrArg conjTranspose hXY
    simpa [conjTranspose_mul, hJ.eq, Matrix.mul_assoc] using this
  have xx : Xᴴ * (J * X) = 0 := by rw [← Matrix.mul_assoc]; exact hXX
  have yy : Yᴴ * (J * Y) = 0 := by rw [← Matrix.mul_assoc]; exact hYY
  have xy : Xᴴ * (J * Y) = 1 := by rw [← Matrix.mul_assoc]; exact hXY
  have yx : Yᴴ * (J * X) = 1 := by rw [← Matrix.mul_assoc]; exact hYX
  set R : Matrix (Fin n) (Fin n) ℂ := J⁻¹ - X * Yᴴ - Y * Xᴴ with hRdef
  have hRh : R.IsHermitian := by
    have hi : (J⁻¹)ᴴ = J⁻¹ := (IsHermitian.inv hJ).eq
    unfold IsHermitian
    rw [hRdef, conjTranspose_sub, conjTranspose_sub, hi, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, conjTranspose_conjTranspose]
    abel
  have hRX : R * (J * X) = 0 := by
    rw [hRdef, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, yx, xx,
      ← Matrix.mul_assoc J⁻¹, hJi]
    simp
  have hRY : R * (J * Y) = 0 := by
    rw [hRdef, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, yy, xy,
      ← Matrix.mul_assoc J⁻¹, hJi]
    simp
  have hRJR : R * (J * R) = R := by
    have e : J * R = 1 - (J * X) * Yᴴ - (J * Y) * Xᴴ := by
      rw [hRdef, Matrix.mul_sub, Matrix.mul_sub, hJi', Matrix.mul_assoc, Matrix.mul_assoc]
    have e1 : R * (J * X * Yᴴ) = (R * (J * X)) * Yᴴ := (Matrix.mul_assoc _ _ _).symm
    have e2 : R * (J * Y * Xᴴ) = (R * (J * Y)) * Xᴴ := (Matrix.mul_assoc _ _ _).symm
    rw [e, Matrix.mul_sub, Matrix.mul_sub, e1, e2, hRX, hRY]
    simp
  obtain ⟨A, S, hA, hAS, hAR, hSSR⟩ := exists_abs_sign hRh
  have hAh : Aᴴ = A := hA.isHermitian.eq
  have hAX : A * (J * X) = 0 := by
    rw [hAS, Matrix.mul_assoc, hRX, Matrix.mul_zero]
  have hAY : A * (J * Y) = 0 := by
    rw [hAS, Matrix.mul_assoc, hRY, Matrix.mul_zero]
  have hXA : Xᴴ * (J * A) = 0 := by
    have := congrArg conjTranspose hAX
    simpa [conjTranspose_mul, hJ.eq, hAh, Matrix.mul_assoc] using this
  have hYA : Yᴴ * (J * A) = 0 := by
    have := congrArg conjTranspose hAY
    simpa [conjTranspose_mul, hJ.eq, hAh, Matrix.mul_assoc] using this
  have hAJA : A * (J * A) = R := by
    calc A * (J * A) = (S * R) * (J * (R * S)) := by rw [← hAS, ← hAR]
      _ = S * (R * (J * R)) * S := by simp only [Matrix.mul_assoc]
      _ = S * (R * S) := by rw [hRJR, Matrix.mul_assoc]
      _ = S * (S * R) := by rw [← hAR, hAS]
      _ = R := by rw [← Matrix.mul_assoc, hSSR]
  set T : Matrix (Fin n) (Fin n) ℂ := X * Xᴴ + Y * Yᴴ + A with hTdef
  have hTX : T * (J * X) = Y := by
    rw [hTdef, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, xx, yx, hAX]
    simp
  have hTY : T * (J * Y) = X := by
    rw [hTdef, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, xy, yy, hAY]
    simp
  have hTA : T * (J * A) = R := by
    rw [hTdef, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, hXA, hYA,
      hAJA]
    simp
  have hTJT : T * (J * T) = J⁻¹ := by
    have e : J * T = (J * X) * Xᴴ + (J * Y) * Yᴴ + J * A := by
      rw [hTdef, Matrix.mul_add, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc]
    have e1 : T * (J * X * Xᴴ) = (T * (J * X)) * Xᴴ := (Matrix.mul_assoc _ _ _).symm
    have e2 : T * (J * Y * Yᴴ) = (T * (J * Y)) * Yᴴ := (Matrix.mul_assoc _ _ _).symm
    rw [e, Matrix.mul_add, Matrix.mul_add, e1, e2, hTX, hTY, hTA, hRdef]
    abel
  have hTpsd : T.PosSemidef :=
    ((posSemidef_self_mul_conjTranspose X).add (posSemidef_self_mul_conjTranspose Y)).add hA
  have hTunit : IsUnit T := by
    have h1 : T * (J * T * J) = 1 := by
      calc T * (J * T * J) = (T * (J * T)) * J := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hTJT, hJi]
    exact (Matrix.isUnit_iff_isUnit_det T).2 (Matrix.isUnit_det_of_right_inverse h1)
  have hTpd : T.PosDef := hTpsd.posDef_iff_isUnit.2 hTunit
  have hJinj : Function.Injective J.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det J).2 hdet)
  refine ⟨J * T * J, ?_, ?_, ?_⟩
  · have := hTpd.conjTranspose_mul_mul_same hJinj
    rwa [hJ.eq] at this
  · calc J * T * J * J⁻¹ * (J * T * J) = J * (T * (J * T)) * J := by
          have h2 : J * T * J * J⁻¹ = J * T := by
            rw [Matrix.mul_assoc (J * T), hJi', Matrix.mul_one]
          rw [h2]
          simp only [Matrix.mul_assoc]
      _ = J := by rw [hTJT, hJi', Matrix.one_mul]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, hTX]

end GlobalTheory.CompanionTheory.WittMajorant
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChainsOfRange
section
namespace GlobalTheory.CompanionTheory.JordanChain

open Module Submodule

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

def chainVec (f : V →ₗ[K] V) {ι : Type} (e : ι → ℕ) (v : ι → V) : (Σ a, Fin (e a)) → V :=
  fun p => (f ^ (p.2 : ℕ)) (v p.1)

theorem pow_coe_of_restrict {W : Submodule K V} (f : V →ₗ[K] V) (g : W →ₗ[K] W)
    (hg : ∀ x, (g x : V) = f x) (k : ℕ) (x : W) : (((g ^ k) x : W) : V) = (f ^ k) x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hg]

theorem exists_chains_of_range [FiniteDimensional K V] (f : V →ₗ[K] V)
    (g : LinearMap.range f →ₗ[K] LinearMap.range f) (hg : ∀ x, (g x : V) = f x)
    {ι' : Type} [Fintype ι'] (e' : ι' → ℕ) (he' : ∀ b, 0 < e' b) (w : ι' → LinearMap.range f)
    (h0 : ∀ b, (g ^ e' b) (w b) = 0) (hli : LinearIndependent K (chainVec g e' w))
    (hsp : span K (Set.range (chainVec g e' w)) = ⊤) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (v : ι → V), (∀ a, 0 < e a) ∧
      (∀ a, (f ^ e a) (v a) = 0) ∧ LinearIndependent K (chainVec f e v) ∧
      span K (Set.range (chainVec f e v)) = ⊤ := by
  classical
  have hu : ∀ b, ∃ u, f u = (w b : V) := fun b => (w b).2
  choose u hu using hu
  have hstep : ∀ (b : ι') (j : ℕ), (f ^ (j + 1)) (u b) = (f ^ j) (w b : V) := by
    intro b j
    rw [pow_succ, Module.End.mul_apply, hu]
  set N := LinearMap.ker f with hN
  let t : ι' → V := fun b => (f ^ e' b) (u b)
  have htN : ∀ b, t b ∈ N := by
    intro b
    have h1 : f (t b) = (f ^ (e' b + 1)) (u b) := by
      simp only [t]
      rw [pow_succ', Module.End.mul_apply]
    rw [hN, LinearMap.mem_ker, h1, hstep, ← pow_coe_of_restrict f g hg, h0]
    rfl
  have hLV : LinearIndependent K (fun p => ((chainVec g e' w p : LinearMap.range f) : V)) :=
    hli.map' (LinearMap.range f).subtype (Submodule.ker_subtype _)
  let idx : ι' → Σ b, Fin (e' b) := fun b => ⟨b, ⟨e' b - 1, by have := he' b; omega⟩⟩
  have hidx : Function.Injective idx := fun a b h => congrArg Sigma.fst h
  have ht : LinearIndependent K t := by
    have h2 := hLV.comp idx hidx
    convert h2 using 1
    funext b
    change (f ^ e' b) (u b) = ((g ^ (e' b - 1)) (w b) : LinearMap.range f)
    rw [pow_coe_of_restrict f g hg, ← hstep]
    congr 2
    have := he' b
    omega
  let tN : ι' → N := fun b => ⟨t b, htN b⟩
  have htNli : LinearIndependent K tN := LinearIndependent.of_comp N.subtype ht
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (span K (Set.range tN))
  let bC := Module.finBasis K C
  let z : Fin (finrank K C) → V := fun c => ((bC c : C) : N)
  have hz : ∀ c, f (z c) = 0 := fun c => ((bC c : C) : N).2
  let e : ι' ⊕ Fin (finrank K C) → ℕ := Sum.elim (fun b => e' b + 1) (fun _ => 1)
  let v : ι' ⊕ Fin (finrank K C) → V := Sum.elim u z
  let T := span K (Set.range (chainVec f e v))
  have hTu : ∀ (b : ι') (j : ℕ), j ≤ e' b → (f ^ j) (u b) ∈ T := by
    intro b j hj
    exact subset_span ⟨⟨Sum.inl b, ⟨j, Nat.lt_succ_of_le hj⟩⟩, rfl⟩
  have hTz : ∀ c, z c ∈ T := by
    intro c
    exact subset_span ⟨⟨Sum.inr c, ⟨0, Nat.one_pos⟩⟩, by simp [chainVec, v]⟩
  have hkerS : map N.subtype (span K (Set.range tN)) ≤ T := by
    refine (Submodule.map_span_le _ _ _).2 ?_
    rintro _ ⟨b, rfl⟩
    exact hTu b _ le_rfl
  have hkerC : map (N.subtype ∘ₗ C.subtype) ⊤ ≤ T := by
    rw [← bC.span_eq]
    refine (Submodule.map_span_le _ _ _).2 ?_
    rintro _ ⟨c, rfl⟩
    exact hTz c
  have hker : N ≤ T := by
    intro x hx
    have hx' : (⟨x, hx⟩ : N) ∈ span K (Set.range tN) ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨s, hs, c, hc, hsc⟩ := Submodule.mem_sup.1 hx'
    have hxe : x = (s : V) + (c : V) := by
      have := congrArg Subtype.val hsc
      simpa using this.symm
    rw [hxe]
    exact T.add_mem (hkerS ⟨s, hs, rfl⟩) (hkerC ⟨⟨c, hc⟩, trivial, rfl⟩)
  have hrange : ∀ y : LinearMap.range f, ∃ x ∈ T, f x = y := by
    have h3 : map (LinearMap.range f).subtype (span K (Set.range (chainVec g e' w))) ≤ map f T := by
      refine (Submodule.map_span_le _ _ _).2 ?_
      rintro _ ⟨⟨b, j⟩, rfl⟩
      refine ⟨(f ^ (j : ℕ)) (u b), hTu b _ j.2.le, ?_⟩
      simp only [chainVec, Submodule.subtype_apply]
      rw [pow_coe_of_restrict f g hg, ← hstep, pow_succ']
      rfl
    intro y
    have hy : (y : V) ∈ map (LinearMap.range f).subtype (span K (Set.range (chainVec g e' w))) := by
      rw [hsp]
      exact ⟨y, trivial, rfl⟩
    obtain ⟨x, hx, hxy⟩ := h3 hy
    exact ⟨x, hx, hxy⟩
  have hTtop : T = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨x', hx', hxx⟩ := hrange ⟨f x, x, rfl⟩
    have hk : x - x' ∈ N := by
      rw [hN, LinearMap.mem_ker, map_sub, hxx]
      simp
    have := T.add_mem (hker hk) hx'
    simpa using this
  have hcard₁ : finrank K (LinearMap.range f) = ∑ b, e' b := by
    have h4 := finrank_span_eq_card hli
    rw [hsp, finrank_top] at h4
    rw [h4, Fintype.card_sigma]
    simp
  have hcard₂ : finrank K N = Fintype.card ι' + finrank K C := by
    have h5 := Submodule.finrank_add_eq_of_isCompl hC
    rw [finrank_span_eq_card htNli] at h5
    exact h5.symm
  have hcard : Fintype.card (Σ a, Fin (e a)) = finrank K V := by
    have h6 := LinearMap.finrank_range_add_finrank_ker f
    rw [Fintype.card_sigma, ← h6, hcard₁, ← hN, hcard₂]
    simp [e, Fintype.sum_sum_type, Finset.sum_add_distrib]
    omega
  refine ⟨ι' ⊕ Fin (finrank K C), inferInstance, e, v, ?_, ?_, ?_, hTtop⟩
  · rintro (b | c)
    · exact Nat.succ_pos _
    · exact Nat.one_pos
  · rintro (b | c)
    · change (f ^ (e' b + 1)) (u b) = 0
      rw [hstep, ← pow_coe_of_restrict f g hg, h0]
      rfl
    · change (f ^ 1) (z c) = 0
      simpa using hz c
  · exact linearIndependent_of_top_le_span_of_card_eq_finrank hTtop.ge hcard

theorem exists_chains : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] V), finrank K V = n → IsNilpotent f →
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (v : ι → V), (∀ a, 0 < e a) ∧
      (∀ a, (f ^ e a) (v a) = 0) ∧ LinearIndependent K (chainVec f e v) ∧
      span K (Set.range (chainVec f e v)) = ⊤ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ f hn hf
    by_cases hV : Subsingleton V
    · refine ⟨Empty, inferInstance, fun _ => 0, fun _ => 0, fun a => a.elim, fun a => a.elim,
        ?_, Subsingleton.elim _ _⟩
      exact linearIndependent_empty_type
    · have hnt : Nontrivial V := not_subsingleton_iff_nontrivial.1 hV
      obtain ⟨m, hm⟩ := hf
      have hlt : finrank K (LinearMap.range f) < n := by
        rw [← hn]
        refine Submodule.finrank_lt ?_
        intro htop
        have hsurj : Function.Surjective f := LinearMap.range_eq_top.1 htop
        have hs : Function.Surjective (f ^ m) := by
          rw [Module.End.coe_pow]
          exact hsurj.iterate m
        rw [hm] at hs
        obtain ⟨x, hx⟩ := exists_ne (0 : V)
        obtain ⟨y, hy⟩ := hs x
        exact hx (by simpa using hy.symm)
      let g : LinearMap.range f →ₗ[K] LinearMap.range f :=
        f.restrict (fun x _ => LinearMap.mem_range_self f x)
      have hg : ∀ x, (g x : V) = f x := fun x => rfl
      have hgn : IsNilpotent g := by
        refine ⟨m, LinearMap.ext fun x => Subtype.ext ?_⟩
        rw [pow_coe_of_restrict f g hg, hm]
        rfl
      obtain ⟨ι', _, e', w, he', h0, hli, hsp⟩ := ih _ hlt (LinearMap.range f) g rfl hgn
      exact exists_chains_of_range f g hg e' he' w h0 hli hsp

theorem exists_chain_basis {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : V →ₗ[K] V) (hf : IsNilpotent f) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (v : ι → V), (∀ a, 0 < e a) ∧
      (∀ a, (f ^ e a) (v a) = 0) ∧
      LinearIndependent K (fun p : Σ a, Fin (e a) => (f ^ (p.2 : ℕ)) (v p.1)) ∧
      span K (Set.range (fun p : Σ a, Fin (e a) => (f ^ (p.2 : ℕ)) (v p.1))) = ⊤ :=
  exists_chains _ V f rfl hf

end GlobalTheory.CompanionTheory.JordanChain
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactOpenSubgroupMem
section
open Matrix ValuativeRel

namespace GlobalTheory.CompanionTheory.LatticePoint

theorem isOpen_valBall {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (γ : ValueGroupWithZero k) (hγ : γ ≠ 0) :
    IsOpen {x : k | valuation k x ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  change valuation k x ≤ γ at hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun y hy => ?_⟩
  change valuation k (y - x) < ((Units.mk0 γ hγ : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) at hy
  rw [Units.val_mk0] at hy
  show valuation k y ≤ γ
  calc valuation k y = valuation k ((y - x) + x) := by rw [sub_add_cancel]
    _ ≤ max (valuation k (y - x)) (valuation k x) := Valuation.map_add _ _ _
    _ ≤ γ := max_le hy.le hx

theorem exists_compact_open_addSubgroup_mem :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (n : ℕ) (x : Fin n → k),
      ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧
        IsOpen (A : Set (Fin n → k)) ∧ x ∈ A := by
  intro k _ _ _ _ n x
  let γ : ValueGroupWithZero k := Finset.univ.sup (fun i => valuation k (x i)) ⊔ 1
  have hγ : γ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one le_sup_right)
  let S : AddSubgroup k :=
    { carrier := {y | valuation k y ≤ γ}
      add_mem' := fun {a b} ha hb => by
        change valuation k a ≤ γ at ha
        change valuation k b ≤ γ at hb
        show valuation k (a + b) ≤ γ
        exact (Valuation.map_add _ _ _).trans (max_le ha hb)
      zero_mem' := by
        show valuation k 0 ≤ γ
        simp
      neg_mem' := fun {a} ha => by
        change valuation k a ≤ γ at ha
        show valuation k (-a) ≤ γ
        rwa [Valuation.map_neg] }
  have hS : (S : Set k) = {y | valuation k y ≤ γ} := rfl
  refine ⟨AddSubgroup.pi Set.univ (fun _ => S), ?_, ?_, ?_⟩
  · rw [AddSubgroup.coe_pi, hS]
    exact isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k γ
  · rw [AddSubgroup.coe_pi, hS]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_valBall γ hγ
  · rw [AddSubgroup.mem_pi]
    intro i _
    show valuation k (x i) ≤ γ
    exact le_sup_of_le_left (Finset.le_sup (f := fun i => valuation k (x i)) (Finset.mem_univ i))

end GlobalTheory.CompanionTheory.LatticePoint
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCosetRepsOpenInCompact
section
open Matrix

namespace GlobalTheory.CompanionTheory.Topology

theorem exists_finset_transversal_of_isCompact_of_isOpen
    (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (A L : AddSubgroup X) (hA : IsCompact (A : Set X)) (hL : IsOpen (L : Set X)) (_hLA : L ≤ A) :
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ (∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ L) := by
  classical
  have hcoset : ∀ x : X, ((↑) : X → X ⧸ L) '' (Homeomorph.addLeft x '' (L : Set X)) =
      {(x : X ⧸ L)} := by
    intro x
    ext q
    constructor
    · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      rw [Set.mem_singleton_iff, QuotientAddGroup.eq, Homeomorph.coe_addLeft]
      simpa using L.neg_mem hl
    · rintro rfl
      exact ⟨x, ⟨0, L.zero_mem, by simp⟩, rfl⟩
  have hdisc : DiscreteTopology (X ⧸ L) := by
    rw [discreteTopology_iff_isOpen_singleton]
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      rw [← hcoset x]
      exact QuotientAddGroup.isOpenMap_coe _ ((Homeomorph.addLeft x).isOpenMap _ hL)
  have hfin : (((↑) : X → X ⧸ L) '' (A : Set X)).Finite :=
    (hA.image continuous_quotient_mk').finite_of_discrete
  have hout : ∀ q : X ⧸ L, ((q.out : X) : X ⧸ L) = q := fun q => Quotient.out_eq q
  refine ⟨hfin.toFinset.image Quotient.out, ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_image] at ht
    obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := ht
    have h1 : -(a : X ⧸ L).out + a ∈ L := QuotientAddGroup.eq.1 (hout _)
    have h2 : (a : X ⧸ L).out = a - (-(a : X ⧸ L).out + a) := by abel
    rw [h2]
    exact A.sub_mem ha (_hLA h1)
  · intro a ha
    have hmem : (a : X ⧸ L).out ∈ hfin.toFinset.image Quotient.out :=
      Finset.mem_image.2 ⟨(a : X ⧸ L), (Set.Finite.mem_toFinset hfin).2 ⟨a, ha, rfl⟩, rfl⟩
    have hrel : -(a : X ⧸ L).out + a ∈ L := QuotientAddGroup.eq.1 (hout _)
    refine ⟨(a : X ⧸ L).out, ⟨hmem, by rw [sub_eq_neg_add]; exact hrel⟩, ?_⟩
    rintro t' ⟨ht', hat'⟩
    simp only [Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_image] at ht'
    obtain ⟨q', -, rfl⟩ := ht'
    have hq : q' = (a : X ⧸ L) := by
      rw [← hout q', QuotientAddGroup.eq]
      rw [sub_eq_neg_add] at hat'
      exact hat'
    rw [hq]

end GlobalTheory.CompanionTheory.Topology
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGlLastRowEq
section
open Matrix

namespace GlobalTheory.CompanionTheory.LinAlg

theorem exists_GL_lastRow_eq : ∀ (K : Type) [Field K] (n : ℕ) (a : Fin (n + 1) → K), a ≠ 0 →
    ∃ m : GL (Fin (n + 1)) K, vecMul (Pi.single (Fin.last n) 1) (m : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = a := by
  intro K _ n a ha
  classical
  set e : Fin (n + 1) → K := Pi.single (Fin.last n) 1 with he_def
  have he : e ≠ 0 := by simp [e]
  let f : (K ∙ e) ≃ₗ[K] (K ∙ a) :=
    (LinearEquiv.toSpanNonzeroSingleton K _ e he).symm ≪≫ₗ
      LinearEquiv.toSpanNonzeroSingleton K _ a ha
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have h1 : (LinearEquiv.toSpanNonzeroSingleton K _ e he).symm
      ⟨e, Submodule.mem_span_singleton_self e⟩ = 1 := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_one]
  have hga : g e = a := by
    have hx := hg ⟨e, Submodule.mem_span_singleton_self e⟩
    rw [← hx]
    simp only [f, LinearEquiv.trans_apply, h1, LinearEquiv.toSpanNonzeroSingleton_one]
  have hdet : IsUnit (LinearMap.toMatrix' (g : (Fin (n + 1) → K) →ₗ[K] Fin (n + 1) → K))ᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose, LinearMap.det_toMatrix']
    exact LinearEquiv.isUnit_det' g
  refine ⟨hdet.unit, ?_⟩
  rw [IsUnit.unit_spec, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
  simpa using hga

end GlobalTheory.CompanionTheory.LinAlg
end

