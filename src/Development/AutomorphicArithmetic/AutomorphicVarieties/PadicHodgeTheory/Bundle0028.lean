module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0083

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.EqZeroOfTwistedCommuteOfDistinctCharacters
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.linearIndependent_distinct_characters {Γ W ι : Type} [Group Γ] [AddCommGroup W] [Module ℂ W] [Fintype ι]
    (ρ : Γ →* Module.End ℂ W) (χ : ι → Γ →* ℂˣ) (y : ι → W) (hy : ∀ i, y i ≠ 0)
    (he : ∀ i σ, ρ σ (y i) = (χ i σ : ℂ) • y i) (hχ : Function.Injective χ) :
    LinearIndependent ℂ y := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hinj : Function.Injective (fun i => (Units.coeHom ℂ).comp (χ i)) := by
    intro a b hab
    apply hχ
    ext σ
    exact DFunLike.congr_fun hab σ
  have hli := (linearIndependent_monoidHom Γ ℂ).comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli
  have key : ∀ φ : Module.Dual ℂ W, c i * φ (y i) = 0 := by
    intro φ
    refine hli (fun j => c j * φ (y j)) ?_ i
    funext σ
    have h1 : φ (ρ σ (∑ j, c j • y j)) = 0 := by rw [hc, map_zero, map_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum] at h1
    rw [Finset.sum_apply, Pi.zero_apply, ← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, he, map_smul, map_smul]
    simp only [Pi.smul_apply, Function.comp_apply, MonoidHom.comp_apply, Units.coeHom_apply, smul_eq_mul]
    ring
  by_contra hci
  apply hy i
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  exact (mul_eq_zero.mp (key φ)).resolve_left hci

theorem UpperTheory.eq_zero_of_twisted_commute_of_distinct_characters :
    ∀ {Γ W : Type} [Group Γ] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {n : ℕ} (ρ : Γ →* Module.End ℂ W) (μ : Fin n → Γ →* ℂˣ) (ν : Γ →* ℂˣ) (N : Module.End ℂ W), Module.finrank ℂ W = n → (∀ j, ∃ y : W, y ≠ 0 ∧ ∀ σ, ρ σ y = (μ j σ : ℂ) • y) → Function.Injective μ → (∀ j k, μ j ≠ μ k * ν) → (∀ σ, ρ σ * N = (ν σ : ℂ) • (N * ρ σ)) → N = 0 := by
  intro Γ W _ _ _ _ n ρ μ ν N hn hy hμ hlink hN
  choose y hy0 hye using hy
  have hli : LinearIndependent ℂ y := UpperTheory.linearIndependent_distinct_characters ρ μ y hy0 hye hμ
  have hNy : ∀ k, N (y k) = 0 := by
    intro k
    by_contra hk
    have h2 : LinearIndependent ℂ (fun o : Option (Fin n) => o.elim (N (y k)) y) := by
      refine UpperTheory.linearIndependent_distinct_characters ρ (fun o : Option (Fin n) => o.elim (μ k * ν) μ) _ ?_ ?_ ?_
      · rintro (_ | j)
        · exact hk
        · exact hy0 j
      · rintro (_ | j) σ
        · have h3 := LinearMap.congr_fun (hN σ) (y k)
          simp only [Module.End.mul_apply, LinearMap.smul_apply, hye, map_smul, smul_smul] at h3
          simp only [Option.elim_none, MonoidHom.mul_apply, Units.val_mul]
          rw [h3, mul_comm]
        · exact hye j σ
      · rintro (_ | a) (_ | b) hab
        · rfl
        · exact absurd hab.symm (hlink b k)
        · exact absurd hab (hlink a k)
        · exact congrArg some (hμ hab)
    have h4 := h2.fintype_card_le_finrank
    rw [Fintype.card_option, Fintype.card_fin, hn] at h4
    omega
  have hspan : Submodule.span ℂ (Set.range y) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hn])
  refine LinearMap.ext_on_range hspan fun k => ?_
  rw [hNy k, LinearMap.zero_apply]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsCommonEigenline
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_common_eigenline :
    ∀ {H k : Type} [Group H] [TopologicalSpace H] [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} (r : H →* GL (Fin (n + 1)) k) (κ : Fin (n + 1) → H →* kˣ) (v : Fin (n + 1) → k), Continuous r → v ≠ 0 → (∀ g, (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ v = (κ 0 g : k) • v) → ∃ (p : GL (Fin (n + 1)) k) (r₁ : H →* GL (Fin (n + 1)) k) (r' : H →* GL (Fin n) k), (∀ g, r₁ g = p * r g * p⁻¹) ∧ Continuous r₁ ∧ Continuous r' ∧ (∀ g (i : Fin n), (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.succ 0 = 0) ∧ (∀ g, (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) 0 0 = (κ 0 g : k)) ∧ (∀ g (i j : Fin n), (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.succ j.succ = (r' g : Matrix (Fin n) (Fin n) k) i j) ∧ (HasFlag r' (fun i => κ i.succ) → HasFlag r κ) :=
  _root_.UpperTheory.Reformulated.B.BlockConjugation.exists_common_eigenline
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsCommonEigenvectorOfCharpolySplitCharacters
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_common_eigenvector_of_charpoly_split_characters :
    ∀ {Γ I W : Type} [Group Γ] [Group I] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {n : ℕ} (i : I →* Γ) (Φ : Γ) (ρ : Γ →* Module.End ℂ W) (μ : Fin n → Γ →* ℂˣ), (∀ σ s, ∃ t, σ * i s = i t * σ) → (∀ σ, ∃ (m : ℤ) (s : I), σ = Φ ^ m * i s) → (Set.range fun s => ρ (i s)).Finite → (∀ σ, (ρ σ).charpoly = ∏ j, (X - C (μ j σ : ℂ))) → ∀ j, ∃ y : W, y ≠ 0 ∧ ∀ σ, ρ σ y = (μ j σ : ℂ) • y := by
  intro Γ I W _ _ _ _ _ n i Φ ρ μ hnorm hgen hfin hchar j
  classical
  have htr : ∀ σ, LinearMap.trace ℂ W (ρ σ) = ∑ k, (μ k σ : ℂ) := by
    intro σ
    rw [LinearMap.trace_eq_matrix_trace ℂ (Module.Free.chooseBasis ℂ W),
      Matrix.trace_eq_neg_charpoly_nextCoeff, LinearMap.charpoly_toMatrix, hchar,
      Polynomial.prod_X_sub_C_nextCoeff, neg_neg]
  have heig : ∀ σ k, (ρ σ).HasEigenvalue (μ k σ : ℂ) := by
    intro σ k
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hchar, Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  let φ : I →* (Module.End ℂ W)ˣ := (ρ.toHomUnits).comp i
  have hφ : ∀ s, ((φ s : (Module.End ℂ W)ˣ) : Module.End ℂ W) = ρ (i s) := fun s => rfl
  have hker : ∀ k, φ.ker ≤ ((μ k).comp i).ker := by
    intro k s hs
    rw [MonoidHom.mem_ker] at hs ⊢
    have h1 : ρ (i s) = 1 := by rw [← hφ, hs]; rfl
    obtain ⟨v, hv⟩ := (heig (i s) k).exists_hasEigenvector
    have hv1 := hv.apply_eq_smul
    rw [h1, Module.End.one_apply] at hv1
    have h2 : ((μ k (i s) : ℂ) - 1) • v = 0 := by rw [sub_smul, one_smul, ← hv1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · apply Units.ext
      simp only [MonoidHom.comp_apply, Units.val_one]
      exact sub_eq_zero.mp h
    · exact absurd h hv.2
  have hfinU : (Set.range φ).Finite := by
    refine (Set.Finite.preimage (Function.Injective.injOn (fun a b h => Units.ext h)) hfin).subset ?_
    rintro _ ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  have hr : ∀ q : I ⧸ φ.ker, QuotientGroup.kerLift φ q ∈ Set.range φ := by
    intro q
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨s, (QuotientGroup.kerLift_mk φ s).symm⟩
  haveI : Finite (I ⧸ φ.ker) := by
    haveI := hfinU.to_subtype
    exact Finite.of_injective (fun q => (⟨_, hr q⟩ : Set.range φ))
      (fun a b hab => QuotientGroup.kerLift_injective φ (congrArg Subtype.val hab))
  letI : Fintype (I ⧸ φ.ker) := Fintype.ofFinite _
  let R : I ⧸ φ.ker →* Module.End ℂ W := (Units.coeHom (Module.End ℂ W)).comp (QuotientGroup.kerLift φ)
  let c : Fin n → (I ⧸ φ.ker →* ℂˣ) := fun k => QuotientGroup.lift φ.ker ((μ k).comp i) (hker k)
  have hR : ∀ s : I, R (s : I ⧸ φ.ker) = ρ (i s) := fun s => rfl
  have hc : ∀ k (s : I), c k (s : I ⧸ φ.ker) = μ k (i s) := fun k s => rfl
  let E : Submodule ℂ W := ⨅ s, (ρ (i s)).eigenspace (μ j (i s) : ℂ)
  have hmemE : ∀ y, y ∈ E ↔ ∀ s, ρ (i s) y = (μ j (i s) : ℂ) • y := by
    intro y
    simp only [E, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hEinv : ∀ y ∈ E, ρ Φ y ∈ E := by
    intro y hy
    rw [hmemE] at hy ⊢
    intro s
    obtain ⟨t, ht⟩ := hnorm Φ⁻¹ s
    have e1 : i s * Φ = Φ * i t := by
      calc i s * Φ = Φ * (Φ⁻¹ * i s) * Φ := by group
        _ = Φ * (i t * Φ⁻¹) * Φ := by rw [ht]
        _ = Φ * i t := by group
    have e2 : μ j (i s) = μ j (i t) := by
      have h3 := congrArg (μ j) e1
      simp only [map_mul] at h3
      rw [mul_comm (μ j Φ)] at h3
      exact mul_right_cancel h3
    calc ρ (i s) (ρ Φ y) = ρ (i s * Φ) y := by rw [map_mul]; rfl
      _ = ρ (Φ * i t) y := by rw [e1]
      _ = ρ Φ (ρ (i t) y) := by rw [map_mul]; rfl
      _ = (μ j (i s) : ℂ) • ρ Φ y := by rw [hy t, map_smul, e2]
  have hmain : ∃ y ∈ E, y ≠ 0 ∧ ρ Φ y = (μ j Φ : ℂ) • y := by
    by_contra hno
    push_neg at hno
    let A : Module.End ℂ E := (ρ Φ).restrict hEinv
    let p := LinearMap.charpoly A
    have hp : p.eval (μ j Φ : ℂ) ≠ 0 := by
      intro h0
      have hA : A.HasEigenvalue (μ j Φ : ℂ) := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr h0
      obtain ⟨v, hv⟩ := hA.exists_hasEigenvector
      have hv0 : (v : W) ≠ 0 := by
        intro h
        apply hv.2
        exact Subtype.ext h
      apply hno v v.2 hv0
      have h5 := congrArg Subtype.val hv.apply_eq_smul
      simpa [A] using h5
    let S := Finset.univ.filter (fun k : Fin n => (μ k Φ : ℂ) ≠ μ j Φ)
    let h := ∏ k ∈ S, (Polynomial.X - Polynomial.C (μ k Φ : ℂ))
    let f := h * p
    have key : ∀ y (hy : y ∈ E), Polynomial.aeval (ρ Φ) p y = ((Polynomial.aeval A p) ⟨y, hy⟩ : W) := by
      intro y hy
      rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range]
      simp [A, Module.End.pow_restrict, LinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Module.End.pow_restrict]
      rfl
    have hfE : ∀ y ∈ E, Polynomial.aeval (ρ Φ) f y = 0 := by
      intro y hy
      rw [Polynomial.aeval_mul, Module.End.mul_apply, key y hy, LinearMap.aeval_self_charpoly]
      simp
    let P : Module.End ℂ W := ∑ q : I ⧸ φ.ker, (((c j q)⁻¹ : ℂˣ) : ℂ) • R q
    have hRP : ∀ a, R a * P = ((c j a : ℂˣ) : ℂ) • P := by
      intro a
      simp only [P, Finset.mul_sum, mul_smul_comm, ← map_mul, Finset.smul_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun q => ?_)
      simp only [Equiv.coe_mulLeft, smul_smul, map_mul]
      congr 1
      rw [← Units.val_mul, _root_.mul_inv_rev, mul_left_comm, mul_inv_cancel, mul_one]
    have hPE : ∀ w, P w ∈ E := by
      intro w
      rw [hmemE]
      intro s
      rw [← hR s, ← Module.End.mul_apply, hRP, LinearMap.smul_apply, hc]
    have hfP : Polynomial.aeval (ρ Φ) f * P = 0 := by
      apply LinearMap.ext
      intro w
      rw [Module.End.mul_apply, LinearMap.zero_apply]
      exact hfE _ (hPE w)
    have htrq : ∀ s : I, LinearMap.trace ℂ W (Polynomial.aeval (ρ Φ) f * ρ (i s)) =
        ∑ k, f.eval (μ k Φ : ℂ) * (μ k (i s) : ℂ) := by
      intro s
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul, map_sum]
      simp_rw [smul_mul_assoc, map_smul, ← map_pow, ← map_mul, htr]
      simp only [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, Polynomial.eval_eq_sum_range,
        Finset.sum_mul, Finset.mul_sum, smul_eq_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun m _ => by ring))
    have hq : ∀ q, LinearMap.trace ℂ W (Polynomial.aeval (ρ Φ) f * R q) =
        ∑ k, f.eval (μ k Φ : ℂ) * (c k q : ℂ) := by
      intro q
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
      rw [hR, htrq]
      rfl
    have htot : LinearMap.trace ℂ W (Polynomial.aeval (ρ Φ) f * P) =
        ∑ k, f.eval (μ k Φ : ℂ) * ∑ q : I ⧸ φ.ker, (((c k q : ℂˣ) : ℂ) * (((c j q)⁻¹ : ℂˣ) : ℂ)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [P, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul, hq]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun q _ => by ring))
    have hψ : ∀ k, ∑ q : I ⧸ φ.ker, (((c k q : ℂˣ) : ℂ) * (((c j q)⁻¹ : ℂˣ) : ℂ)) =
        ((if (Units.coeHom ℂ).comp (c k / c j) = 1 then Fintype.card (I ⧸ φ.ker) else 0 : ℕ) : ℂ) := by
      intro k
      rw [← sum_hom_units]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      simp [div_eq_mul_inv]
    have hzero : ∀ k, (μ k Φ : ℂ) ≠ μ j Φ → f.eval (μ k Φ : ℂ) = 0 := by
      intro k hk
      simp only [f, Polynomial.eval_mul, h, Polynomial.eval_prod]
      rw [Finset.prod_eq_zero (i := k) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩) (by simp), zero_mul]
    have hfl : f.eval (μ j Φ : ℂ) ≠ 0 := by
      simp only [f, Polynomial.eval_mul, h, Polynomial.eval_prod]
      refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)) hp
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact sub_ne_zero.mpr (Ne.symm (Finset.mem_filter.mp hk).2)
    let N : ℕ := ∑ k ∈ Finset.univ.filter (fun k : Fin n => (μ k Φ : ℂ) = μ j Φ),
      (if (Units.coeHom ℂ).comp (c k / c j) = 1 then Fintype.card (I ⧸ φ.ker) else 0)
    have hN : N ≠ 0 := by
      have hj : j ∈ Finset.univ.filter (fun k : Fin n => (μ k Φ : ℂ) = μ j Φ) := by simp
      have h7 : (Units.coeHom ℂ).comp (c j / c j) = 1 := by simp
      intro h8
      have h9 := (Finset.sum_eq_zero_iff.mp h8) j hj
      rw [if_pos h7] at h9
      exact Fintype.card_ne_zero h9
    have heq : LinearMap.trace ℂ W (Polynomial.aeval (ρ Φ) f * P) = f.eval (μ j Φ : ℂ) * N := by
      rw [htot]
      simp only [hψ, N, Nat.cast_sum, Finset.mul_sum]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      by_cases hk : (μ k Φ : ℂ) = μ j Φ
      · rw [if_pos hk, hk]
      · rw [if_neg hk, hzero k hk, zero_mul]
    rw [hfP, map_zero] at heq
    exact mul_ne_zero hfl (Nat.cast_ne_zero.mpr hN) heq.symm
  obtain ⟨y, hyE, hy0, hyΦ⟩ := hmain
  refine ⟨y, hy0, ?_⟩
  let G : Subgroup Γ :=
    { carrier := {σ | ρ σ y = (μ j σ : ℂ) • y}
      mul_mem' := by
        intro a b ha hb
        show ρ (a * b) y = (μ j (a * b) : ℂ) • y
        rw [map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul, map_mul, Units.val_mul, mul_comm]
      one_mem' := by
        show ρ 1 y = (μ j 1 : ℂ) • y
        simp
      inv_mem' := by
        intro a ha
        show ρ a⁻¹ y = (μ j a⁻¹ : ℂ) • y
        have h4 : y = ρ a⁻¹ (ρ a y) := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rw [ha, map_smul] at h4
        rw [map_inv (μ j), Units.val_inv_eq_inv_val]
        calc ρ a⁻¹ y = (μ j a : ℂ)⁻¹ • ((μ j a : ℂ) • ρ a⁻¹ y) := by
              rw [smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]
          _ = (μ j a : ℂ)⁻¹ • y := by rw [← h4] }
  intro σ
  obtain ⟨m, s, rfl⟩ := hgen σ
  have h1 : Φ ∈ G := hyΦ
  have h2 : i s ∈ G := (hmemE y).1 hyE s
  exact G.mul_mem (G.zpow_mem h1 m) h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsInvariantOfDpstPhiFixedOfNonnegWeights
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_invariant_of_dpst_phi_fixed_of_nonneg_weights :
    ∀ {l : ℕ} [Fact l.Prime] {K L : FinExt l}, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ L.1) → ∀ {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK K) V), FiniteDimensional ↥L.1 ↥(DdR ((UpperTheory.V.Loc.PP l).PD K) ρ) → (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (c : ℤ), c < 0 → multV ((UpperTheory.V.Loc.PP l).PD K) ρ τ c = 0) → ∀ z : ↥(Dpst (UpperTheory.V.Loc.PP l) ρ), z ≠ 0 → monD (UpperTheory.V.Loc.PP l) ρ z = 0 → phiD (UpperTheory.V.Loc.PP l) ρ z = z → (∀ g, actD (UpperTheory.V.Loc.PP l) ρ g z = z) → ∃ v : V, v ≠ 0 ∧ ∀ g, ρ g v = v := by
  intro l _ K L key V _ _ _ _ _ ρ hfin hm z hz hN hφ hG
  let P := UpperTheory.V.Loc.PP l
  obtain ⟨y, hy, e⟩ := (mem_Dst_and_monV_eq_zero_iff l P K L V ρ z.1).mp
    ⟨(mem_Dst P ρ).mpr fun g => congrArg Subtype.val (hG g), congrArg Subtype.val hN⟩
  have hy' : ∀ g, actVB (P.PD K) ρ g y = y := by
    intro g
    have := (Submodule.mem_iInf _).mp hy g
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
  have c1 : ∀ x : TensorProduct ℚ_[l] V P.R.B, phiV P ↥L.1 V (crisIncl P ↥L.1 V x) =
      crisIncl P ↥L.1 V (LinearMap.lTensor V P.φB.toLinearMap x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have h1 : LinearMap.lTensor V P.φB.toLinearMap y = y := by
    apply crisIncl_injective (LL := ↥L.1) P
    rw [← c1, e]
    exact congrArg Subtype.val hφ
  have c2 : ∀ g (x : TensorProduct ℚ_[l] V P.R.B),
      actVdR (P.PD K) ρ g (LinearMap.lTensor V P.ιB.toLinearMap x) =
      LinearMap.lTensor V P.ιB.toLinearMap (actVB (P.PD K) ρ g x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      have := (P.PD K).ι_comm g b
      rw [P.PD_ι, P.PD_ι] at this
      simp [actVdR, actVB, this]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have h2 : LinearMap.lTensor V P.ιB.toLinearMap y ∈ DdR (P.PD K) ρ := by
    refine (Submodule.mem_iInf _).mpr fun g => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, c2, hy']
  have h3 := (UpperTheory.ddR_le_fil_and_inf_fil_eq_bot_of_hodgeTate_mult P key ρ hfin).1 0 hm h2
  have hF : ((P.PD (UpperTheory.V.Loc.botExt l)).Fil 0).restrictScalars ℚ_[l] =
      ((P.PD K).Fil 0).restrictScalars ℚ_[l] := SetLike.coe_injective (P.PD_Fil _ _ 0)
  have h4 : LinearMap.lTensor V P.ιB.toLinearMap y ∈ UpperTheory.V.Loc.FilT ↥L.1 V 0 := by
    unfold UpperTheory.V.Loc.FilT
    unfold FilV at h3
    rw [← hF] at h3
    exact h3
  obtain ⟨v, hv, hu⟩ := UpperTheory.V.Loc.lineInv (A := ↥L.1) y h1 h4
  refine ⟨v, ?_, fun g => hu _ ?_⟩
  · rintro rfl
    apply hz
    apply Subtype.ext
    rw [← e, hv]
    simp
  · have := hy' g
    rw [← this, hv]
    simp [actVB]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsInvariantVectorOfFiniteImageAveraging
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.fixed_vector_descends_finite_image {Γ L D W : Type} [Group Γ] [Field L] [AddCommGroup D] [Module L D]
    [AddCommGroup W] [Module ℂ W] (a : Γ →* Module.End L D) (b : Γ →* Module.End ℂ W) (mk : D →+ W)
    (hs : Submodule.span ℂ (Set.range mk) = ⊤) (hc : ∀ g x, b g (mk x) = mk (a g x))
    [Finite (Γ ⧸ a.ker)] (y : W) (hy : y ≠ 0) (hi : ∀ g, b g y = y) :
    ∃ x : D, x ≠ 0 ∧ ∀ g, a g x = x := by
  classical
  by_contra hn
  push Not at hn
  let := Fintype.ofFinite (Γ ⧸ a.ker)
  let a' : Γ ⧸ a.ker →* Module.End L D := QuotientGroup.lift a.ker a le_rfl
  have ha : ∀ q : Γ ⧸ a.ker, a q.out = a' q := fun q => by
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have h0 : ∀ x : D, ∑ q : Γ ⧸ a.ker, a' q x = 0 := fun x => by
    by_contra hx
    obtain ⟨g, hg⟩ := hn _ hx
    refine hg ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (g : Γ ⧸ a.ker)) _ _ fun q => ?_
    rw [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply]
    rfl
  have h1 : (∑ q : Γ ⧸ a.ker, b q.out) = 0 := by
    refine LinearMap.ext_on_range hs fun x => ?_
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    simp only [hc, ha]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, h0, map_zero]
  have h2 := LinearMap.congr_fun h1 y
  rw [LinearMap.sum_apply, LinearMap.zero_apply] at h2
  simp only [hi, Finset.sum_const, Finset.card_univ] at h2
  rw [← Nat.cast_smul_eq_nsmul ℂ] at h2
  exact hy ((smul_eq_zero.mp h2).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))

theorem UpperTheory.exists_invariant_vector_of_finite_image_averaging :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (P : LocPrime l) {L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)], (∃ y : WDSpace P ι ρ, y ≠ 0 ∧ ∀ s, wdRho P ι Bw h hj ρ (ineIncl h s) y = y) → (∀ y : WDSpace P ι ρ, (∀ s, wdRho P ι Bw h hj ρ (ineIncl h s) y = y) → ∀ σ, wdRho P ι Bw h hj ρ σ y = y) → (∃ x : ↥(Dpst P ρ), x ≠ 0 ∧ ∀ s, weilD Bw h P ρ (ineIncl h s) x = x) ∧ ∀ x : ↥(Dpst P ρ), (∀ s, weilD Bw h P ρ (ineIncl h s) x = x) → ∀ σ, weilD Bw h P ρ σ x = x := by
  intro F Ω _ _ _ _ _ l _ ι A w h O _ _ _ Bw hj P L V _ _ _ _ _ ρ _ h1 h2
  refine ⟨?_, fun x hx σ => ?_⟩
  · obtain ⟨y, hy, hi⟩ := h1
    have := compactSpace_Ine (E := F) A
    have : Finite (Ine (F := F) A ⧸ (MonoidHom.comp (weilD Bw h P ρ) (ineIncl h)).ker) :=
      Subgroup.quotient_finite_of_isOpen _ (isSmooth_weilD Bw h P ρ hj)
    exact UpperTheory.fixed_vector_descends_finite_image (MonoidHom.comp (weilD Bw h P ρ) (ineIncl h))
      (MonoidHom.comp (wdRho P ι Bw h hj ρ) (ineIncl h))
      (AddMonoidHom.mk' (wdMk P ι ρ) (wdMk_add P ι ρ)) (span_wdMk P ι ρ)
      (fun g x => wdRho_mk P ι Bw h hj ρ _ x) y hy hi
  · have hc : ∀ (n : ℕ) τ, Commute (phiD P ρ ^ n) (weilD Bw h P ρ τ) := fun n τ => by
      refine Commute.pow_left ?_ n
      rw [weilD_apply]
      refine Commute.mul_right (phiD_actD P ρ _) ?_
      exact Commute.units_zpow_right (u := phiU P ρ) (Commute.refl _) _
    have hc' : ∀ (n : ℕ) τ, weilD Bw h P ρ τ ((phiD P ρ ^ n) x) = (phiD P ρ ^ n) (weilD Bw h P ρ τ x) :=
      fun n τ => (LinearMap.congr_fun (hc n τ).eq x).symm
    refine sub_eq_zero.mp
      (GlobalTheory.PstFaithful.eq_zero_of_wdMk_phiD_pow l P ι _ L V ρ _ fun n => ?_)
    have h3 := h2 (wdMk P ι ρ ((phiD P ρ ^ n) x)) (fun s => by rw [wdRho_mk, hc', hx]) σ
    rw [wdRho_mk, hc'] at h3
    have h4 := wdMk_add P ι ρ ((phiD P ρ ^ n) (weilD Bw h P ρ σ x - x)) ((phiD P ρ ^ n) x)
    rw [← map_add (f := _), sub_add_cancel, h3] at h4
    exact left_eq_add.mp (h4.trans (add_comm _ _))
end

