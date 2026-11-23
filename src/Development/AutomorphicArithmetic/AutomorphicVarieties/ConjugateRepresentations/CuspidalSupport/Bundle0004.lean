module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SatArith
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem es_zero (A : Multiset ℂ) : A.esymm 0 = 1 := by simp [Multiset.esymm]

private theorem es_cons (a : ℂ) (A : Multiset ℂ) (k : ℕ) :
    (a ::ₘ A).esymm (k + 1) = A.esymm (k + 1) + a * A.esymm k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]

private theorem es_big (A : Multiset ℂ) {k : ℕ} (h : A.card < k) : A.esymm k = 0 := by
  simp [Multiset.esymm, Multiset.powersetCard_eq_empty k h]

private theorem es_add (A C : Multiset ℂ) (j : ℕ) :
    (A + C).esymm j = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal j, A.esymm p.1 * C.esymm p.2 := by
  induction A using Multiset.induction_on generalizing j with
  | empty =>
    rw [Finset.sum_eq_single (0, j)]
    · simp [es_zero]
    · rintro ⟨i, k⟩ hp hne
      have : 0 < i := by
        rcases Nat.eq_zero_or_pos i with rfl | h
        · simp at hp; simp [hp] at hne
        · exact h
      rw [es_big 0 (by simpa using this), zero_mul]
    · simp
  | cons a A ih =>
    cases j with
    | zero => simp [es_zero]
    | succ j =>
      rw [Multiset.cons_add, es_cons, ih, ih, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ]
      simp only [es_cons, es_zero, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, add_assoc]

private theorem es_add_fin (A C : Multiset ℂ) {r s : ℕ} (hA : A.card = r) (hC : C.card = s) (j : ℕ) :
    (A + C).esymm j =
      ∑ p : Fin (r + 1) × Fin (s + 1), if (p.1 : ℕ) + p.2 = j then A.esymm p.1 * C.esymm p.2 else 0 := by
  rw [es_add, ← Finset.sum_filter]
  symm
  refine Finset.sum_of_injOn (fun p => ((p.1 : ℕ), (p.2 : ℕ))) ?_ ?_ ?_ fun _ _ => rfl
  · rintro ⟨a, b⟩ - ⟨c, d⟩ - h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
  · intro p hp
    simpa using hp
  · rintro ⟨i, k⟩ hp hn
    by_cases hi : r < i
    · rw [es_big A (hA ▸ hi), zero_mul]
    by_cases hk : s < k
    · rw [es_big C (hC ▸ hk), mul_zero]
    exact absurd ⟨(⟨i, by omega⟩, ⟨k, by omega⟩), by simpa using hp, rfl⟩ hn

private theorem es_scale (A : Multiset ℂˣ) (c : ℂˣ) (k : ℕ) :
    ((A.map (· * c)).map fun b : ℂˣ => (b : ℂ)).esymm k = (c : ℂ) ^ k * (A.map fun b : ℂˣ => (b : ℂ)).esymm k := by
  rw [← smul_eq_mul, Multiset.pow_smul_esymm]
  simp [Multiset.map_map, mul_comm]

theorem UpperTheory.V.Cj.S.satArith :
    UpperTheory.V.Cj.S.SatArith := by
  intro q r s hq B B₁ B₂ hB h₁ h₂ h α β hα hβ
  refine eq_of_satEig_eq hq hB (by simp [h₁, h₂]) fun j hj => ?_
  rw [← h j hj, satEig, Multiset.map_add (f := _), es_add_fin (r := r) (s := s) _ _ (by simpa using h₁) (by simpa using h₂),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold coef
  split_ifs with hp
  swap
  · simp
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hk : (p.2 : ℕ) ≤ s := Nat.lt_succ_iff.1 p.2.2
  have key : (q : ℂ) ^ ((p.1 : ℕ) * (s - p.2)) * (q : ℂ) ^ ((((p.1 : ℕ) : ℂ) * ((r : ℂ) - (p.1 : ℕ))) / 2) *
      (q : ℂ) ^ ((((p.2 : ℕ) : ℂ) * ((s : ℂ) - (p.2 : ℕ))) / 2) =
      (q : ℂ) ^ (((j : ℂ) * (((r + s : ℕ) : ℂ) - j)) / 2) * (α : ℂ) ^ (p.1 : ℕ) * (β : ℂ) ^ (p.2 : ℕ) := by
    rw [hα, hβ, ← Complex.cpow_nat_mul, ← Complex.cpow_nat_mul, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hq',
      ← Complex.cpow_add _ _ hq', ← Complex.cpow_add _ _ hq', ← Complex.cpow_add _ _ hq', ← hp]
    congr 1
    push_cast [hk]
    ring
  rw [es_scale, es_scale, satEig, satEig]
  linear_combination ((B₁.map fun b : ℂˣ => (b : ℂ)).esymm p.1 * (B₂.map fun b : ℂˣ => (b : ℂ)).esymm p.2) * key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SingleBdd
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem exists_types {G H : Type} [Group G] [Group H] (i : H →* G) (W : Submodule ℂ (G → ℂ))
    [FiniteDimensional ℂ W] (hW : ∀ h, ∀ f ∈ W, (fun g => f (g * i h)) ∈ W) :
    ∃ V : Submodule ℂ (H → ℂ), FiniteDimensional ℂ V ∧ (∀ f ∈ V, ∀ k', (fun k => f (k * k')) ∈ V) ∧
      ∀ f ∈ W, ∀ g, (fun k => f (g * i k)) ∈ V := by
  let ρ : H → W →ₗ[ℂ] W := fun h => (LinearMap.funLeft ℂ ℂ fun g => g * i h).restrict (hW h)
  have hρ : ∀ k k' w, ρ (k * k') w = ρ k (ρ k' w) := fun k k' w =>
    Subtype.ext (funext fun g => by
      change w.1 (g * i (k * k')) = w.1 (g * i k * i k')
      rw [map_mul, mul_assoc])
  let m : Module.Dual ℂ W →ₗ[ℂ] W →ₗ[ℂ] (H → ℂ) :=
    LinearMap.mk₂ ℂ (fun l w k => l (ρ k w)) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => by funext k; simp) (fun _ _ _ => by funext k; simp)
  refine ⟨LinearMap.range (TensorProduct.lift m), inferInstance, ?_, fun f hf g => ?_⟩
  · rintro _ ⟨t, rfl⟩ k'
    induction t using TensorProduct.inductionOn with
    | tmul l w => exact ⟨l ⊗ₜ ρ k' w, funext fun k => congrArg l (hρ k k' w).symm⟩
    | add s t hs ht => rw [map_add]; exact add_mem hs ht
  · exact ⟨((LinearMap.proj g).comp W.subtype) ⊗ₜ ⟨f, hf⟩, rfl⟩

private theorem exists_types' {G H : Type} [Group G] [Group H] (i : H →* G) (C : Subgroup G) (hi : ∀ k, i k ∈ C) (f : G → ℂ)
    (hf : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : C => GroundTheory.Automorphic.rightTranslate (k : G) f))) :
    ∃ V : Submodule ℂ (H → ℂ), FiniteDimensional ℂ V ∧ (∀ f ∈ V, ∀ k', (fun k => f (k * k')) ∈ V) ∧
      ∀ g, (fun k => f (g * i k)) ∈ V := by
  obtain ⟨V, h1, h2, h3⟩ := exists_types i
    (Submodule.span ℂ (Set.range fun k : C => GroundTheory.Automorphic.rightTranslate (k : G) f)) (fun k ψ hψ => by
      induction hψ using Submodule.span_induction with
      | mem ψ hψ =>
        obtain ⟨l, rfl⟩ := hψ
        exact Submodule.subset_span ⟨⟨i k, hi k⟩ * l, funext fun g => congrArg f (mul_assoc g (i k) l.1).symm⟩
      | zero => exact zero_mem _
      | add _ _ _ _ a b => exact add_mem a b
      | smul c _ _ a => exact Submodule.smul_mem _ c a)
  exact ⟨V, h1, h2, h3 f (Submodule.subset_span ⟨1, funext fun g => congrArg f (mul_one g)⟩)⟩

private theorem exists_monic {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (W : Submodule ℂ M)
    [FiniteDimensional ℂ W] (hW : ∀ x ∈ W, T x ∈ W) : UpperTheory.V.Af.Fin.AlgMod W ⊥ T := by
  obtain ⟨p, hp, h⟩ := LinearMap.exists_monic_and_aeval_eq_zero ℂ (T.restrict hW)
  refine ⟨p, hp, fun x hx => ?_⟩
  have key : ∀ q : Polynomial ℂ, Polynomial.aeval T q x = (Polynomial.aeval (T.restrict hW) q ⟨x, hx⟩ : W) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add q r hq hr => simp only [map_add (f := _), LinearMap.add_apply, hq, hr, Submodule.coe_add]
    | monomial n c =>
      simp only [Polynomial.aeval_monomial, mul_apply_eq_comp, Module.algebraMap_end_apply, Submodule.coe_smul,
        Module.End.pow_restrict n hW, LinearMap.restrict_apply]
  rw [key, h]
  rfl

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm in
private theorem bdd_span {K : Type} [Field K] [NumberField K] {n : ℕ} (f : archSmooth K n) (h : IsAutomorphicForm f.1) :
    Bdd (Submodule.span ℂ {f}) := by
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, ?_, ?_, fun z hz => ?_⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    exact h.isLeftInvariant.smul c
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    exact h.hasModerateGrowth.smul c
  · obtain ⟨U, -, hU⟩ := exists_openSubgroup_rightInvariant h.isSmooth h.isKFinite
    refine ⟨U.toSubgroup, U.isOpen, fun φ hφ u hu g => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    exact congrArg (c • ·) (hU g u hu)
  · have hK := h.isKFinite
    unfold IsKFinite at hK
    obtain ⟨V, h1, h2, h3⟩ := exists_types' ((infEmb K n).comp (archCompact K n).subtype) Reduction.maxCompact
      (fun k => k.2) f.1 hK
    refine ⟨V, h1, h2, fun φ hφ g => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    exact V.smul_mem c (h3 g)
  · have hZ : IsZFinite f := h.isZFinite
    unfold IsZFinite at hZ
    refine (exists_monic (uAction z) (Submodule.span ℂ
      ((fun z => uAction z f) '' ((isExpLieAlgebra K n).centerU : Set (UEnv K n)))) (fun ψ hψ => ?_)).mono
      (Submodule.span_mono ?_)
    · induction hψ using Submodule.span_induction with
      | mem ψ hψ =>
        obtain ⟨y, hy, rfl⟩ := hψ
        exact Submodule.subset_span ⟨z * y, mul_mem hz hy, by simp only [map_mul, mul_apply_eq_comp]⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add _ _ _ _ a b => rw [map_add]; exact add_mem a b
      | smul c _ _ a => rw [map_smul]; exact Submodule.smul_mem _ c a
    · rintro _ rfl
      exact ⟨1, one_mem _, by simp only [map_one, Module.End.one_apply]⟩

theorem UpperTheory.V.Cj.S.singleBdd :
    UpperTheory.V.Cj.S.SingleBdd := by
  intro E _ _ _ a φ h
  unfold BddS
  rw [Submodule.map_span, Set.image_singleton]
  exact bdd_span _ ((UpperTheory.V.Cm.isAutForm_iff φ).1 h)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SliceBdd
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section SlopeTestRemainingChoices

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin

variable {K : Type} [Field K] [NumberField K]

private theorem left_slSp {a n : ℕ} (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n))
    (S : Submodule ℂ (archSmooth K n))
    (h : ∀ ψ ∈ S, ∀ g ∈ Γ, ∀ γ m, ψ.1 (g * emb e (AdelicGLn.diagonal K a γ * m)) = ψ.1 (g * emb e m)) :
    ∀ f ∈ slSp e Γ S, IsLeftInvariant f.1 := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ψ, hψ, g, hg, hf⟩ := hf
    intro γ m
    rw [hf, hf, h ψ hψ g hg]
  | zero => exact isLeftInvariant_zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

private theorem bdd_slices {r s : ℕ} {S : Submodule ℂ (archSmooth K (r + s))} (hS : Bdd S) (hK : Sat S) :
    Bdd (slSp (e1 r s) (Set.range (emb (e2 r s))) (ctSp r S)) ∧
      Bdd (slSp (e2 r s) (Set.range (emb (e1 r s))) (ctSp r S)) := by
  obtain ⟨ι, _, ⟨D⟩⟩ := UpperTheory.exists_idempotent_decomposition_mixedSpace K
  obtain ⟨hN, hG, hL, hK', hM⟩ := UpperTheory.constantTermSpace_automorphic_properties K r s S hS hK
  have hT := UpperTheory.constantTermSpace_types_of_bdd K _ r S hS
  have hA := UpperTheory.algebraic_module_of_vanishing_block K r s _ hN (UpperTheory.constantTermSpace_centre_of_bdd K _ r S hS) ι D
  refine ⟨⟨left_slSp _ _ _ ?_, (UpperTheory.slSp_preserves_growth_and_level K _ _ _ _ _).1 hG,
      (UpperTheory.slSp_preserves_growth_and_level K _ _ _ _ _).2 hL, UpperTheory.finiteDimensional_slSp_reduction K _ _ _ _ _ hT,
      UpperTheory.siegelLevi_block_aeval_stable K _ _ _ _ _ (Van K r s) ι D ?_ fun τ u => (hA τ u).1⟩,
    ⟨left_slSp _ _ _ ?_, (UpperTheory.slSp_preserves_growth_and_level K _ _ _ _ _).1 hG,
      (UpperTheory.slSp_preserves_growth_and_level K _ _ _ _ _).2 hL, UpperTheory.finiteDimensional_slSp_reduction K _ _ _ _ _ hT,
      UpperTheory.siegelLevi_block_aeval_stable K _ _ _ _ _ (Van K r s) ι D ?_ fun τ u => (hA τ u).2⟩⟩
  · rintro ψ hψ _ ⟨m₂, rfl⟩ γ m
    rw [← hM ψ hψ γ 1 (emb (e2 r s) m₂ * emb (e1 r s) m), map_mul, ← mul_assoc, ← emb_comm, blk, map_one, mul_one,
      ← (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K _ _ _).2.1, mul_assoc]
  · rintro ψ hψ _ ⟨m₂, rfl⟩ m
    rw [← emb_comm]
    exact hψ m m₂
  · rintro ψ hψ _ ⟨m₁, rfl⟩ γ m
    rw [← hM ψ hψ 1 γ (emb (e1 r s) m₁ * emb (e2 r s) m), map_mul, ← mul_assoc, emb_comm, blk, map_one, one_mul,
      ← (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K _ _ _).2.1, mul_assoc]
  · rintro ψ hψ _ ⟨m₁, rfl⟩ m
    exact hψ m₁ m

private theorem exists_slice {a n : ℕ} (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n))
    (S : Submodule ℂ (archSmooth K n)) {ψ : archSmooth K n} (hψ : ψ ∈ S) {g : AdelicGLn.AdelicGL K n} (hg : g ∈ Γ) :
    ∃ f ∈ slSp e Γ S, ∀ m, f.1 m = ψ.1 (g * emb e m) := by
  obtain ⟨f, hf, -⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie K a n e g
  exact ⟨f ψ, Submodule.subset_span ⟨ψ, hψ, g, hg, hf ψ⟩, hf ψ⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.S.sliceBdd :
    UpperTheory.V.Cj.S.SingleBdd → UpperTheory.V.Cj.S.SliceBdd := by
  intro hB E _ _ _ r s φ hφ
  obtain ⟨S, hle, hS, hK⟩ := UpperTheory.exists_automorphic_saturation_submodule E (r + s) _ (hB E (r + s) φ hφ)
  have hmem : UpperTheory.V.Cm.smEq E (r + s) φ ∈ S :=
    hle (Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self φ))
  obtain ⟨hs, -⟩ := UpperTheory.constantTerm_archSmooth E (r + s) r (UpperTheory.V.Cm.smEq E (r + s) φ) (UpperTheory.isAutomorphicForm_of_bdd_submodule E _ S hS _ hmem)
  have hψ : (⟨_, hs⟩ : GroundTheory.Automorphic.AutomorphicForm.archSmooth E (r + s)) ∈ UpperTheory.V.Af.Fin.ctSp r S :=
    Submodule.subset_span ⟨_, hmem, rfl⟩
  obtain ⟨h₁, h₂⟩ := bdd_slices hS hK
  refine ⟨Submodule.comap (UpperTheory.V.Cm.smEq E r).toLinearMap _, Submodule.comap (UpperTheory.V.Cm.smEq E s).toLinearMap _,
    h₁.mono (Submodule.map_comap_le _ _), h₂.mono (Submodule.map_comap_le _ _), fun y => ?_, fun x => ?_⟩
  · obtain ⟨f, hf, hf'⟩ := exists_slice (e1 r s) (Set.range (emb (e2 r s))) _ hψ ⟨y, rfl⟩
    refine ⟨(UpperTheory.V.Cm.smEq E r).symm f, by simpa using hf, funext fun x => (hf' x).trans ?_⟩
    rw [← UpperTheory.V.Af.Fin.emb_comm]
    rfl
  · obtain ⟨f, hf, hf'⟩ := exists_slice (e2 r s) (Set.range (emb (e1 r s))) _ hψ ⟨x, rfl⟩
    exact ⟨(UpperTheory.V.Cm.smEq E s).symm f, by simpa using hf, funext fun y => hf' y⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.StabSp
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.stabSp :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.LevelSplit → UpperTheory.V.Cj.S.HullBdd → UpperTheory.V.Cj.S.HullOps → UpperTheory.V.Cj.S.StabSp := by
  intro hC hL hB hO E _ _ _ a S hS
  obtain ⟨L, hLo, hl⟩ := hS.level
  obtain ⟨L', hL'o, hle, T, hT, hsp⟩ := hL E a L hLo
  obtain ⟨h1, h2, h3⟩ := hO E a S
  have hb := hB E a S hS L' hL'o
  have hK : ∀ w ∉ T, fixed (finRep E a) L' ≤ fixed (fL a w) (KGL w (n := a)) := fun w hw φ hφ =>
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => GlobalTheory.LGrp.mem_fixed.1 hφ _ ((hsp w hw).1 k hk)
  refine ⟨T, hT, hull S ⊓ fixed (finRep E a) L', le_inf h1 fun φ hφ => ?_, ?_, fun φ hφ => ?_,
    fun w hw => inf_le_right.trans (hK w hw), ?_⟩
  · refine GlobalTheory.LGrp.mem_fixed.2 fun u hu => Subtype.ext (funext fun g => ?_)
    have := hl _ ⟨φ, hφ, rfl⟩ u (hle hu) g
    rw [UpperTheory.V.Fb.finEmb_eq] at this
    exact this
  · haveI := UpperTheory.V.Af.Fin.formsFinite E a _ hb
    exact Module.Finite.equiv (Submodule.equivMapOfInjective _ (UpperTheory.V.Cm.smEq E a).injective _).symm
  · exact (UpperTheory.V.Cm.isAutForm_iff φ).2 (UpperTheory.isAutomorphicForm_of_bdd_submodule E a _ hb _ ⟨φ, hφ, rfl⟩)
  · rintro (⟨t, u⟩ | ⟨⟨w, hw⟩, h, hh⟩) φ ⟨hφ, hφ'⟩
    · refine ⟨h2 t u φ hφ, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_⟩
      have e := LinearMap.congr_fun ((hC E a t u).1 (finGL E a k)).eq φ
      have e' : rt E a (finGL E a k) φ = φ := GlobalTheory.LGrp.mem_fixed.1 hφ' k hk
      rw [Module.End.mul_apply, Module.End.mul_apply, e'] at e
      exact e.symm
    · have hc := Final.GLintComm E w a
      refine ⟨?_, GlobalTheory.LGrp.mem_fixed.2 fun u hu => ?_⟩
      · change heckeVec (fL a w) (KGL w (n := a)) h φ ∈ hull S
        rw [heckeVec, finsum_eq_sum (fun c : _ ⧸ KGL w (n := a) => h c.out • fL a w c.out φ) (finite_heckeVec hc hh (fL a w) φ)]
        exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (h3 _ φ hφ)
      · change finRep E a u (heckeVec (fL a w) (KGL w (n := a)) h φ) = heckeVec (fL a w) (KGL w (n := a)) h φ
        obtain ⟨k, hk, u', hu', e1, rfl⟩ := (hsp w hw).2 u hu
        have e2 := map_heckeVec hc hh (ρ := fL a w) (ρ' := fL a w) (finRep E a u') (fun g y => by
          change finRep E a u' (finRep E a (locGL E a w g) y) = finRep E a (locGL E a w g) (finRep E a u' y)
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
            LocUniq.comm_locGL w e1]) φ
        rw [map_mul, Module.End.mul_apply, e2, GlobalTheory.LGrp.mem_fixed.1 hφ' u' hu']
        exact GlobalTheory.LGrp.mem_fixed.1 (SatCompare.heckeVec_mem_fixed hc hh (hK w hw hφ')) k hk
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SumInner
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem sum_three {A B C P R : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype P] [Fintype R]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq P]
    (f : A → P) (f' : B → P) (f'' : C → P) (h : Function.Bijective (Sum.elim (Sum.elim f f') f''))
    (g : (A → R) → (B → R) → ℂ) :
    ∑ c : P → R, g (c ∘ f) (c ∘ f') = (Fintype.card R : ℂ) ^ Fintype.card C * ∑ c₁, ∑ c₂, g c₁ c₂ := by
  let e : (P → R) ≃ ((A → R) × (B → R)) × (C → R) :=
    ((Equiv.ofBijective _ h).symm.arrowCongr (Equiv.refl R)).trans
      ((Equiv.sumArrowEquivProdArrow _ _ _).trans
        ((Equiv.sumArrowEquivProdArrow _ _ _).prodCongr (Equiv.refl _)))
  have h1 : ∑ c : P → R, g (c ∘ f) (c ∘ f') = ∑ x : ((A → R) × (B → R)) × (C → R), g x.1.1 x.1.2 :=
    Fintype.sum_equiv e _ _ (fun c => rfl)
  rw [h1, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul]
  rw [← Finset.mul_sum, Fintype.sum_prod_type]
  push_cast
  rfl

private def pair3 {r s : ℕ} (S : Finset (Fin (r + s))) (p : sub1 S × ((sub2 S)ᶜ : Finset (Fin s))) : satakePairs S :=
  ⟨(Fin.castAdd s p.1.1, Fin.natAdd r p.2.1), (Finset.mem_filter.1 p.1.2).2, by simpa [sub2] using p.2.2, by
    have := p.1.1.2
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega⟩

private theorem bij3 {r s : ℕ} (S : Finset (Fin (r + s))) :
    Function.Bijective (Sum.elim (Sum.elim (pair1 S) (pair2 S)) (pair3 S)) := by
  constructor
  · rintro ((⟨⟨a, b⟩, h⟩ | ⟨⟨a, b⟩, h⟩) | ⟨⟨a, h⟩, ⟨b, h'⟩⟩) ((⟨⟨c, d⟩, k⟩ | ⟨⟨c, d⟩, k⟩) | ⟨⟨c, k⟩, ⟨d, k'⟩⟩) H <;>
      simp only [Sum.elim_inl, Sum.elim_inr, pair1, pair2, pair3, Subtype.mk.injEq, Prod.mk.injEq, Fin.ext_iff,
        Fin.val_castAdd, Fin.val_natAdd, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at H ⊢ <;>
      omega
  · rintro ⟨⟨a, b⟩, h1, h2, h3⟩
    induction a using Fin.addCases with
    | left a =>
      induction b using Fin.addCases with
      | left b =>
        exact ⟨.inl (.inl ⟨(a, b), by simpa [sub1] using h1, by simpa [sub1] using h2, h3⟩), rfl⟩
      | right b =>
        exact ⟨.inr (⟨a, by simpa [sub1] using h1⟩, ⟨b, by simpa [sub2] using h2⟩), rfl⟩
    | right a =>
      induction b using Fin.addCases with
      | left b =>
        exfalso
        simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd] at h3
        omega
      | right b =>
        refine ⟨.inl (.inr ⟨(a, b), by simpa [sub2] using h1, by simpa [sub2] using h2, ?_⟩), rfl⟩
        simp only [Fin.lt_def, Fin.val_natAdd] at h3 ⊢
        omega

theorem UpperTheory.V.Cj.S.sumInner :
    UpperTheory.V.Cj.S.SumInner := by
  intro r s R _ S g
  rw [sum_three (pair1 S) (pair2 S) (pair3 S) (bij3 S) g]
  simp only [Fintype.card_prod, Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SuppAdd
section
namespace UpperTheory.V.Cj.S

theorem suppAdd : SuppAdd := by
  intro E _ _ _ r s k l m₁ m₂ B₁ B₂ h₁ h₂
  obtain ⟨ι, _, n, π, μ, hk, hn, hs, hi, hm, hB⟩ := h₁
  obtain ⟨κ, _, n', π', μ', hk', hn', hs', hi', hm', hB'⟩ := h₂
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim n n', fun i => Sum.rec (fun i => π i) (fun i => π' i) i, Sum.elim μ μ',
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_sum]
    exact Nat.add_le_add hk hk'
  · rintro (i | i)
    · exact hn i
    · exact hn' i
  · rw [Fintype.sum_sum_type, ← hs, ← hs']
    rfl
  · rintro (i | i) t
    · exact hi i t
    · exact hi' i t
  · intro t
    rw [Fintype.sum_sum_type]
    show ∑ i, μ i t + ∑ i, μ' i t = m₁ t + m₂ t
    rw [hm t, hm' t]
  · filter_upwards [hB, hB'] with w hw hw'
    obtain ⟨C, hC, hCs⟩ := hw
    obtain ⟨C', hC', hCs'⟩ := hw'
    refine ⟨Sum.elim C C', ?_, ?_⟩
    · rintro (i | i)
      · exact hC i
      · exact hC' i
    · rw [Fintype.sum_sum_type]
      show ∑ i, C i + ∑ i, C' i = B₁ w + B₂ w
      rw [hCs, hCs']

end UpperTheory.V.Cj.S
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SuppTwist
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem sum_map {ι α : Type} [Fintype ι] (f : α → α) (C : ι → Multiset α) :
    ∑ i, (C i).map f = (∑ i, C i).map f := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Multiset.coe_mapAddMonoidHom, map_sum]

private theorem sat_twist {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (π : CG E a) {w : Pl E}
    {B : Multiset ℂˣ} (h : π.HasSat w B) {χ : HChar E} (hχ : χ.UnrAt w) :
    (π.twist χ).HasSat w (B.map (· * χ.val w)) := by
  induction π using Quotient.inductionOn
  exact GlobalTheory.SphGal.hasSatGL_twist _ _ _ χ w B hχ h

theorem UpperTheory.V.Cj.S.suppTwist :
    UpperTheory.V.Cj.S.SuppTwist := by
  rintro E _ _ _ a k m B ⟨ι, _, n, π, μ, hk, hn, ha, hμ, hm, hB⟩ x ν hν
  refine ⟨ι, inferInstance, n, fun i => (π i).twist ν, fun i t => (μ i t).map (· + (x : ℂ)), hk, hn, ha,
    fun i t => ?_, fun t => ?_, hB.mono ?_⟩
  · have h := (hμ i t).twist ν
    rwa [(InfType.expo_of_infType E ν).2.1 x hν t] at h
  · rw [sum_map, hm]
  · rintro w ⟨C, hC, hs⟩
    exact ⟨fun i => (C i).map (· * ν.val w), fun i => sat_twist _ (hC i) (hν.1 w), by rw [sum_map, hs]⟩
end

