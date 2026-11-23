module

public import Mathlib
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0274
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0027
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AutTranslate
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.MultiCentre
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Classifies
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SpFlag

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdmissibleEquivariantFormsRepresentation
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {S : Type} [AddCommGroup S] [Module ℂ S]

private def eqForms (ρ : Representation ℂ (infU E n) S) : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)) where
  carrier := {f | (∀ v, f v ∈ autU E n) ∧ ∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)}
  add_mem' ha hb := ⟨fun v => add_mem (ha.1 v) (hb.1 v), fun x v => by
    rw [LinearMap.add_apply, LinearMap.add_apply, ha.2, hb.2, map_add (f := _)]⟩
  zero_mem' := ⟨fun _ => zero_mem _, fun _ _ => rfl⟩
  smul_mem' c _ ha := ⟨fun v => Submodule.smul_mem _ c (ha.1 v), fun x v => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, ha.2, map_smul]⟩

private noncomputable def eqRep (ρ : Representation ℂ (infU E n) S) : Representation ℂ (finU (E := E) (n := n)) (eqForms ρ) where
  toFun k := (LinearMap.llcomp ℂ _ _ _ (RU E n k)).restrict (p := eqForms ρ) (q := eqForms ρ) fun f h =>
    ⟨fun v => RU_mem_autU _ _ (h.1 v), fun x v => by
      change RU E n k (f (ρ x v)) = RU E n x (RU E n k (f v))
      rw [h.2, RU_RU, RU_RU, fin_mul_inf k.2 x.2]⟩
  map_one' := LinearMap.ext fun f => Subtype.ext (LinearMap.ext fun v => funext fun g => congrArg (f.1 v) (mul_one g))
  map_mul' a b := LinearMap.ext fun f => Subtype.ext (LinearMap.ext fun v => funext fun g =>
    congrArg (f.1 v) (mul_assoc g a b).symm)

private theorem eqRep_adm [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S) (f : eqForms ρ) :
    ∃ K : Subgroup (finU (E := E) (n := n)), (∀ k ∈ K, eqRep ρ k f = f) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed (eqRep ρ) K) ∧
      ∀ w, (Set.range fun k : K => eqRep ρ k w).Finite :=
  _root_.UpperTheory.Reformulated.B.Gr38.eqRep_adm ρ f

end

theorem UpperTheory.admissible_equivariantForms_representation :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (B : (UA E n → ℂ) →ₗ⋆[ℂ] (UA E n → ℂ) →ₗ[ℂ] ℂ), (∀ φ, IsAutFormU φ → B φ φ = 0 → φ = 0) → (∀ x φ ψ, IsAutFormU φ → IsAutFormU ψ → B (RU E n x φ) (RU E n x ψ) = B φ ψ) → ∀ (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ f : S →ₗ[ℂ] (UA E n → ℂ), (∀ v, IsAutFormU (f v)) → (∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) → ∀ v, f v ∈ ⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1 := by
  intro E _ _ _ n B hdefB hinv S _ _ _ ρ hsp f hfa hfe v
  classical
  by_cases hv : v = 0
  · rw [hv, map_zero]
    exact zero_mem _
  let ev : eqForms ρ →ₗ[ℂ] (UA E n → ℂ) := LinearMap.applyₗ v ∘ₗ (eqForms ρ).subtype
  let B' : eqForms ρ →ₗ⋆[ℂ] eqForms ρ →ₗ[ℂ] ℂ := (B.compl₂ ev).comp ev
  have hB' : ∀ u w, B' u w = B (u.1 v) (w.1 v) := fun _ _ => rfl
  have hev : ∀ u : eqForms ρ, u.1 v = 0 → u = 0 := fun u hu => by
    have h1 : ∀ T ∈ Submodule.span ℂ (Set.range ρ), u.1 (T v) = 0 := by
      intro T hT
      induction hT using Submodule.span_induction with
      | mem T hT =>
        obtain ⟨x, rfl⟩ := hT
        rw [u.2.2, hu, map_zero]
      | zero => simp
      | add a b _ _ ha hb => rw [LinearMap.add_apply, map_add (f := _), ha, hb, add_zero]
      | smul c a _ ha => rw [LinearMap.smul_apply, map_smul, ha, smul_zero]
    obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hv
    refine Subtype.ext (LinearMap.ext fun w => ?_)
    have h2 := h1 (LinearMap.smulRight l w) (hsp ▸ Submodule.mem_top)
    rw [LinearMap.smulRight_apply, hl, one_smul] at h2
    exact h2
  have hdef : ∀ u, B' u u = 0 → u = 0 := fun u hu => hev u (hdefB _ (u.2.1 v) hu)
  have hinv' : ∀ g u w, B' (eqRep ρ g u) (eqRep ρ g w) = B' u w := fun g u w =>
    hinv g _ _ (u.2.1 _) (w.2.1 _)
  have hmem := UpperTheory.mem_iSup_irreducible_of_admissible_unitary (finU (E := E) (n := n)) (eqForms ρ) (eqRep ρ) B' hdef hinv' (eqRep_adm ρ) ⟨f, hfa, hfe⟩
  refine (iSup_le ?_ : _ ≤ (⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1).comap ev) hmem
  rintro ⟨U, hU0, hU, hirr⟩
  let j : U →ₗ[ℂ] S →ₗ[ℂ] (UA E n → ℂ) := (eqForms ρ).subtype ∘ₗ U.subtype
  have hj : ∀ (p : U) (x : infU E n) v, j p (ρ x v) = RU E n x.1 (j p v) := fun p x v => p.1.2.2 x v
  have hrep : IsAutRepU (Pairs.img j) := by
    refine ⟨fun φ hφ => ?_, fun x φ hφ => ?_, fun h => hU0 ?_, fun N hle hN => ?_⟩
    · have h1 : Pairs.img j ≤ autU E n := Submodule.span_le.2 (by
        rintro _ ⟨p, v, rfl⟩
        exact p.1.2.1 v)
      exact h1 hφ
    · refine Pairs.stable_of (fun a => ?_) (fun k => ?_) x φ hφ
      · have h1 : Pairs.img j ≤ (Pairs.img j).comap (RU E n a.1) := Submodule.span_le.2 (by
          rintro _ ⟨p, v, rfl⟩
          change RU E n a.1 _ ∈ Pairs.img j
          rw [← hj]
          exact Pairs.apply_mem_img _ _ _)
        exact fun φ hφ => h1 hφ
      · have h1 : Pairs.img j ≤ (Pairs.img j).comap (RU E n k.1) := Submodule.span_le.2 (by
          rintro _ ⟨p, v, rfl⟩
          exact Pairs.apply_mem_img j ⟨eqRep ρ k p.1, hU k _ p.2⟩ v)
        exact fun φ hφ => h1 hφ
    · rw [Submodule.eq_bot_iff]
      intro u hu
      have := Pairs.apply_mem_img j ⟨u, hu⟩ v
      rw [h, Submodule.mem_bot] at this
      exact hev u this
    · refine Pairs.eq_bot_or_eq_img hsp (R := fun x => RU E n x.1) hj
        (Q := fun k : finU (E := E) (n := n) => (eqRep ρ k).restrict (hU k)) (T := fun k => RU E n k.1) (fun _ _ _ => rfl)
        (fun P hP => ?_) hle (fun x => hN x.1) (fun k => hN k.1)
      rcases hirr (P.map U.subtype) (Submodule.map_subtype_le U P) (by
        rintro g _ ⟨p, hp, rfl⟩
        exact ⟨_, hP g p hp, rfl⟩) with h | h
      · left
        exact Submodule.map_injective_of_injective U.injective_subtype (h.trans (Submodule.map_bot _).symm)
      · right
        exact Submodule.map_injective_of_injective U.injective_subtype (h.trans (Submodule.map_subtype_top _).symm)
  intro u hu
  exact le_iSup (fun σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ} => σ.1) ⟨_, hrep⟩
    (Pairs.apply_mem_img j ⟨u, hu⟩ v)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CenterUActionMemAdjoinCapOp
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.centerU_action_mem_adjoin_capOp :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type) [Fintype ι] (D : Idem (mixedSpace K) ι), ∀ z ∈ (isExpLieAlgebra K n).centerU, uAction z ∈ Algebra.adjoin ℂ {x | ∃ τ u, x = capOp D n τ u} := by
  intro K _ _ n ι _ D z hz
  obtain ⟨hrel, hcomm⟩ := UpperTheory.gen_glRelations_and_commute_of_isLie (mixedSpace K) ι n _ D (lam K n) (isLie_lam K n)
  have h1 : ∀ u : UEnv K n,
      uAction u ∈ Algebra.adjoin ℂ {x | ∃ τ i j, x = gen D (lam K n) τ i j} := by
    intro u
    induction u using UEnv.induction with
    | halg r =>
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply ℝ ℂ]
      exact Subalgebra.algebraMap_mem _ _
    | hι Y =>
      obtain ⟨X, rfl⟩ := (toLie K n).surjective Y
      rw [← lam_apply, UpperTheory.lieMap_eq_sum_idempotent_gen (mixedSpace K) ι n _ D (lam K n) X]
      exact sum_mem fun τ _ => sum_mem fun i _ => sum_mem fun j _ =>
        Subalgebra.smul_mem _ (Algebra.subset_adjoin (by exact ⟨τ, i, j, rfl⟩)) _
    | hmul x y hx hy => rw [map_mul]; exact mul_mem hx hy
    | hadd x y hx hy => rw [map_add]; exact add_mem hx hy
  refine UpperTheory.V.Fb.multiCentre (gen D (lam K n)) hrel hcomm (h1 z) fun τ i j => ?_
  have h2 := gen_mem D (lam K n) τ i j
    (Subalgebra.toSubmodule (Subalgebra.centralizer ℂ {uAction z})) fun x => by
      rintro _ rfl
      rw [lam_apply, ← map_mul, ← map_mul, Subalgebra.mem_center_iff.1 hz]
  exact (h2 _ rfl).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusTraceNormNonzeroLogBound
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.frobenius_trace_norm_nonzero_log_bound :
    ∀ (q e : ℕ), 7 ≤ q → 1 ≤ e → ∀ (D : TrData q e) (Orb : Type) [Fintype Orb] (z : Orb → ℂ), (∀ o, ∃ k : ℕ, 0 < k ∧ z o ^ k = 1) → (∀ σ : ℂ ≃+* ℂ, ∃ u : Orb ≃ Orb, ∀ o, z (u o) = σ (z o)) → ∃ NN : ℤ, NN ≠ 0 ∧ Real.log |(NN : ℝ)| ≤ Fintype.card Orb * Nat.card D.S * (2 * e * Real.log q + 1) ∧ ∀ (l : ℕ) [Fact l.Prime], ¬ l ∣ q → ∀ (ι : Qbar l ≃+* ℂ) (Γ : Type) [Group Γ] (g : Γ) (admitted : (Γ →* GL (Fin 3) (Qbar l)) → Prop), D.Classifies ι g admitted → ∀ X : Orb → Finset (Γ →* GL (Fin 3) (Qbar l)), (∀ o, ∀ ρ ∈ X o, admitted ρ) → (∀ o, ∀ ρ ∈ X o, ∀ ρ' ∈ X o, RepIso ρ ρ' → ρ = ρ') → (∀ o, ∀ ρ ∈ X o, (ρ g : Matrix (Fin 3) (Fin 3) (Qbar l)).trace ≠ ι.symm (eis3 q e (z o))) ∧ ‖((NN : ℤ) : Qbar l)‖ ≤ ∏ o, ∏ ρ ∈ X o, ‖(ρ g : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - ι.symm (eis3 q e (z o))‖ := by
  intro q e hq he D Orb _ z hz hσ
  classical
  have := D.fin
  letI : Fintype D.S := Fintype.ofFinite D.S
  let f : Orb → D.S → ℂ := fun o s => (q : ℂ) ^ e * (D.t s - eis3 q e (z o))
  have key : ∀ o s, D.t s ≠ eis3 q e (z o) ∧ IsIntegral ℤ (f o s) ∧
      Real.log ‖f o s‖ ≤ 2 * e * Real.log q + 1 := by
    intro o s
    obtain ⟨k, hk, hzk⟩ := hz o
    exact UpperTheory.eisenstein_trace_difference_log_bound q e k hq he hk (z o) (D.t s) hzk (D.bd s) (D.int s)
  have hq0 : (q : ℂ) ≠ 0 := by
    have : q ≠ 0 := by omega
    exact_mod_cast this
  have hf0 : ∀ o s, f o s ≠ 0 := fun o s =>
    mul_ne_zero (pow_ne_zero _ hq0) (sub_ne_zero.2 (key o s).1)
  obtain ⟨n, hn⟩ := UpperTheory.exists_int_eq_prod_of_galois_permuted_integral (Orb × D.S) (fun p => f p.1 p.2) (fun p => (key p.1 p.2).2.1) (by
    intro σ
    obtain ⟨u, hu⟩ := hσ σ
    obtain ⟨v, hv⟩ := D.conj σ
    refine ⟨u.prodCongr v, fun p => ?_⟩
    simp [f, eis3, hu, hv])
  refine ⟨n, ?_, ?_, ?_⟩
  · intro h
    rw [h, Int.cast_zero] at hn
    exact Finset.prod_ne_zero_iff.2 (fun p _ => hf0 p.1 p.2) hn.symm
  · have h1 : |(n : ℝ)| = ∏ p : Orb × D.S, ‖f p.1 p.2‖ := by
      rw [← norm_prod, ← hn, Complex.norm_intCast]
    rw [h1, Real.log_prod (fun p _ => norm_ne_zero_iff.2 (hf0 p.1 p.2))]
    refine (Finset.sum_le_sum (fun p _ => (key p.1 p.2).2.2)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Nat.card_eq_fintype_card, nsmul_eq_mul]
    push_cast
    exact le_rfl
  · intro l _ hl ι Γ _ g admitted hcl X hX hinj
    obtain ⟨cl, hc1, hc2⟩ := hcl
    refine ⟨fun o ρ hρ h => ?_, ?_⟩
    · rw [hc2 ⟨ρ, hX o ρ hρ⟩] at h
      exact (key o _).1 (ι.symm.injective h)
    · have hq1 : ‖(q : Qbar l)‖ = 1 := by
        rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
        exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hl
      have h2 := UpperTheory.adicNorm_prod_le_prod_of_injective_classes l ι Orb D.S _ f (fun o s => (key o s).2.1) X
        (fun o r => cl ⟨r.1, hX o r.1 r.2⟩)
        (fun o r r' h => Subtype.ext (hinj o _ r.2 _ r'.2 (hc1 _ _ h)))
      rw [← Fintype.prod_prod_type', ← hn, map_intCast] at h2
      refine h2.trans (le_of_eq (Finset.prod_congr rfl fun o _ => ?_))
      rw [← Finset.prod_coe_sort (X o)]
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [hc2 ⟨r.1, hX o r.1 r.2⟩]
      simp only [f, map_mul, map_pow, map_natCast, map_sub, norm_mul, norm_pow, hq1, one_pow, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PseudoDeformationDiagCharactersMulRevEqSimilitud
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem adj_tri {R : Type} [CommRing R] {A : M4 R} (h : IsUp A) : (adj A).BlockTriangular id := by
  intro i j hij
  rw [adj_apply, h j.rev i.rev (Fin.rev_lt_rev.2 hij), smul_zero]

private theorem adj_dg {R : Type} [CommRing R] (A : M4 R) (i : Fin 4) : adj A i i = A i.rev i.rev := by
  rw [adj_apply]
  fin_cases i <;> simp [sgn]

theorem UpperTheory.pseudoDeformation_diag_characters_mul_rev_eq_similitude :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) {R : Type} [CommRing R] (a : O →+* R) (P : PD Φ.ι Γ R), Φ.IsPair a P → ∀ (v : Φ.ι) (i : Fin 4), P.ψ v i 1 = 1 ∧ (∀ s ∈ Φ.Gv v, ∀ t ∈ Φ.Gv v, P.ψ v i (s * t) = P.ψ v i s * P.ψ v i t) ∧ ∀ s ∈ Φ.Gv v, P.ψ v i s * P.ψ v i.rev s = a (Φ.ν s) := by
  intro O Γ _ _ Φ R _ a P hP v i
  have hn : adj (P.n v) * P.n v = 1 := by
    have h := (hP.low v).1
    unfold IsGSp at h
    simpa using h
  have hn' : P.n v * adj (P.n v) = 1 := mul_eq_one_comm.mp hn
  refine ⟨?_, ?_, ?_⟩
  · simp [PD.ψ, hn]
  · intro s hs t ht
    have e : adj (P.n v) * P.r (s * t) * P.n v =
        (adj (P.n v) * P.r s * P.n v) * (adj (P.n v) * P.r t * P.n v) := by
      rw [map_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (P.n v) (adj (P.n v)), hn', Matrix.one_mul]
    unfold PD.ψ
    rw [e]
    exact UpperTheory.V.Loc.SpFlag.tri_mul_diag (fun p q h => hP.flag v s hs p q h) (fun p q h => hP.flag v t ht p q h) i
  · intro s hs
    have hB := hP.flag v s hs
    have hg := hP.mult s
    unfold IsGSp at hg
    have e : adj (adj (P.n v) * P.r s * P.n v) * (adj (P.n v) * P.r s * P.n v) = a (Φ.ν s) • 1 := by
      rw [UpperTheory.V.Loc.SpFlag.adj_mul, UpperTheory.V.Loc.SpFlag.adj_mul, UpperTheory.V.Loc.SpFlag.adj_adj]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (P.n v) (adj (P.n v)), hn', Matrix.one_mul, ← Matrix.mul_assoc (adj (P.r s)), hg]
      simp [hn]
    have d := UpperTheory.V.Loc.SpFlag.tri_mul_diag (adj_tri hB) (fun p q h => hB p q h) i
    rw [e, adj_dg] at d
    unfold PD.ψ
    rw [mul_comm, ← d]
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.QdetGeneratesUniversalEnvelopingCentre
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem qdet_mem' {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (S : Subalgebra ℂ A) (X : Fin n → Fin n → A)
    (h : ∀ a b, X a b ∈ S) (u : ℂ) : Formalism.REAL.qdet X u ∈ S := by
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (h _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

private theorem aux {R : Type} [CommRing R] [Algebra ℝ R] {ι : Type} [Fintype ι] {n : ℕ} {A : Type} [Ring A]
    [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] {B : Type} [Ring B] [Algebra ℝ B] (D : Idem R ι)
    (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] B) (hl : ∀ X Y, l X * l Y - l Y * l X = l (X * Y - Y * X))
    (htop : Algebra.adjoin ℝ (Set.range l) = ⊤) (ρ : B →ₐ[ℝ] A) (τ : ι) (u : ℂ) :
    Formalism.REAL.qdet (gen D (ρ.toLinearMap ∘ₗ l) τ) u ∈
      Submodule.span ℂ (ρ '' (Subalgebra.center ℝ B : Set B)) := by
  let j : B →ₐ[ℝ] ℂ ⊗[ℝ] B := Algebra.TensorProduct.includeRight
  let ψ : ℂ ⊗[ℝ] B →ₐ[ℂ] A := Algebra.TensorProduct.lift (Algebra.ofId ℂ A) ρ fun c x => Algebra.commutes c (ρ x)
  have hψ : ∀ c x, ψ (c ⊗ₜ x) = c • ρ x := fun c x =>
    (Algebra.TensorProduct.lift_tmul _ _ _ c x).trans (Algebra.smul_def c (ρ x)).symm
  let l' : Matrix (Fin n) (Fin n) R →ₗ[ℝ] ℂ ⊗[ℝ] B := j.toLinearMap ∘ₗ l
  have hl' : IsLie l' := fun X Y => by
    change j (l X) * j (l Y) - j (l Y) * j (l X) = j (l (X * Y - Y * X))
    rw [← hl, map_sub, map_mul, map_mul]
  obtain ⟨hrel, hc⟩ := UpperTheory.gen_glRelations_and_commute_of_isLie R ι n _ D l' hl'
  set w := Formalism.REAL.qdet (gen D l' τ) u with hw
  have h0 : ∀ σ a b, gen D l' σ a b ∈ Subalgebra.centralizer ℂ {w} := fun σ a b => by
    rintro _ rfl
    by_cases e : σ = τ
    · subst e
      exact (Formalism.REAL.qDetCentral _ n _ (hrel σ) u a b)
    · refine (qdet_mem' (Subalgebra.centralizer ℂ {gen D l' σ a b}) _ (fun c d => ?_) u _ rfl).symm
      rintro _ rfl
      exact hc σ τ e a b c d
  have h1 : ∀ x : B, j x * w = w * j x := fun x => by
    have : Algebra.adjoin ℝ (Set.range l) ≤ (Subalgebra.centralizer ℝ {w}).comap j := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨X, rfl⟩
      have h2 : l' X ∈ Subalgebra.centralizer ℂ {w} := by
        rw [UpperTheory.lieMap_eq_sum_idempotent_gen R ι n _ D l' X]
        exact sum_mem fun σ _ => sum_mem fun a _ => sum_mem fun b _ => Subalgebra.smul_mem _ (h0 σ a b) _
      exact h2
    exact (this (htop ▸ Algebra.mem_top) w rfl).symm
  obtain ⟨p, hp, q, hq, e⟩ := UpperTheory.V.Fb.exists_re_im w h1
  have h2 : ψ w = Formalism.REAL.qdet (gen D (ρ.toLinearMap ∘ₗ l) τ) u := by
    rw [hw, UpperTheory.V.Fb.map_qdet]
    congr 1
    funext a b
    exact gen_inter D l' (ρ.toLinearMap ∘ₗ l) τ a b a b ψ.toLinearMap LinearMap.id fun x =>
      (hψ 1 _).trans (one_smul _ _)
  rw [← h2, e, map_add (f := _), hψ, hψ]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, hp, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, hq, rfl⟩))

theorem UpperTheory.qdet_generates_universalEnveloping_centre :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type) [Fintype ι] (D : Idem (mixedSpace K) ι) (τ : ι) (u : ℂ), capOp D n τ u ∈ Zc K n := by
  intro K _ _ n ι _ D τ u
  let l : Matrix (Fin n) (Fin n) (mixedSpace K) →ₗ[ℝ] UEnv K n :=
    (UniversalEnvelopingAlgebra.ι ℝ (L := (isExpLieAlgebra K n).lieSubalgebra)).toLinearMap ∘ₗ (toLie K n).toLinearMap
  have hl : ∀ X Y, l X * l Y - l Y * l X = l (X * Y - Y * X) := fun X Y => by
    change UniversalEnvelopingAlgebra.ι ℝ (toLie K n X) * UniversalEnvelopingAlgebra.ι ℝ (toLie K n Y) -
      UniversalEnvelopingAlgebra.ι ℝ (toLie K n Y) * UniversalEnvelopingAlgebra.ι ℝ (toLie K n X) =
      UniversalEnvelopingAlgebra.ι ℝ (toLie K n (X * Y - Y * X))
    rw [← Ring.lie_def, ← LieHom.map_lie]
    rfl
  have htop : Algebra.adjoin ℝ (Set.range l) = ⊤ := by
    refine eq_top_iff.2 fun z hz => ?_
    clear hz
    induction z using UEnv.induction with
    | halg r => exact Subalgebra.algebraMap_mem _ r
    | hι X => exact Algebra.subset_adjoin ⟨(toLie K n).symm X, by simp [l]⟩
    | hmul a b ha hb => exact mul_mem ha hb
    | hadd a b ha hb => exact add_mem ha hb
  have h := aux D l hl htop (uAction (K := K) (n := n)) τ u
  exact Algebra.span_le_adjoin ℂ _ h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TracesFromEigenvaluesRank2
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.traces_from_eigenvalues_rank2 :
    ∀ (p h e : ℕ), ∀ D : EigData 2 p ![(e : ℤ), -(e : ℤ)] 0, ∃ (T : TrData (p ^ h) e) (u : D.S ≃ T.S), ∀ s, T.t (u s) = 1 + ((D.β s).map fun b => b⁻¹ ^ h).sum := by
  intro p h e D
  refine ⟨⟨D.S, D.fin, fun s => 1 + ((D.β s).map fun b => b⁻¹ ^ h).sum, ?_, ?_, ?_⟩, Equiv.refl _, fun s => rfl⟩
  · intro σ
    obtain ⟨u, hu⟩ := D.conj σ
    refine ⟨u, fun s => ?_⟩
    rw [hu, map_add (f := _), map_one, map_multiset_sum, Multiset.map_map, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp, map_pow, map_inv₀]
  · intro s
    obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.1 (D.card s)
    have hx : ‖x‖ = 1 := by simpa using D.pure s x (by rw [hxy]; simp)
    have hy : ‖y‖ = 1 := by simpa using D.pure s y (by rw [hxy]; simp)
    have e1 : ((D.β s).map fun b => b⁻¹ ^ h).sum = x⁻¹ ^ h + y⁻¹ ^ h := by
      rw [hxy]; simp
    have h1 : ‖x⁻¹ ^ h‖ = 1 := by simp [hx]
    have h2 : ‖y⁻¹ ^ h‖ = 1 := by simp [hy]
    rw [e1]
    have h3 := norm_add_le (1 : ℂ) (x⁻¹ ^ h + y⁻¹ ^ h)
    have h4 := norm_add_le (x⁻¹ ^ h) (y⁻¹ ^ h)
    rw [norm_one] at h3
    linarith
  · intro s
    obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.1 (D.card s)
    have hm : ∀ i, (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i ≤ (e : ℤ) := by
      intro i
      fin_cases i
      · simp
      · simp
    have hx := D.intInv e hm s x (by rw [hxy]; simp)
    have hy := D.intInv e hm s y (by rw [hxy]; simp)
    rw [zpow_natCast] at hx hy
    have e1 : ((D.β s).map fun b => b⁻¹ ^ h).sum = x⁻¹ ^ h + y⁻¹ ^ h := by
      rw [hxy]; simp
    have e2 : (((p ^ h : ℕ) : ℂ)) ^ e * (1 + (x⁻¹ ^ h + y⁻¹ ^ h)) =
        ((p ^ (h * e) : ℕ) : ℂ) + (((p : ℂ) ^ e * x⁻¹) ^ h + ((p : ℂ) ^ e * y⁻¹) ^ h) := by
      push_cast; ring
    rw [e1, e2]
    refine IsIntegral.add ?_ ((hx.pow h).add (hy.pow h))
    exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ((p ^ (h * e) : ℕ) : ℤ)))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TracesFromEigenvaluesRank3
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.traces_from_eigenvalues_rank3 :
    ∀ (q e : ℕ), 1 ≤ q → ∀ D : EigData 3 q ![(e : ℤ) - 1, -1, -(e : ℤ) - 1] (1 - ((3 : ℕ) : ℤ)), ∃ (T : TrData q e) (u : D.S ≃ T.S), ∀ s, T.t (u s) = ((D.β s).map fun b => ((q : ℂ) * b)⁻¹).sum := by
  intro q e hq D
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hqR.ne'
  refine ⟨⟨D.S, D.fin, fun s => ((D.β s).map fun b => ((q : ℂ) * b)⁻¹).sum, ?_, ?_, ?_⟩, Equiv.refl _, fun s => rfl⟩
  · intro σ
    obtain ⟨u, hu⟩ := D.conj σ
    refine ⟨u, fun s => ?_⟩
    rw [hu, map_multiset_sum, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun b _ => ?_
    simp
  · intro s
    refine (norm_multiset_sum_le _).trans ?_
    have h := Multiset.sum_le_card_nsmul (((D.β s).map fun b => ((q : ℂ) * b)⁻¹).map fun x => ‖x‖) (1 : ℝ) (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hy
      have hp := D.pure s b hb
      have he : (((1 - ((3 : ℕ) : ℤ) : ℤ) : ℝ) / 2) = -1 := by push_cast; norm_num
      rw [he, Real.rpow_neg_one] at hp
      rw [norm_inv, norm_mul, hp, Complex.norm_natCast, mul_inv_cancel₀ hqR.ne', inv_one])
    rw [Multiset.card_map, Multiset.card_map, D.card] at h
    simpa using h
  · intro s
    rw [← Multiset.sum_map_mul_left]
    refine (integralClosure ℤ ℂ).multiset_sum_mem ?_
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hx
    have h := D.intInv ((e : ℤ) - 1) (by
      intro i
      fin_cases i <;> simp <;> omega) s b hb
    have he : (q : ℂ) ^ e * ((q : ℂ) * b)⁻¹ = (q : ℂ) ^ ((e : ℤ) - 1) * b⁻¹ := by
      rw [zpow_sub_one₀ hqC, zpow_natCast, mul_inv, mul_assoc]
    rw [mem_integralClosure_iff, he]
    exact h
end

