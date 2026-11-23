module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRingFreeOverFrobeniusImage
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffTensorAcrisWithFrobeniusGalois
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0299
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0301

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeRestrictScalarsTraceForm
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.DualLatDescent

theorem dualLat_resQ : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [Module O V] [IsScalarTower O LL V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    [Module O V'] [IsScalarTower O LL V'] [Module ℤ_[l] V'] [IsScalarTower ℤ_[l] ℚ_[l] V']
    [FiniteDimensional ℚ_[l] LL] [FiniteDimensional LL V] [FiniteDimensional LL V']
    (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
    (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) →
    (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) →
    (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) →
    ∀ (ρ : Representation LL ↥(GK K) V) (ρ' : Representation LL ↥(GK K) V')
    (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ')
    (LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ)) (LZ' : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ')),
    (∀ v, v ∈ LZ.T ↔ v ∈ L.T) → (∀ v, v ∈ LZ'.T ↔ v ∈ L'.T) →
    ∀ (Pr : V →ₗ[LL] V' →ₗ[LL] LL) (PQ : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]),
    (∀ x y, PQ x y = lam (Pr x y)) → IsDualLat1 (P.PD K) L L' Pr →
    IsDualLat1 (P.PD K) LZ LZ' PQ := by
  intro l _ P K LL _ _ O _ _ V _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ _ _ lam n e f h1 h2 h3 ρ ρ' L L' LZ LZ' hT hT' Pr PQ hPQ hP
  obtain ⟨⟨hg, hl, hr, hrk⟩, hlat⟩ := hP

  have key : ∀ z : LL, (∀ a : LL, lam (a * z) = 0) → z = 0 := by
    intro z hz
    rw [h3 z]
    simp [hz]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro g x y
    rw [hPQ, GlobalTheory.PstCoeff.resQ_apply, GlobalTheory.PstCoeff.resQ_apply, hg, hPQ]
    have : ((cycLL (P.PD K) LL g : LLˣ) : LL) = algebraMap ℚ_[l] LL ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) := by
      simp [cycLL]
    rw [this, ← Algebra.smul_def, map_smul, smul_eq_mul]
  · intro x hx
    apply hl
    intro y
    apply key
    intro a
    rw [← smul_eq_mul, ← map_smul, ← hPQ]
    exact hx _
  · intro y hy
    apply hr
    intro x
    apply key
    intro a
    rw [← smul_eq_mul, ← LinearMap.smul_apply, ← map_smul, ← hPQ]
    exact hy _
  · rw [← Module.finrank_mul_finrank ℚ_[l] LL V, ← Module.finrank_mul_finrank ℚ_[l] LL V', hrk]
  · intro y
    rw [hT', hlat]
    constructor
    · intro H x hx
      obtain ⟨a, ha⟩ := H x ((hT x).1 hx)
      obtain ⟨z, hz⟩ := h2 a
      exact ⟨z, by rw [hPQ, ha, hz]; rfl⟩
    · intro H x hx
      have hi : ∀ i, ∃ z : ℤ_[l], lam (algebraMap O LL (f i) * Pr x y) = (z : ℚ_[l]) := by
        intro i
        have hm : f i • x ∈ L.T := L.T.smul_mem _ hx
        obtain ⟨z, hz⟩ := H _ ((hT _).2 hm)
        refine ⟨z, ?_⟩
        rw [hPQ, ← algebraMap_smul LL (f i) x, map_smul, LinearMap.smul_apply, smul_eq_mul] at hz
        rw [hz]; rfl
      choose z hz using hi
      have ho : ∀ i, ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z i : ℚ_[l]) := fun i => h1 (z i)
      choose o ho using ho
      refine ⟨∑ i, o i * e i, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h3 (Pr x y), map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hz i, map_mul, ho i, Algebra.smul_def]

end GlobalTheory.DualLatDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfComm
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.ResComm

theorem comm_span {Λ M C : Type} [CommRing Λ] [AddCommGroup M] [Module Λ M] [AddCommGroup C] (S : Set (Module.End Λ M))
    (φ : M →+ C) (h : ∀ A ∈ S, ∀ B ∈ S, ∀ m, φ (A (B m)) = φ (B (A m))) :
    ∀ A ∈ Submodule.span Λ S, ∀ B ∈ Submodule.span Λ S, ∀ m, φ (A (B m)) = φ (B (A m)) := by

  have key : ∀ A ∈ S, ∀ B ∈ Submodule.span Λ S, ∀ m, φ (A (B m)) = φ (B (A m)) := by
    intro A hA B hB
    induction hB using Submodule.span_induction with
    | mem B hB => exact h A hA B hB
    | zero => intro m; simp
    | add B₁ B₂ _ _ h₁ h₂ => intro m; simp [h₁, h₂]
    | smul c B _ hB' =>
      intro m
      simp only [LinearMap.smul_apply, ← map_smul]
      exact hB' (c • m)
  intro A hA B hB
  induction hA using Submodule.span_induction with
  | mem A hA => exact key A hA B hB
  | zero => intro m; simp
  | add A₁ A₂ _ _ h₁ h₂ => intro m; simp [h₁, h₂]
  | smul c A _ hA' =>
    intro m
    simp only [LinearMap.smul_apply, ← map_smul]
    exact hA' (c • m)

theorem act_add {O Λ K : Type} [CommRing O] [CommRing Λ] [Algebra O Λ] [AddCommGroup K] [Module Λ K] {r : ℕ}
    (P Q : Matrix (Fin r) (Fin r) O) :
    matAct (M := K) ((P + Q).map (algebraMap O Λ)) =
      matAct (P.map (algebraMap O Λ)) + matAct (Q.map (algebraMap O Λ)) := by
  refine LinearMap.ext fun v => funext fun i => ?_
  simp [matAct, add_smul, Finset.sum_add_distrib]

theorem act_smul {O Λ K : Type} [CommRing O] [CommRing Λ] [Algebra O Λ] [AddCommGroup K] [Module Λ K] {r : ℕ}
    (c : O) (P : Matrix (Fin r) (Fin r) O) :
    matAct (M := K) ((c • P).map (algebraMap O Λ)) = algebraMap O Λ c • matAct (P.map (algebraMap O Λ)) := by
  refine LinearMap.ext fun v => funext fun i => ?_
  simp [matAct, mul_smul, Finset.smul_sum]

theorem act_congr {O Λ K : Type} [CommRing O] [IsLocalRing O] [CommRing Λ] [IsLocalRing Λ] [Algebra O Λ]
    [IsLocalHom (algebraMap O Λ)] [AddCommGroup K] [Module Λ K] {r : ℕ}
    (hm : ∀ x ∈ IsLocalRing.maximalIdeal Λ, ∀ k : K, x • k = 0) (P Q : Matrix (Fin r) (Fin r) O)
    (h : P.map (IsLocalRing.residue O) = Q.map (IsLocalRing.residue O)) :
    matAct (M := K) (P.map (algebraMap O Λ)) = matAct (Q.map (algebraMap O Λ)) := by
  refine LinearMap.ext fun v => funext fun i => ?_
  simp only [matAct, LinearMap.coe_mk, AddHom.coe_mk, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_

  have hPQ : P i j - Q i j ∈ IsLocalRing.maximalIdeal O := by
    have e := congrFun (congrFun h i) j
    simp only [Matrix.map_apply] at e
    exact Ideal.Quotient.eq.mp e
  have hΛ : algebraMap O Λ (P i j - Q i j) ∈ IsLocalRing.maximalIdeal Λ :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr fun hu =>
      mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hPQ) (isUnit_of_map_unit (algebraMap O Λ) _ hu))
  have e := hm _ hΛ (v j)
  rwa [map_sub, sub_smul, sub_eq_zero] at e

private theorem matAct_single {O Λ K : Type} [CommRing O] [CommRing Λ] [Algebra O Λ] [AddCommGroup K] [Module Λ K] {r : ℕ}
    (a b : Fin r) (v : Fin r → K) :
    matAct (M := K) ((Matrix.of fun i j => if i = a ∧ j = b then (1 : O) else 0).map (algebraMap O Λ)) v =
      Pi.single a (v b) := by
  funext i
  simp only [matAct, LinearMap.coe_mk, AddHom.coe_mk, Matrix.map_apply, Matrix.of_apply]
  by_cases hi : i = a
  · subst hi
    simp [apply_ite (algebraMap O Λ), ite_smul]
  · simp [hi]

private theorem matAct_of_span_residue_spans {Γ O Λ K : Type} [Group Γ] [CommRing O] [IsLocalRing O] [CommRing Λ] [IsLocalRing Λ]
    [Algebra O Λ] [IsLocalHom (algebraMap O Λ)] [AddCommGroup K] [Module Λ K] {r : ℕ} (ρ : Γ →* GL (Fin r) O)
    (hm : ∀ x ∈ IsLocalRing.maximalIdeal Λ, ∀ k : K, x • k = 0)
    (hsp : Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g =>
      ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) = ⊤)
    (P : Matrix (Fin r) (Fin r) O) :
    matAct (M := K) (P.map (algebraMap O Λ)) ∈ Submodule.span Λ (Set.range fun g =>
      matAct (M := K) (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (algebraMap O Λ))) := by

  have lift : ∀ X : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O),
      ∃ P' : Matrix (Fin r) (Fin r) O, P'.map (IsLocalRing.residue O) = X := fun X =>
    ⟨X.map (Function.surjInv IsLocalRing.residue_surjective), by
      ext i j; simp [Function.surjInv_eq IsLocalRing.residue_surjective]⟩

  suffices H : ∀ X ∈ Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g =>
      ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)),
      ∀ P : Matrix (Fin r) (Fin r) O, P.map (IsLocalRing.residue O) = X →
        matAct (M := K) (P.map (algebraMap O Λ)) ∈ Submodule.span Λ (Set.range fun g =>
          matAct (M := K) (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (algebraMap O Λ))) by
    exact H _ (by rw [hsp]; exact Submodule.mem_top) P rfl
  intro X hX
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨g, rfl⟩ := hX
    intro P hP
    rw [act_congr (K := K) hm P _ hP]
    exact Submodule.subset_span ⟨g, rfl⟩
  | zero =>
    intro P hP
    have hP0 : P.map (IsLocalRing.residue O) = (0 : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O) := by
      rw [hP]; ext i j; simp
    rw [act_congr (K := K) hm P 0 hP0]
    have h0 : matAct (M := K) ((0 : Matrix (Fin r) (Fin r) O).map (algebraMap O Λ)) = 0 := by
      refine LinearMap.ext fun v => funext fun i => ?_
      simp [matAct]
    rw [h0]
    exact Submodule.zero_mem _
  | add X Y _ _ hX hY =>
    intro P hP
    obtain ⟨P₁, hP₁⟩ := lift X
    have hP₂ : (P - P₁).map (IsLocalRing.residue O) = Y := by
      have e : (P - P₁).map (IsLocalRing.residue O) =
          P.map (IsLocalRing.residue O) - P₁.map (IsLocalRing.residue O) := by
        ext i j; simp
      rw [e, hP, hP₁, add_sub_cancel_left]
    have e : P = P₁ + (P - P₁) := by abel
    rw [e, act_add]
    exact Submodule.add_mem _ (hX P₁ hP₁) (hY _ hP₂)
  | smul c X _ hX =>
    intro P hP
    obtain ⟨P₁, hP₁⟩ := lift X
    obtain ⟨c₀, rfl⟩ := IsLocalRing.residue_surjective c
    have h' : P.map (IsLocalRing.residue O) = (c₀ • P₁).map (IsLocalRing.residue O) := by
      rw [hP, ← hP₁]; ext i j; simp
    rw [act_congr (K := K) hm P _ h', act_smul]
    exact Submodule.smul_mem _ _ (hX P₁ hP₁)

private theorem matAct_rep {Γ O Λ K : Type} [Group Γ] [CommRing O] [CommRing Λ] [Algebra O Λ] [AddCommGroup K]
    [Module Λ K] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (χ : Γ →* Oˣ) (κ : Γ →* Λˣ) (g : Γ) (m : Fin r → K) :
    repOn (twGL ρ χ) κ K g m = ((κ g : Λ) * algebraMap O Λ (((χ g)⁻¹ : Oˣ) : O)) •
      matAct (M := K) (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (algebraMap O Λ)) m := by
  have e : (((twGL ρ χ) g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) =
      (((χ g)⁻¹ : Oˣ) : O) • ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) := by
    simp [twGL, scalGL, Matrix.smul_eq_diagonal_mul]
  show ((κ g : Λ) • matAct (M := K) ((((twGL ρ χ) g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map
    (algebraMap O Λ))) m = _
  rw [e, act_smul, smul_smul]
  rfl

theorem eq_zero_of_comm : ∀ (Γ O Λ K C : Type) [Group Γ] [CommRing O] [IsLocalRing O] [CommRing Λ] [IsLocalRing Λ] [Algebra O Λ] [IsLocalHom (algebraMap O Λ)] [AddCommGroup K] [Module Λ K] [AddCommGroup C] (r : ℕ) (ρ : Γ →* GL (Fin r) O) (χ : Γ →* Oˣ) (κ : Γ →* Λˣ), 2 ≤ r → (∀ x ∈ IsLocalRing.maximalIdeal Λ, ∀ k : K, x • k = 0) → Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g => ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) = ⊤ → ∀ φ : (Fin r → K) →+ C, (∀ g h m, φ (repOn (twGL ρ χ) κ K g (repOn (twGL ρ χ) κ K h m)) = φ (repOn (twGL ρ χ) κ K h (repOn (twGL ρ χ) κ K g m))) → φ = 0 := by
  intro Γ O Λ K C _ _ _ _ _ _ _ _ _ _ r ρ χ κ hr hm hsp φ hφ

  have hunit : ∀ g, IsUnit ((κ g : Λ) * algebraMap O Λ (((χ g)⁻¹ : Oˣ) : O)) := fun g =>
    (κ g).isUnit.mul (((χ g)⁻¹).isUnit.map _)
  have hcomm : ∀ A ∈ Set.range fun g =>
      matAct (M := K) (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (algebraMap O Λ)),
      ∀ B ∈ Set.range fun g =>
      matAct (M := K) (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (algebraMap O Λ)),
      ∀ m, φ (A (B m)) = φ (B (A m)) := by
    rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩ m
    obtain ⟨w, hw⟩ : ∃ w : Λ, ((κ g : Λ) * algebraMap O Λ (((χ g)⁻¹ : Oˣ) : O)) *
        ((κ h : Λ) * algebraMap O Λ (((χ h)⁻¹ : Oˣ) : O)) * w = 1 :=
      ⟨(((hunit g).mul (hunit h)).unit⁻¹ : Λˣ), by simp⟩
    have e := hφ g h (w • m)
    simp only [matAct_rep, map_smul, smul_smul] at e
    have e1 : w * ((κ h : Λ) * algebraMap O Λ (((χ h)⁻¹ : Oˣ) : O)) *
        ((κ g : Λ) * algebraMap O Λ (((χ g)⁻¹ : Oˣ) : O)) = 1 := by linear_combination hw
    have e2 : w * ((κ g : Λ) * algebraMap O Λ (((χ g)⁻¹ : Oˣ) : O)) *
        ((κ h : Λ) * algebraMap O Λ (((χ h)⁻¹ : Oˣ) : O)) = 1 := by linear_combination hw
    rw [e1, e2, one_smul, one_smul] at e
    exact e

  have hall : ∀ (P Q : Matrix (Fin r) (Fin r) O) (m : Fin r → K),
      φ (matAct (M := K) (P.map (algebraMap O Λ)) (matAct (M := K) (Q.map (algebraMap O Λ)) m)) =
        φ (matAct (M := K) (Q.map (algebraMap O Λ)) (matAct (M := K) (P.map (algebraMap O Λ)) m)) :=
    fun P Q => comm_span _ φ hcomm _ (matAct_of_span_residue_spans ρ hm hsp P) _ (matAct_of_span_residue_spans ρ hm hsp Q)

  have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr hr
  have hsingle : ∀ (a : Fin r) (x : K), φ (Pi.single a x) = 0 := by
    intro a x
    obtain ⟨b, hb⟩ := exists_ne a
    have e := hall (Matrix.of fun i j => if i = a ∧ j = b then (1 : O) else 0)
      (Matrix.of fun i j => if i = b ∧ j = b then (1 : O) else 0) (Pi.single b x)
    simp only [matAct_single] at e
    simpa [Pi.single_eq_of_ne hb] using e
  refine AddMonoidHom.ext fun m => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.univ_sum_single m, map_sum]
  simp [hsingle]

end GlobalTheory.ResComm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonPiAdicFiltrationModEll
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl

section Abstract

variable {O : Type} [CommRing O] {n : ℕ} {EE RA R : Type} [CommRing EE] [CommRing RA] [CommRing R]

theorem letA_dvd_of_forall_pow (p : ℕ) (a : LetA O n)
    (h : ∀ m : ℕ, ∃ a1 a2 : LetA O n, a = letπ ^ m * a1 + (p : LetA O n) * a2) :
    ∃ b : LetA O n, a = (p : LetA O n) * b := by
  have h1 : ∀ (i : ZMod n) (k : ℕ), ∃ c : O, PowerSeries.coeff k (a i) = (p : O) * c := by
    intro i k
    obtain ⟨a1, a2, h2⟩ := h (k + 1)
    refine ⟨PowerSeries.coeff k (a2 i), ?_⟩
    have h3 : a i = PowerSeries.X ^ (k + 1) * a1 i + PowerSeries.C (p : O) * a2 i := by
      rw [h2, map_natCast]; rfl
    rw [h3, map_add (f := _), PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_add,
      PowerSeries.coeff_C_mul]
  choose c hc using h1
  refine ⟨fun i => PowerSeries.mk (c i), funext fun i => PowerSeries.ext fun k => ?_⟩
  have h3 : ((p : LetA O n) * fun i => PowerSeries.mk (c i)) i =
      PowerSeries.C (p : O) * PowerSeries.mk (c i) := by
    rw [map_natCast]; rfl
  rw [h3, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc]

theorem near_abstract (p : ℕ) (f : LetA O n →+* EE) (io : EE →+* R) (ι : RA →+* R) (t : R)
    (τ : RA) (hτ : ι τ = t) (ht : io (f letπ) = t) (hu : IsUnit (f letπ))
    (hd : ∀ x : EE, ∃ (a : LetA O n) (m : ℕ), x * f (letπ ^ m) - f a ∈ Ideal.span {(p : EE) ^ 1})
    (hs : ∀ a : LetA O n, f a ∈ Ideal.span {(p : EE) ^ 1} →
      ∃ b : LetA O n, a = (p : LetA O n) ^ 1 * b)
    (key : ∀ (m : ℕ) (a : LetA O n), Near ι p t m (io (f a)) →
      ∃ a1 a2 : LetA O n, a = letπ ^ m * a1 + (p : LetA O n) * a2) :
    (∀ (m : ℕ) (e : EE), Near ι p t m (io e) →
      ∃ (a : LetA O n) (e' : EE), e = f (letπ ^ m * a) + (p : EE) * e') ∧
    ∀ (e : EE) (r : R), io e = (p : R) * r → ∃ e' : EE, e = (p : EE) * e' := by
  have H1 : ∀ (m : ℕ) (e : EE), Near ι p t m (io e) →
      ∃ (a : LetA O n) (e' : EE), e = f (letπ ^ m * a) + (p : EE) * e' := by
    intro m e he
    obtain ⟨a, N, h1⟩ := hd e
    rw [pow_one, Ideal.mem_span_singleton] at h1
    obtain ⟨e1, h1⟩ := h1
    have h2 : f a = f letπ ^ N * e - p * e1 := by
      rw [map_pow] at h1; linear_combination -h1
    have h3 : Near ι p t (N + m) (io (f a)) := by
      rw [h2, map_sub, map_mul, map_mul, map_pow, ht, map_natCast]
      refine Near.sub (Near.mul ?_ he) (Near.of_mul _ _)
      simpa using Near.pow_mul (ι := ι) (p := p) (t := t) N 1
    obtain ⟨a1, a2, h4⟩ := key _ _ h3
    obtain ⟨u, hu'⟩ := hu.exists_right_inv
    have h5 : f letπ ^ N * u ^ N = 1 := by rw [← mul_pow, hu', one_pow]
    refine ⟨a1, u ^ N * (e1 + f a2), ?_⟩
    rw [h4, map_add (f := _), map_mul, map_mul, map_pow, map_natCast, pow_add] at h2
    rw [map_mul, map_pow]
    linear_combination (-u ^ N) * h2 - (e - f letπ ^ m * f a1) * h5
  refine ⟨H1, fun e r he => ?_⟩
  have h1 := fun m => H1 m e (he ▸ Near.of_mul m r)
  choose a e' h2 using h1
  obtain ⟨b, hb⟩ := letA_dvd_of_forall_pow p (a 0) fun m => by
    obtain ⟨b, hb⟩ := hs (a 0 - letπ ^ m * a m) (by
      rw [pow_one, Ideal.mem_span_singleton]
      refine ⟨e' m - e' 0, ?_⟩
      have h3 := h2 0
      rw [pow_zero, one_mul] at h3
      rw [map_sub]
      linear_combination h2 m - h3)
    exact ⟨a m, b, by linear_combination hb⟩
  refine ⟨f b + e' 0, ?_⟩
  have h3 := h2 0
  rw [pow_zero, one_mul, hb, map_mul, map_natCast] at h3
  linear_combination h3

end Abstract


set_option maxHeartbeats 1000000 in
theorem near_ioE : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), (∀ (m : ℕ) (e : W.EE), NearPi AI LL s m (E.tie.ioE e) → ∃ (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) (e' : W.EE), e = algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE (letπ ^ m * a) + (l : W.EE) * e') ∧ ∀ (e : W.EE) (r : RW LL), E.tie.ioE e = (l : RW LL) * r → ∃ e' : W.EE, e = (l : W.EE) * e' := by
  intro l _ P AI K s LL h W E
  have hd := W.EE_dense
  have hs := W.EE_sat
  rw [P.PD_p K] at hd hs
  exact near_abstract l (algebraMap _ W.EE) (E.tie.ioE : W.EE →+* RW LL)
    (inclR LL : RA LL →+* RW LL) (piR AI LL s) _ rfl (_root_.GlobalTheory.Decompl.ioE_compat l P AI K s LL h W E).2.2.1
    W.EE_π (fun x => hd x 1) (fun a => hs a 1)
    (fun m a ha => _root_.GlobalTheory.Decompl.mem_pow_pi_of_nearPi l P AI K s LL h W E m a (E.tie.ioE_ext a ▸ ha))

end GlobalTheory.Decompl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRingFreeOverFrobeniusImageStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleRing_free_over_frobenius_image : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ x : W.EE, ∃! c : Fin l → W.EE, x = ∑ j : Fin l, algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE ((1 : (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)))) + (letπ : (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))))) ^ (j : ℕ) * W.φE (c j) := by
  first | exact @GlobalTheory.NL.FreeEE.ee_free | exact GlobalTheory.NL.FreeEE.ee_free | (intros; apply GlobalTheory.NL.FreeEE.ee_free <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffTensorAcrisWithFrobeniusGaloisStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeffTensorAcris_with_frobenius_galois : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (LL : FinExt l) (β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B), IsBeta AI β → ∃ (A : Type) (_ : CommRing A) (b : RA LL →+* A) (κ : A →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B) (φ : A →+* A) (γ : GQ l → (A →+* A)) (t : A), GlobalTheory.Decompl.LAdic.Good l A ∧ ((∀ y, κ (b y) = β y) ∧ (∀ o w, φ (b (o ⊗ₜ[ℤ_[l]] w)) = b (o ⊗ₜ[ℤ_[l]] WittVector.frobenius w)) ∧ (∀ x, κ (φ x) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) P.φB (κ x)) ∧ (∀ g o w, γ g (b (o ⊗ₜ[ℤ_[l]] w)) = b (o ⊗ₜ[ℤ_[l]] AI.actW g w)) ∧ (∀ g x, κ (γ g x) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) (P.actQ g).toAlgHom (κ x)) ∧ κ t = (1 : ↥LL.1) ⊗ₜ[ℚ_[l]] P.tB) ∧ (∀ s : ℕ, ∃ d : ℕ, 0 < d ∧ (l : A) ∣ b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1)) ^ d) ∧ (∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ u z : A, ((n.factorial : ℕ) : A) * u = ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : A) * b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.μ) ^ (k + 1) ∧ t - u = (l : A) ^ r * z) ∧ ∀ (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (m : ℕ), ∃ C : ℕ, ∀ y : A, (l : P.R.BdR) ^ C * Algebra.TensorProduct.productMap ι P.ιB (κ y) ∈ GlobalTheory.ExpImage.Lat AI m 0 := by
  first | exact @GlobalTheory.HWLCris.exists_tensor_acris | exact GlobalTheory.HWLCris.exists_tensor_acris | (intros; apply GlobalTheory.HWLCris.exists_tensor_acris <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrameOfTorsionInvariantsStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_of_torsion_invariants : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA} (E : EtTie W RA RW inclR φR gR πA) {k : Type} [Field k] [Algebra O k] {Rk : Type} [CommRing Rk] [Algebra k Rk] [Algebra O Rk] [IsScalarTower O k Rk] (ρ : RW →ₐ[O] Rk) (lam : O) (κ : k⸨X⸩ →+* Rk) (a : G → (Rk →ₐ[k] Rk)) (ι : k⸨X⸩ →+* k⸨X⸩) (σ : {δ // δ ∈ W.DelF} → (k⸨X⸩ →+* k⸨X⸩)), IsRed E ρ (k := k) lam κ → IsDel E ρ κ a ι σ → ∀ (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q → ∀ i, (∃ u : Fin A.m → W.DD T, ∀ x, ∃ c : Fin A.m → k⸨X⸩, eps E ρ i • J E ρ T q x = ∑ j, κ (c j) • eps E ρ i • J E ρ T q (u j)) → ∃ β : Vc k A.m →+ Rk ⊗[k] (Fin A.m → k), IsFrame (κ.comp ι) (eps E ρ i) β ∧ ∀ y, (∃ x, β x = y) ↔ ∃ x : ↥(DΔ W T), y = eps E ρ i • J E ρ T q x := by
  first | exact @GlobalTheory.RedFun.exists_frame_of_invariants | exact GlobalTheory.RedFun.exists_frame_of_invariants | (intros; apply GlobalTheory.RedFun.exists_frame_of_invariants <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralDualFunctionalStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_dual_functional : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
    (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
    ∃ (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
      (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) ∧
      (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) ∧
      (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) := by
  first | exact @GlobalTheory.IntDual.intDual_coef | exact GlobalTheory.IntDual.intDual_coef | (intros; apply GlobalTheory.IntDual.intDual_coef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLimitCocycleOfCompatibleModPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_limit_cocycle_of_compatible_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (hI : ∀ n : ℕ, StableSub LA (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)) (w : ℕ → ↥(GK K) → ↥LA.T), (∀ n, (fun g => (Submodule.Quotient.mk (w n g) : ↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T))) ∈ quotientCocycles LA _ (hI n)) → (∀ n g, w (n + 1) g - w n g ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)) → ∃ d ∈ latticeCocycles LA, ∀ n g, ∃ t ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T), d g = (w n g : A.V) + (t : A.V) := by
  first | exact @GlobalTheory.LimCocycle.limit_cocycle | exact GlobalTheory.LimCocycle.limit_cocycle | (intros; apply GlobalTheory.LimCocycle.limit_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMutuallyDualStableLatticesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mutuallyDual_stable_lattices : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∃ (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ), IsDualLat1 (P.PD K) LA LA' m ∧ IsDualLat1 (P.PD K) LA' LA m.flip := by
  first | exact @GlobalTheory.StableDual.stable_dual_lattices | exact GlobalTheory.StableDual.stable_dual_lattices | (intros; apply GlobalTheory.StableDual.stable_dual_lattices <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLatticeCocyclesModUniformizerPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_latticeCocycles_mod_uniformizer_pow : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (n : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)), (quotientCocycles LA _ hI : Set (↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T))).Finite := by
  first | exact @GlobalTheory.CocycleModPow.finite_Z1Q | exact GlobalTheory.CocycleModPow.finite_Z1Q | (intros; apply GlobalTheory.CocycleModPow.finite_Z1Q <;> assumption)
end

