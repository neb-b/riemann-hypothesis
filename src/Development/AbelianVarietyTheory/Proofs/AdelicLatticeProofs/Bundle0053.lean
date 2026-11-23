module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0051
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteAdelicDoubleCosetsOfRationalSLSubgroup
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem cf_congr_of_vanI_eq {ι : Type} [Fintype ι] [DecidableEq ι] {Γ Δ : Set (Matrix ι ι ℂ)}
    (h : vanI Γ = vanI Δ) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R) :
    CF Γ R R₀ ↔ CF Δ R R₀ := by

  have key : ∀ (S : Type) [CommRing S] [Algebra ℚ S], pts Γ S = pts Δ S := by
    intro S _ _
    simp only [pts, h]
  simp only [CF, key]

theorem cf_of_isQGroup : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → AdelicPair R R₀ → CF Γ R R₀ := by
  intro ι _ _

  suffices H : ∀ n : ℕ, ∀ (Γ : Set (Matrix ι ι ℂ)), Module.finrank ℂ (Submodule.span ℂ Γ) = n →
      ∀ (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → AdelicPair R R₀ → CF Γ R R₀ by
    intro Γ R _ _ R₀ hQ hA
    exact H _ Γ rfl R R₀ hQ hA
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Γ hn R _ _ R₀ hQ hA
    by_cases hS : SS Γ
    · exact _root_.GlobalTheory.ClassFin.cf_of_ss ι Γ R R₀ hQ hS hA
    · obtain ⟨e, he, hup, a, ha, ha0, hblk⟩ := _root_.GlobalTheory.ClassFin.exists_rat_idempotent_blk_eq_zero ι Γ hQ.toIsPre hS

      have hPre : IsPre (blk e '' Γ) := _root_.GlobalTheory.ClassFin.isPre_blk_image ι Γ e hQ.toIsPre he hup
      obtain ⟨hQ', hvan, hspan⟩ := _root_.GlobalTheory.ClassFin.RatClosure.ratClosure ι (blk e '' Γ) hPre
      have hlt := _root_.GlobalTheory.ClassFin.finrank_span_blk_image_lt ι Γ e a ha ha0 hblk
      have hcl : CF (pts (blk e '' Γ) ℂ) R R₀ :=
        ih _ (by rw [← hn, hspan]; exact hlt) _ rfl R R₀ hQ' hA
      have hblkCF : CF (blk e '' Γ) R R₀ := (cf_congr_of_vanI_eq hvan R R₀).mp hcl
      exact GlobalTheory.T.hasFiniteAdelicDoubleCosets_of_blockDiagPart_image ι Γ e R R₀ hQ he hup hA hblkCF

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem hasseNormSt : GlobalTheory.Published.HasseNormSt := by
  intro F _ _ δ x hδ hx hreal hfin
  classical
  by_cases hsq : IsSquare δ
  · exact GlobalTheory.Published.HasseNormSt.of_isSquare hδ hsq x
  obtain ⟨S, -, hS⟩ := exists_superset_mem_sUnits F {Units.mk0 δ hδ, Units.mk0 x hx} ∅
  obtain ⟨T, hST, hT⟩ := exists_admissible_superset_finite_places F S
  have hδT : Units.mk0 δ hδ ∈ sUnits F T := hS T hST _ (by simp)
  have hxT : Units.mk0 x hx ∈ sUnits F T := hS T hST _ (by simp)
  have hloc : Units.mk0 x hx ∈ locNorm F ((Units.mk0 δ hδ : Fˣ) : F) T := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · refine Subgroup.mem_iInf.mpr fun v => Subgroup.mem_iInf.mpr fun _ => ?_
      rw [mem_normSub]
      exact hfin v
    · refine Subgroup.mem_iInf.mpr fun σ => ?_
      rw [mem_normSub]
      exact hreal σ
  have h := _root_.GlobalTheory.QNorm.sUnit_mem_normSub_of_mem_locNorm F (Units.mk0 δ hδ) T hT hδT hsq _ hxT hloc
  rw [mem_normSub] at h
  exact h

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NpOfFinrankPrimeOfIsPrimitiveRoot
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_isKum_of_finrank_prime (p : ℕ) (F E : Type) [Field F] [Field E] [Algebra F E]
    [IsGalois F E] (ζ : F) (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    (hr : Module.finrank F E = p) :
    ∃ (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (hr ▸ hp.pos)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic (E ≃ₐ[F] E) :=
    isCyclic_of_prime_card (p := p) (by rw [IsGalois.card_aut_eq_finrank, hr])
  have hK : (primitiveRoots (Module.finrank F E) F).Nonempty :=
    ⟨ζ, by rw [hr, mem_primitiveRoots hp.pos]; exact hζ⟩
  obtain ⟨θ, ⟨δ, hδ⟩, hθ⟩ := exists_root_adjoin_eq_top_of_isCyclic F E hK
  have hirr := irreducible_X_pow_sub_C_of_root_adjoin_eq_top hδ.symm hθ
  rw [hr] at hirr hδ
  have hmin : (X ^ p - C δ : F[X]) = minpoly F θ :=
    minpoly.eq_of_irreducible_of_monic hirr (by simp [hδ]) (monic_X_pow_sub_C _ hp.ne_zero)
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (K := F) (L := E) (x := algebraMap F E ζ * θ)
    (y := θ) (Algebra.IsAlgebraic.isAlgebraic θ) (by
      rw [← hmin]
      rw [map_sub, map_pow, aeval_X, aeval_C, mul_pow, ← map_pow, hζ.pow_eq_one, map_one, one_mul,
        hδ, sub_self])
  refine ⟨δ, θ, σ, hp, hζ, (X_pow_sub_C_irreducible_iff_of_prime hp).1 hirr, hδ.symm, hσ, ?_⟩
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (Algebra.IsAlgebraic.isAlgebraic θ), hθ, IntermediateField.top_toSubalgebra]

theorem np_of_finrank_prime_of_isPrimitiveRoot : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] [IsGalois F E] (ζ : F), p.Prime → IsPrimitiveRoot ζ p → Module.finrank F E = p → NP F E := by
  intro p F E _ _ _ _ _ _ _ ζ hp hζ hr x hx hloc
  classical
  obtain ⟨δ, θ, σ, hk⟩ := exists_isKum_of_finrank_prime p F E ζ hp hζ hr
  have hδ0 : δ ≠ 0 := fun h => hk.nonpow 0 (by rw [h, zero_pow hp.ne_zero])
  obtain ⟨S₁, -, hS₁⟩ := exists_superset_mem_sUnits F {Units.mk0 δ hδ0, Units.mk0 x hx} ∅
  obtain ⟨S, hS, hadm⟩ := (exists_admissiblePlaces_superset_and_mono p F hp.pos).1 S₁
  have hfin : Units.mk0 x hx ∈ finNorm p F δ S := by
    simp only [finNorm, Subgroup.mem_iInf]
    intro v _
    exact _root_.GlobalTheory.CNorm.mem_kNorm_of_tNorm p F E (v.adicCompletion F) ζ δ θ σ hk (Units.mk0 x hx) (hloc.1 v)
  have hx' := _root_.GlobalTheory.CNorm.sUnit_mem_kNorm_of_mem_finNorm p F ζ (Units.mk0 δ hδ0) S hp hζ hadm (hS₁ S hS _ (by simp))
    hk.nonpow (Units.mk0 x hx) (hS₁ S hS _ (by simp)) hfin
  obtain ⟨y, hy⟩ := (mem_kNorm p (RingHom.id F) δ _).1 hx'
  obtain ⟨-, -, -, -, -, ⟨e⟩, -⟩ := kummer_galois p F E ζ δ θ σ hk
  refine ⟨e.symm y, ?_⟩
  rw [Algebra.norm_eq_of_algEquiv]
  exact hy

end GlobalTheory.CNorm
end

