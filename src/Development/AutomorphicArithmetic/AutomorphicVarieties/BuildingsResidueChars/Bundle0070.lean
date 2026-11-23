module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricSquareMixedCharpoly
section
open Polynomial Matrix

namespace UpperTheory.V.Sd.S2.symmetric_square_mixed_charpoly

variable {k : Type} [Field k]

private def blk (A B : Matrix (Fin 2) (Fin 2) k) : Matrix (Fin 4) (Fin 4) k :=
  !![A 0 0, A 0 1, 0, 0; A 1 0, A 1 1, 0, 0; 0, 0, B 0 0, B 0 1; 0, 0, B 1 0, B 1 1]

private def ant (A B : Matrix (Fin 2) (Fin 2) k) : Matrix (Fin 4) (Fin 4) k :=
  !![0, 0, A 0 0, A 0 1; 0, 0, A 1 0, A 1 1; B 0 0, B 0 1, 0, 0; B 1 0, B 1 1, 0, 0]

private def Pm (α β : k) : Matrix (Fin 4) (Fin 4) k :=
  !![0, α, 0, α; β, 0, -β, 0; 0, -1, 0, 1; 1, 0, 1, 0]

private def Qm (α β : k) : Matrix (Fin 4) (Fin 4) k :=
  (2 : k)⁻¹ • !![0, β⁻¹, 0, 1; α⁻¹, 0, -1, 0; 0, -β⁻¹, 0, 1; α⁻¹, 0, 1, 0]

private lemma PQ (h2 : (2 : k) ≠ 0) {α β : k} (ha : α ≠ 0) (hb : β ≠ 0) : Pm α β * Qm α β = 1 := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;>
    simp [Pm, Qm, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp [h2, ha, hb] <;> ring

private lemma cp_conj (h2 : (2 : k) ≠ 0) {α β : k} (ha : α ≠ 0) (hb : β ≠ 0) (M N : Matrix (Fin 4) (Fin 4) k)
    (h : Pm α β * M = N * Pm α β) : M.charpoly = N.charpoly := by
  have h1 := PQ h2 ha hb
  have h3 : Qm α β * Pm α β = 1 := mul_eq_one_comm.mp h1
  have : M = Qm α β * (N * Pm α β) := by rw [← h, ← Matrix.mul_assoc, h3, Matrix.one_mul]
  rw [this, Matrix.charpoly_mul_comm, Matrix.mul_assoc, h1, Matrix.mul_one]

private lemma P_mix (h2 : (2 : k) ≠ 0) (α β : kˣ) (A B : Matrix (Fin 2) (Fin 2) k) :
    Pm (α : k) β * mix (β / α) A B = blk A B * Pm (α : k) β := by
  have ha := α.ne_zero
  have hb := β.ne_zero
  ext i j : 1
  fin_cases i <;> fin_cases j <;>
    simp [Pm, mix, blk, Matrix.mul_apply, Fin.sum_univ_four, Units.val_div_eq_div_val] <;>
    field_simp [h2, ha, hb] <;> ring

private lemma blk_P (α β : k) (A B : Matrix (Fin 2) (Fin 2) k) :
    blk A B * Pm α β * Matrix.diagonal ![β, -α, -β, α] =
      ant (A * Matrix.diagonal ![α ^ 2, β ^ 2]) B * Pm α β := by
  ext i j : 1
  rw [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [Pm, ant, blk, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private lemma cp_blk (A B : Matrix (Fin 2) (Fin 2) k) : (blk A B).charpoly = A.charpoly * B.charpoly := by
  simp only [Matrix.charpoly, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.det_fin_zero, Matrix.submatrix_apply, Matrix.charmatrix_apply]
  norm_num [blk, Fin.succAbove, Fin.lt_def, Fin.ext_iff, Matrix.diagonal_apply]
  ring

private lemma cp_ant (A B : Matrix (Fin 2) (Fin 2) k) : (ant A B).charpoly = (A * B).charpoly.comp (X ^ 2) := by
  simp only [Matrix.charpoly, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.det_fin_zero, Matrix.submatrix_apply, Matrix.charmatrix_apply]
  norm_num [ant, Fin.succAbove, Fin.lt_def, Fin.ext_iff, Matrix.diagonal_apply, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring

end UpperTheory.V.Sd.S2.symmetric_square_mixed_charpoly

open UpperTheory.V.Sd.S2 UpperTheory.V.Sd.S2.symmetric_square_mixed_charpoly in
theorem UpperTheory.symmetric_square_mixed_charpoly :
    UpperTheory.V.Sd.S2.MixCp := by
  intro k Γ₀ Γ _ _ _ j t α β ρ R H s hs
  have hN : j.range.Normal := Subgroup.normal_of_index_eq_two H.index
  have hc : ∀ h : Γ₀, ∃ h', j h' = t⁻¹ * j h * t := fun h => by
    have := hN.conj_mem' (j h) ⟨h, rfl⟩ t
    exact this
  have hm : ∀ a b : Γ, a ∉ j.range → b ∉ j.range → a * b ∈ j.range := fun a b ha hb =>
    (Subgroup.mul_mem_iff_of_index_two H.index).mpr (by simp [ha, hb])
  have ht' : t⁻¹ ∉ j.range := fun h => H.nmem (inv_mem_iff.mp h)
  refine ⟨fun g g' hg => ?_, fun g hg => ?_⟩
  · obtain ⟨h, hh⟩ := hm _ _ ht' hs
    obtain ⟨g'', hg''⟩ := hc g
    have e : g' = h⁻¹ * g'' * h := H.inj (by
      rw [map_mul, map_mul, map_inv, hh, hg'', hg]; group)
    rw [H.on g g'' hg'', cp_conj H.two α.ne_zero β.ne_zero _ _ (P_mix H.two α β _ _), cp_blk, e]
    congr 1
    rw [map_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  · obtain ⟨h, hh⟩ := hm _ _ hs ht'
    obtain ⟨h', hh'⟩ := hc h
    obtain ⟨u, hu⟩ := hm _ _ H.nmem H.nmem
    have e : g = h * u * h' := H.inj (by
      rw [map_mul, map_mul, hh', hu, hh, hg]; group)
    have es : s = j h * t := by rw [hh]; group
    have key : Pm (α : k) β * (R s : Matrix (Fin 4) (Fin 4) k) =
        ant ((ρ h : Matrix (Fin 2) (Fin 2) k) * Matrix.diagonal ![(α : k) ^ 2, (β : k) ^ 2]) (ρ h') * Pm (α : k) β := by
      rw [es, map_mul, Units.val_mul, H.on h h' hh', H.off, ← Matrix.mul_assoc, P_mix H.two, blk_P]
    rw [cp_conj H.two α.ne_zero β.ne_zero _ _ key, cp_ant, e, map_mul, map_mul, Units.val_mul, Units.val_mul, H.sq u hu]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaUnramifiedOfKillsRootsOfUnity
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem aux_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0) {ζ : Ω}
    (h : ζ ^ m = 1) : A.valuation ζ = 1 := by
  have h1 : A.valuation ζ ^ m = 1 := by rw [← map_pow, h, map_one]
  exact (pow_eq_one_iff_left hm).1 h1

private theorem power_bounds_of_between {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {η : Ω} (h1 : A.valuation η = 1)
    (h : A.valuation (η - 1) < 1) (i : ℕ) : A.valuation (1 - η ^ i) < 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : 1 - η ^ (i + 1) = η * (1 - η ^ i) - (η - 1) := by ring
    rw [e]
    refine A.valuation.map_sub_lt ?_ h
    rw [map_mul, h1, one_mul]; exact ih

private theorem root_of_unity_eq_one_of_close_residue {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hv : ¬ A.valuation (m : Ω) < 1) {η : Ω} (hη : η ^ m = 1) (h : A.valuation (η - 1) < 1) : η = 1 := by
  by_contra hne
  apply hv
  have hs : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have := mul_geom_sum η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have e : (m : Ω) = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [e]
  exact A.valuation.map_sum_lt one_ne_zero fun i _ => power_bounds_of_between A (aux_one A hm hη) h i

private theorem inertia_fixes_prime_to_roots {Ω : Type} [Field Ω] [CharZero Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hA : ¬ A.valuation (m : Ω) < 1) {g : G ℚ Ω} (hg : g ∈ Ine (F := ℚ) A) {ζ : Ω} (hζ : ζ ^ m = 1) : g ζ = ζ := by
  have hv := aux_one A hm hζ
  have h0 : ζ ≠ 0 := by
    rintro rfl
    simp at hv
  have e : g ζ / ζ - 1 = (g ζ - ζ) / ζ := by field_simp
  have : g ζ / ζ = 1 := by
    refine root_of_unity_eq_one_of_close_residue A hm hA (by rw [div_pow, ← map_pow, hζ, map_one, div_one]) ?_
    rw [e, map_div₀, hv, div_one]; exact hg.2 ζ hv.le
  exact (div_eq_one_iff_eq h0).1 this

private theorem open_kernel_killing_roots_of_unity {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {w : ℕ} (hw : w ≠ 0) {C : Type} [Group C]
    (θ : G ℚ Ω →* C) (hk : KillsMu w θ) : IsOpen (θ.ker : Set (G ℚ Ω)) := by
  have hfin : {ζ : Ω | ζ ^ w = 1}.Finite := by
    refine (nthRoots w (1 : Ω)).finite_toSet.subset fun ζ hζ => ?_
    exact (mem_nthRoots (Nat.pos_of_ne_zero hw)).2 hζ
  haveI : Finite {ζ : Ω | ζ ^ w = 1} := hfin
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ : Ω | ζ ^ w = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin ℚ {ζ : Ω | ζ ^ w = 1}).fixingSubgroup) (fun g hg => ?_)
    (IntermediateField.fixingSubgroup_isOpen _)
  refine hk g fun ζ hζ => ?_
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ (IntermediateField.subset_adjoin _ _ hζ)

theorem UpperTheory.theta_unramified_of_kills_roots_of_unity :
    UpperTheory.V.Sd.S3.ThetaUnr := by
  intro Ω _ _ _ l hl w hw θ hθ hk
  have h1 : ∀ A, Raw.Away {w} A → Ine (F := ℚ) A ≤ θ.ker := fun A hA g hg =>
    hk g fun ζ hζ => inertia_fixes_prime_to_roots A hw.ne_zero (hA w (Finset.mem_singleton_self w)) hg hζ
  refine ⟨h1, fun F hF => ?_⟩
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  haveI : NeZero (l : Qbar l) := ⟨Nat.cast_ne_zero.2 hl.out.ne_zero⟩
  have hc : Nat.card (rootsOfUnity l (Qbar l)) = Nat.card (Multiplicative (ZMod l)) := by
    rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity]; simp
  let e := mulEquivOfCyclicCardEq hc
  have hm : ∀ g, θ g ∈ rootsOfUnity l (Qbar l) := fun g => by
    rw [mem_rootsOfUnity]
    exact DFunLike.congr_fun hθ g
  have hker : (e.toMonoidHom.comp (θ.codRestrict _ hm)).ker = θ.ker := by
    ext g
    simp [MonoidHom.mem_ker, Subtype.ext_iff]
  have := hF (e.toMonoidHom.comp (θ.codRestrict _ hm))
  rw [hker] at this
  exact this (open_kernel_killing_roots_of_unity hw.ne_zero θ hk) h1
end

