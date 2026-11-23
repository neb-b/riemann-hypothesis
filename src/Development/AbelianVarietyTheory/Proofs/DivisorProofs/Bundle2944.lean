module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2098
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2363
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1938
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2253
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2920
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPelUnifPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeastIntCombinationMinimiserCellUnitary
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc.FinTypes

theorem single : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], IsPolFanOn bar φ Y → ∀ (n N : ℕ) [NeZero N], 3 ≤ N → Odd N → ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → ∀ b₀ ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b₀ x x) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b₀ (μ cl) (μ cl) ≤ b₀ α α) → ∃ (ι : ℕ) (L : Finset ((Fin n → ZMod N) → ℤ)), 1 ≤ ι ∧ ∀ b' ∈ balForms bar Y, (∀ x, 0 ≤ b' x x) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) → (∀ ν ∈ L, (ι : ℝ) * φ.evalZ b' ≤ ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl)) ∧ ∃ ν ∈ L, (ι : ℝ) * φ.evalZ b' = ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl) := by
  classical
  intro O _ bar φ Y _ _ _ _ hY n N _ hN3 hNo eb μ hμ b₀ hb₀ hpos hmin
  obtain ⟨p, m, γ, hcone, hcov⟩ := _root_.GlobalTheory.UPoinc.CellCones.exists_finite_cones O bar φ Y hY n N hN3 eb μ hμ b₀ hb₀ hpos hmin
  obtain ⟨Nℓ, ℓ, hNℓ, hℓ⟩ := _root_.GlobalTheory.PolFan.cones_eq_min_linear O bar φ Y p m γ hcone
  choose D ν hD hν using fun i : Fin p => _root_.GlobalTheory.Poinc.linForm_eq_sum_lifts Y n N hN3 hNo eb μ hμ (ℓ i)
  obtain ⟨E, hDE⟩ : ∃ E : Fin p → ℕ, ∀ i, D i * E i = ∏ j, D j :=
    ⟨fun i => ∏ j ∈ Finset.univ.erase i, D j, fun i => Finset.mul_prod_erase _ _ (Finset.mem_univ i)⟩
  have hDp : 0 < ∏ j, D j := Finset.prod_pos (fun j _ => hD j)
  refine ⟨Nℓ * ∏ j, D j, Finset.univ.image (fun i c => (E i : ℤ) * ν i c), ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hNℓ.ne' hDp.ne')
  intro b' hb' hp hm
  have hcv := hcov b' hb' hp hm
  obtain ⟨hle, i1, heq⟩ := hℓ b' hb' hp hcv
  have key : ∀ i, ∑ c, (((E i : ℤ) * ν i c : ℤ) : ℝ) * ((b' (μ c) (μ c) : ℤ) : ℝ)
      = ((E i : ℝ) * (D i : ℝ)) * ((ℓ i b' : ℤ) : ℝ) := by
    intro i
    have h' : (((∑ c, ν i c * b' (μ c) (μ c) : ℤ)) : ℝ) = (((D i : ℤ) * ℓ i b' : ℤ) : ℝ) := by
      rw [hν i b' hb'.1]
    push_cast at h' ⊢
    calc ∑ c, (E i : ℝ) * (ν i c : ℝ) * (b' (μ c) (μ c) : ℝ)
        = (E i : ℝ) * ∑ c, (ν i c : ℝ) * (b' (μ c) (μ c) : ℝ) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun c _ => ?_); ring
      _ = _ := by rw [h']; ring
  have hι : ∀ i, ((Nℓ * ∏ j, D j : ℕ) : ℝ) = ((E i : ℝ) * (D i : ℝ)) * (Nℓ : ℝ) := by
    intro i; rw [← hDE i]; push_cast; ring
  refine ⟨fun ν' hν' => ?_, ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hν'
    have hc : (0 : ℝ) ≤ (E i : ℝ) * (D i : ℝ) := by positivity
    calc ((Nℓ * ∏ j, D j : ℕ) : ℝ) * φ.evalZ b'
        = ((E i : ℝ) * (D i : ℝ)) * ((Nℓ : ℝ) * φ.evalZ b') := by rw [hι i]; ring
      _ ≤ ((E i : ℝ) * (D i : ℝ)) * ((ℓ i b' : ℤ) : ℝ) := mul_le_mul_of_nonneg_left (hle i) hc
      _ = _ := (key i).symm
  · refine ⟨_, Finset.mem_image.mpr ⟨i1, Finset.mem_univ _, rfl⟩, ?_⟩
    calc ((Nℓ * ∏ j, D j : ℕ) : ℝ) * φ.evalZ b'
        = ((E i1 : ℝ) * (D i1 : ℝ)) * ((Nℓ : ℝ) * φ.evalZ b') := by rw [hι i1]; ring
      _ = ((E i1 : ℝ) * (D i1 : ℝ)) * ((ℓ i1 b' : ℤ) : ℝ) := by rw [heq]
      _ = _ := (key i1).symm

theorem P1 : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], IsPolFanOn bar φ Y → ∀ (n N : ℕ) [NeZero N], 3 ≤ N → Odd N → ∀ (ebY : Y ≃ₗ[ℤ] (Fin n → ℤ)), ∃ (ι : ℕ) (𝓛₀ : Finset (Finset ((Fin n → ZMod N) → ℤ))), 1 ≤ ι ∧ ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (ebX : X ≃ₗ[ℤ] (Fin n → ℤ)) (f : X ≃ₗ[O] Y), ∀ b ∈ balForms bar X, (∀ x, x ≠ 0 → 0 < b x x) → ∀ μ : (Fin n → ZMod N) → X, (∀ cl i, ((ebX (μ cl) i : ℤ) : ZMod N) = cl i) → (∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → ∃ L ∈ 𝓛₀, ∀ b' ∈ balForms bar X, (∀ x, 0 ≤ b' x x) → (∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) → (∀ ν ∈ L, (ι : ℝ) * φ.evalZ b' ≤ ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl)) ∧ ∃ ν ∈ L, (ι : ℝ) * φ.evalZ b' = ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl) := by
  classical
  intro O _ bar φ Y _ _ _ _ hY n N _ hN3 hNo ebY
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.Poinc.MinSysTypeBal.finite_minimiser_systems_upTo_aut O bar φ Y hY n N hN3 ebY
  have hP : ∀ μ' : (Fin n → ZMod N) → Y,
      ((∀ cl i, ((ebY (μ' cl) i : ℤ) : ZMod N) = cl i) ∧ ∃ b₀ ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b₀ x x) ∧
        (∀ cl (α : Y), (∀ i, ((ebY α i : ℤ) : ZMod N) = cl i) → b₀ (μ' cl) (μ' cl) ≤ b₀ α α)) →
      ∃ (ι : ℕ) (L : Finset ((Fin n → ZMod N) → ℤ)), 1 ≤ ι ∧ ∀ b' ∈ balForms bar Y, (∀ x, 0 ≤ b' x x) →
        (∀ cl (α : Y), (∀ i, ((ebY α i : ℤ) : ZMod N) = cl i) → b' (μ' cl) (μ' cl) ≤ b' α α) →
        (∀ ν ∈ L, (ι : ℝ) * φ.evalZ b' ≤ ∑ cl, (ν cl : ℝ) * b' (μ' cl) (μ' cl)) ∧
          ∃ ν ∈ L, (ι : ℝ) * φ.evalZ b' = ∑ cl, (ν cl : ℝ) * b' (μ' cl) (μ' cl) :=
    fun μ' ⟨h1, b₀, hb₀, h2, h3⟩ => single O bar φ Y hY n N hN3 hNo ebY μ' h1 b₀ hb₀ h2 h3
  choose! ιf Lf hιf hLf using hP
  set ι : ℕ := ∏ μ' ∈ S, max (ιf μ') 1 with hιdef
  refine ⟨ι, S.biUnion fun μ' => Finset.univ.image fun σ : Equiv.Perm (Fin n → ZMod N) =>
    (Lf μ').image fun ν c => ((ι / ιf μ' : ℕ) : ℤ) * ν (σ c), ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun _ _ => by omega)
  intro X _ _ _ ebX f b hb hbp μ hμ hmin
  have hbY : pull f.symm.toLinearMap b ∈ balForms bar Y := pull_mem _ hb
  have hbYp : ∀ x, x ≠ 0 → 0 < pull f.symm.toLinearMap b x x := fun x hx => by
    simpa using hbp (f.symm x) (by simpa using hx)
  obtain ⟨e, he⟩ := hS _ hbY hbYp
  set g : Y ≃ₗ[O] X := e.trans f.symm with hg
  obtain ⟨σ, hσ1, hσ2⟩ := _root_.GlobalTheory.transport_minimisers O Y X n N ebY ebX g μ hμ
  set μ' : (Fin n → ZMod N) → Y := fun c => g.symm (μ (σ c)) with hμ'
  have hpull : ∀ β : LinearMap.BilinForm ℤ X, pull e.toLinearMap (pull f.symm.toLinearMap β) = pull g.toLinearMap β :=
    fun β => LinearMap.ext₂ fun x y => rfl
  have hmem : μ' ∈ S := he μ' hσ1 (by rw [hpull]; exact hσ2 b hmin)
  have hgb : pull g.toLinearMap b ∈ balForms bar Y := pull_mem _ hb
  have hgp : ∀ x, x ≠ 0 → 0 < pull g.toLinearMap b x x := fun x hx => by
    simpa using hbp (g x) (by simpa using hx)
  have hPμ : (∀ cl i, ((ebY (μ' cl) i : ℤ) : ZMod N) = cl i) ∧ ∃ b₀ ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b₀ x x) ∧
        (∀ cl (α : Y), (∀ i, ((ebY α i : ℤ) : ZMod N) = cl i) → b₀ (μ' cl) (μ' cl) ≤ b₀ α α) :=
    ⟨hσ1, _, hgb, hgp, hσ2 b hmin⟩
  have hι1 := hιf _ hPμ
  have hL := hLf _ hPμ
  have hdvd : ιf μ' ∣ ι := by
    have := Finset.dvd_prod_of_mem (fun μ'' => max (ιf μ'') 1) hmem
    simpa [max_eq_left hι1] using this
  set k : ℕ := ι / ιf μ' with hk
  have hkι : (ι : ℝ) = k * ιf μ' := by exact_mod_cast (Nat.div_mul_cancel hdvd).symm
  refine ⟨(Lf μ').image fun ν c => ((k : ℕ) : ℤ) * ν (σ.symm c),
    Finset.mem_biUnion.2 ⟨μ', hmem, Finset.mem_image.2 ⟨σ.symm, Finset.mem_univ _, rfl⟩⟩, ?_⟩
  intro b' hb' hb'p hb'min
  have key := hL (pull g.toLinearMap b') (pull_mem _ hb') (fun x => hb'p _) (hσ2 b' hb'min)
  have hφ' : φ.evalZ (pull g.toLinearMap b') = φ.evalZ b' := evalZ_pull φ g.surjective b'
  have hq : ∀ c, pull g.toLinearMap b' (μ' c) (μ' c) = b' (μ (σ c)) (μ (σ c)) := fun c => by
    simp [μ']
  have hsum : ∀ ν : (Fin n → ZMod N) → ℤ,
      ∑ c, ((((k : ℕ) : ℤ) * ν (σ.symm c) : ℤ) : ℝ) * b' (μ c) (μ c) =
        k * ∑ c, (ν c : ℝ) * pull g.toLinearMap b' (μ' c) (μ' c) := fun ν => by
    rw [Finset.mul_sum, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hq]; simp; ring
  have hlhs : (ι : ℝ) * φ.evalZ b' = k * ((ιf μ' : ℝ) * φ.evalZ (pull g.toLinearMap b')) := by
    rw [hφ', hkι]; ring
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  refine ⟨fun ν' hν' => ?_, ?_⟩
  · obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hν'
    rw [hsum, hlhs]
    exact mul_le_mul_of_nonneg_left (key.1 ν hν) hk0
  · obtain ⟨ν, hν, heq⟩ := key.2
    exact ⟨_, Finset.mem_image_of_mem _ hν, by rw [hsum, hlhs, heq]⟩

end GlobalTheory.UPoinc.FinTypes

theorem GlobalTheory.UPoinc.finite_types_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ : InvFun (𝓞 E)), IsPolFan H.bar q φ → ∀ (N : ℕ) [NeZero N], 3 ≤ N → Odd N → ∃ (B ι : ℕ) (𝓛 : ∀ n : ℕ, Finset (Finset ((Fin n → ZMod N) → ℤ))), 1 ≤ ι ∧ ∀ (n : ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (eb : X ≃ₗ[ℤ] (Fin n → ℤ)), n < B ∧ ∀ (b : LinearMap.BilinForm ℤ X), b ∈ balForms H.bar X → (∀ y, y ≠ 0 → 0 < b y y) → ∀ μ : (Fin n → ZMod N) → X, (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → ∃ L ∈ 𝓛 n, ∀ b' : LinearMap.BilinForm ℤ X, b' ∈ balForms H.bar X → (∀ y, 0 ≤ b' y y) → (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) → (∀ ν ∈ L, (ι : ℝ) * φ.evalZ b' ≤ ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl)) ∧ ∃ ν ∈ L, (ι : ℝ) * φ.evalZ b' = ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl) := by
  intro E _ _ _ H q φ hφ N _ hN3 hNo
  classical
  obtain ⟨R, Y, hY⟩ := GlobalTheory.ProjModFinIso.finitely_many_iso_classes E q
  set B : ℕ := Module.finrank ℚ E * q + 1 with hB
  have hP : ∀ (n : ℕ) (k : Fin R), ∃ (ι : ℕ) (𝓛₀ : Finset (Finset ((Fin n → ZMod N) → ℤ))), 1 ≤ ι ∧
      ((Module.Finite (𝓞 E) (Y k) ∧ Module.Projective (𝓞 E) (Y k) ∧ Module.finrank (𝓞 E) (Y k) ≤ q ∧
        Nonempty (Y k ≃ₗ[ℤ] (Fin n → ℤ))) →
      ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (ebX : X ≃ₗ[ℤ] (Fin n → ℤ))
        (f : X ≃ₗ[𝓞 E] Y k), ∀ b ∈ balForms H.bar X, (∀ x, x ≠ 0 → 0 < b x x) → ∀ μ : (Fin n → ZMod N) → X,
        (∀ cl i, ((ebX (μ cl) i : ℤ) : ZMod N) = cl i) →
        (∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) →
        ∃ L ∈ 𝓛₀, ∀ b' ∈ balForms H.bar X, (∀ x, 0 ≤ b' x x) →
          (∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) →
          (∀ ν ∈ L, (ι : ℝ) * φ.evalZ b' ≤ ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl)) ∧
            ∃ ν ∈ L, (ι : ℝ) * φ.evalZ b' = ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl)) := by
    intro n k
    by_cases hC : Module.Finite (𝓞 E) (Y k) ∧ Module.Projective (𝓞 E) (Y k) ∧ Module.finrank (𝓞 E) (Y k) ≤ q ∧
        Nonempty (Y k ≃ₗ[ℤ] (Fin n → ℤ))
    · obtain ⟨h1, h2, h3, ⟨ebY⟩⟩ := hC
      obtain ⟨ι, 𝓛₀, hι, h⟩ := GlobalTheory.UPoinc.FinTypes.P1 (𝓞 E) H.bar φ (Y k) (hφ (Y k) h3) n N hN3 hNo ebY
      exact ⟨ι, 𝓛₀, hι, fun _ => h⟩
    · exact ⟨1, ∅, le_rfl, fun h => (hC h).elim⟩
  choose ιf 𝓛f hιf h𝓛f using hP
  set ι : ℕ := ∏ n ∈ Finset.range B, ∏ k, ιf n k with hιdef
  have hιpos : 0 < ι := Finset.prod_pos fun n _ => Finset.prod_pos fun k _ => hιf n k
  refine ⟨B, ι, fun n => Finset.univ.biUnion fun k =>
    (𝓛f n k).image fun L => L.image fun ν c => ((ι / ιf n k : ℕ) : ℤ) * ν c, hιpos, ?_⟩
  intro n X _ _ _ _ hXq eb
  obtain ⟨hfinZ, -, hrk⟩ := GlobalTheory.finite_projective_int_of_ringOfIntegers E X
  have hn : Module.finrank ℤ X = n := by rw [eb.finrank_eq, Module.finrank_fin_fun]
  have hnB : n < B := by
    rw [hB, ← hn, hrk]
    have := Nat.mul_le_mul_left (Module.finrank ℚ E) hXq
    omega
  refine ⟨hnB, ?_⟩
  intro b hb hbp μ hμ hmin
  obtain ⟨k, ⟨f⟩⟩ := hY X hXq
  haveI h1 : Module.Finite (𝓞 E) (Y k) := Module.Finite.equiv f
  haveI h2 : Module.Projective (𝓞 E) (Y k) := Module.Projective.of_equiv f
  have h3 : Module.finrank (𝓞 E) (Y k) ≤ q := f.finrank_eq ▸ hXq
  have h4 : Nonempty (Y k ≃ₗ[ℤ] (Fin n → ℤ)) := ⟨f.symm.toAddEquiv.toIntLinearEquiv.trans eb⟩
  obtain ⟨L, hL, hLb⟩ := h𝓛f n k ⟨h1, h2, h3, h4⟩ X eb f b hb hbp μ hμ hmin
  have hdvd : ιf n k ∣ ι := by
    have h5 : ∏ k, ιf n k ∣ ι := Finset.dvd_prod_of_mem (fun n => ∏ k, ιf n k) (Finset.mem_range.2 hnB)
    exact (Finset.dvd_prod_of_mem (fun k => ιf n k) (Finset.mem_univ k)).trans h5
  set c : ℕ := ι / ιf n k with hc
  have hcι : (ι : ℝ) = c * ιf n k := by exact_mod_cast (Nat.div_mul_cancel hdvd).symm
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  refine ⟨L.image fun ν cl => ((c : ℕ) : ℤ) * ν cl,
    Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, Finset.mem_image.2 ⟨L, hL, rfl⟩⟩, ?_⟩
  intro b' hb' hb'p hb'min
  obtain ⟨hle, ν₀, hν₀, heq⟩ := hLb b' hb' hb'p hb'min
  have hsum : ∀ ν : (Fin n → ZMod N) → ℤ, ∑ cl, ((((c : ℕ) : ℤ) * ν cl : ℤ) : ℝ) * b' (μ cl) (μ cl) =
      c * ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl) := fun ν => by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun cl _ => ?_; push_cast; ring
  have hlhs : (ι : ℝ) * φ.evalZ b' = c * ((ιf n k : ℝ) * φ.evalZ b') := by rw [hcι]; ring
  refine ⟨fun ν' hν' => ?_, ⟨_, Finset.mem_image_of_mem _ hν₀, by rw [hsum, hlhs, heq]⟩⟩
  obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hν'
  rw [hsum, hlhs]
  exact mul_le_mul_of_nonneg_left (hle ν hν) hc0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionsExactKernelLocusOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LevTrivOpen

variable {S : Scheme.{0}}

theorem range_subset_iff_mem {k : Type} [Field k] (x : Sp k ⟶ S) (U : Set S) (p : Sp k) :
    Set.range x.base ⊆ U ↔ x.base p ∈ U := by
  refine ⟨fun h => h ⟨p, rfl⟩, ?_⟩
  rintro h _ ⟨q, rfl⟩
  rwa [Subsingleton.elim q p]

theorem pow_nsmul {G : Over S} [GrpObj G] {h : ℕ} (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G))
    (hadd : ∀ a b, lev (a + b) = lev a * lev b) (n : ℕ) (c : Fin h ⊕ Fin h → ℤ) : lev (n • c) = lev c ^ n := by
  have h0 : lev 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  induction n with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]

end GlobalTheory.LevTrivOpen

open GlobalTheory.LevCover GlobalTheory.LevTrivOpen in
theorem GlobalTheory.levTriv_locus_open : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → 3 ≤ M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S), (∀ a, (toUnit (Over.mk x₀) ≫ lev a = 1 ↔ ∃ b, a = M • b)) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S), Set.range x.base ⊆ W → ∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = M • b) := by
  intro S _ M t G _ _ h lev hab hM hadd hpow k _ _ x₀ hx₀
  have hu : IsUnit (M : Γ(S, ⊤)) := by
    have := (GlobalTheory.SiegelTor.isUnit_natCast (n := M) (by omega)).map
      (t.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (GlobalTheory.SiegelTor.cycAway M))).inv.hom)
    rwa [map_natCast] at this
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion G (hG := hab) hu
  have hU : ∀ f : 𝟙_ (Over S) ⟶ G, ∃ U : S.Opens, IsClosed (U : Set S) ∧ (f ^ M = 1 → ∀ (k' : Type) [Field k']
      [IsAlgClosed k'] (x : Sp k' ⟶ S), (toUnit (Over.mk x) ≫ f = 1 ↔ Set.range x.base ⊆ U)) := fun f => by
    by_cases hf : f ^ M = 1
    · obtain ⟨U, hUc, HU⟩ := GlobalTheory.TorsionSections.clopenCond_torsion_eq (n := M) (T := 𝟙_ (Over S)) hf (one_pow M)
      refine ⟨U, hUc, fun _ k' _ _ x => ?_⟩
      have := HU (Over.mk x) (toUnit (Over.mk x))
      simp only [MonObj.comp_one] at this
      simpa using this
    · exact ⟨⊤, isClosed_univ, fun h => absurd h hf⟩
  choose Uf hUc HU using hU
  classical
  obtain ⟨κ, _, q, hq⟩ := exists_finite_mod (Fin h ⊕ Fin h → ℤ) (show 0 < M by omega)
  let P : (Fin h ⊕ Fin h → ℤ) → Prop := fun a => ∃ b, a = M • b
  let A : (Fin h ⊕ Fin h → ℤ) → Set S := fun a => {s | s ∈ (Uf (lev a) : Set S) ↔ P a}
  have hAo : ∀ a, IsOpen (A a) := fun a => by
    by_cases hp : P a
    · convert (Uf (lev a)).isOpen using 1
      ext s
      simp only [A, Set.mem_setOf_eq, hp, iff_true, SetLike.mem_coe]
    · convert (hUc (lev a)).isOpen_compl using 1
      ext s
      simp only [A, Set.mem_setOf_eq, hp, iff_false, Set.mem_compl_iff, SetLike.mem_coe]
  have hAq : ∀ a a', q a = q a' → A a = A a' := fun a a' e => by
    obtain ⟨c, rfl⟩ := hq a a' e
    have hl : lev (a + M • c) = lev a := by rw [hadd, pow_nsmul lev hadd, hpow, _root_.mul_one]
    have hP : P (a + M • c) ↔ P a :=
      ⟨fun ⟨b, hb⟩ => ⟨b - c, by rw [smul_sub, ← hb]; abel⟩, fun ⟨b, hb⟩ => ⟨b + c, by rw [hb, smul_add]⟩⟩
    ext s
    simp only [A, Set.mem_setOf_eq, hl, hP]
  let pick : κ → (Fin h ⊕ Fin h → ℤ) := fun c => if hc : ∃ a, q a = c then hc.choose else 0
  have hpick : ∀ a, A a = A (pick (q a)) := fun a => by
    have hc : ∃ a', q a' = q a := ⟨a, rfl⟩
    refine hAq _ _ ?_
    simp only [pick, dif_pos hc]
    exact hc.choose_spec.symm
  refine ⟨⟨⋂ c, A (pick c), isOpen_iInter_of_finite fun c => hAo _⟩, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩
    simp only [TopologicalSpace.Opens.coe_mk, Set.mem_iInter]
    intro c
    show x₀.base p ∈ (Uf (lev (pick c)) : Set S) ↔ P (pick c)
    rw [← range_subset_iff_mem, ← HU _ (hpow _) k x₀]
    exact hx₀ _
  · intro k' _ _ x hx a
    obtain ⟨p⟩ := (inferInstance : Nonempty (Sp k'))
    have h1 := hx ⟨p, rfl⟩
    simp only [TopologicalSpace.Opens.coe_mk, Set.mem_iInter] at h1
    have h2 : x.base p ∈ A a := by rw [hpick]; exact h1 _
    rw [HU _ (hpow a) k' x, range_subset_iff_mem _ _ p]
    exact h2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationOfOrthogonalPerfectPairing
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PoincareKer

theorem mem_fil_of_orth : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] [Nontrivial R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → ∀ y : HdR B, (∀ x ∈ Fil A, φ x y = 0) → y ∈ Fil B := by
  intro hH R _ _ A B _ _ g hA hB hgA hgB P hP φ hφ y hy
  have hL := hP.isLB

  obtain ⟨v, hv, -⟩ := ((_root_.GlobalTheory.abelianDeRham_free_hodge_baseChange hH).2.1 R B g hB hgB).1.1 y

  have horth := _root_.GlobalTheory.PtExt.HodgeOrth.fil_orthogonal hH R A B g hA hB hgA hgB P hL φ hφ
  obtain ⟨j, hj⟩ := _root_.GlobalTheory.PtExt.exists_isChoice R A B P hL

  have hpairZero (h : HdR A) (hh : h ∈ Fil A) : φ h y = h (0 : primDR A) :=
    (hy h hh).trans h.map_zero.symm
  have hc : Cohom (chartsA P) (fv (0 : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _)))) (tanCoc P j v).neg :=
    _root_.GlobalTheory.PtExt.cohom_fv_neg_tanCoc_of_orthogonal hH R A B g hA hB hgA hgB P hL φ hφ horth y v hv 0
      hpairZero 0 (by rw [LinearMap.map_zero]; rfl) j hj
  obtain ⟨k, hk⟩ := hc
  have hk' : IsCob (chartsA P) (tanCoc P j v) k := by
    intro D _ _ D' _ _ ψ x hx
    have e := hk D D' ψ x hx
    have h0 : fv (0 : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) D D' ψ x = 0 := rfl
    simp only [Fn1.add, Fn1.neg, h0, zero_add, neg_neg] at e
    exact e

  obtain ⟨s, hs⟩ := _root_.GlobalTheory.PtExt.exists_isPtGen R (A ⊗ B) A P hL (AbDual.inl A B) hP.zero_right

  obtain ⟨T, hT⟩ := _root_.GlobalTheory.PtExt.exists_isEpsGen_of_isCob R A B P hL v hv.1 j hj s hs k hk'
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_pointwiseGenerator_of_dualNumberLineBundleGenerator R A B P hL v hv.1 T hT
  have htriv := _root_.GlobalTheory.PtExt.triv_pull_of_isPtGen R (A ⊗ B) (A ⊗ epsR R) P hL _ t ht

  have hv1 : v = 1 := hP.ker_right (epsR R) v htriv
  subst hv1
  exact isLieImage_one_iff.mp hv

end GlobalTheory.PoincareKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialBoundaryFamilyPullUnitaryTraitForm
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart

theorem trait_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)} {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] (C : MonoFam Xo c φ R) (hR : GlobalTheory.Mum.Base R) (W : Type) [CommRing W] [IsDomain W]
    [IsLocalRing W] (hW : GlobalTheory.UU.CDVR W) (ϖ : W) (ρ : R →+* W) (hinj : Function.Injective ρ) (hloc : IsLocalHom ρ)
    (w : Fin C.m → ℕ) (u : Fin C.m → Wˣ) (hs : ∀ i, ρ (C.s i) = u i * ϖ ^ w i) :
    ∃ (t : SAB H (Sp W)) (P : PELUnif (maximalIdeal W) t) (e : P.D.toPre.X ≃ₗ[𝓞 E] C.P.D.toPre.X)
      (be : LinearMap.BilinForm ℤ P.D.toPre.X),
      Nonempty (SABMap t C.t (spMap ρ)) ∧
      (∀ κ : Sp (FractionRing W) ⟶ Sp (FractionRing R), κ ≫ jK R = jK W ≫ spMap ρ →
        ∃ tK : SAB H (Sp (FractionRing W)), Nonempty (SABMap tK t (jK W)) ∧
          Nonempty (SABMap tK Xo.univ.t ((κ ≫ C.y) ≫ pullback.fst _ _))) ∧
      be = ∑ i, (w i : ℤ) • pull e.toLinearMap ((l.M' : ℤ) • C.δ i) ∧
      be ∈ levelForms H 1 P.D.toPre.X ∧ IsMonomial P.D.toPre ![ϖ] ![be] ∧
      φ.evalZ be = ∑ i, (w i : ℝ) * φ.evalZ ((l.M' : ℤ) • C.δ i) := by
  obtain ⟨h1, -, h3, h4, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨hdvr, hcomp, -⟩ := hW
  have hWa : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hcomp⟩
  have hI : (maximalIdeal R).map ρ ≤ maximalIdeal W := ((IsLocalRing.local_hom_tfae ρ).out 1 3).1 hloc
  obtain ⟨t', m₀, P', hD, -, -, -, -, hlin, -⟩ := GlobalTheory.ArcDataDescent.exists_pelUnif_pull h3.cubePull h1.polBaseChange
    h4.unifBaseChange h5 hR.1 hWa C.t C.P ρ hinj hI
  let e : P'.D.toPre.X ≃ₗ[𝓞 E] C.P.D.toPre.X := { hD.xe with map_smul' := hlin }
  have he : ∀ y, e y = hD.xe y := fun _ => rfl
  refine ⟨t', P', e, ∑ i, (w i : ℤ) • pull e.toLinearMap ((l.M' : ℤ) • C.δ i), ⟨m₀⟩, ?_, rfl, ?_, ?_, ?_⟩
  · intro κ hκ
    obtain ⟨tKR, ⟨n1⟩, ⟨n2⟩⟩ := C.gen
    obtain ⟨tK, ⟨k⟩⟩ := GlobalTheory.Models.Inhab.exists_pull κ tKR
    obtain ⟨a, -⟩ := sabComp pullCubComp E H _ _ _ C.t tKR tK (jK R) κ n1 k
    rw [hκ] at a
    obtain ⟨b, -⟩ := sabCancel pullCubCancel E H _ _ _ C.t t' tK (spMap ρ) (jK W) m₀ a
    obtain ⟨d, -⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t tKR tK _ κ n2 k
    rw [← Category.assoc] at d
    exact ⟨tK, ⟨b⟩, ⟨d⟩⟩
  · rw [← balForms_eq_levelForms]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (pull_mem _ (Submodule.smul_mem _ _ (C.cone.mem i)))
  · intro y
    obtain ⟨u0, n, hn, hc⟩ := C.mono (hD.xe y)
    obtain ⟨u', hu'⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD y _ hc
    refine ⟨u' * Units.map ρ.toMonoidHom u0 * ∏ i, u i ^ n i, fun _ => ∑ i, w i * n i, fun j => ?_, ?_⟩
    · fin_cases j
      show (∑ i, (w i : ℤ) • pull e.toLinearMap ((l.M' : ℤ) • C.δ i)) y y = 2 * ((∑ i, w i * n i : ℕ) : ℤ)
      rw [LinearMap.sum_apply, LinearMap.sum_apply]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h2 : ((l.M' : ℤ) • C.δ i) (hD.xe y) (hD.xe y) = 2 * n i := hn i
      rw [LinearMap.smul_apply, LinearMap.smul_apply, pull_apply]
      rw [show (e.toLinearMap y) = hD.xe y from rfl, h2]
      simp only [smul_eq_mul]; ring
    · convert hu' using 1
      simp only [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_prod, map_pow, hs, Units.val_mul,
        Units.coe_map, Units.coe_prod, Units.val_pow_eq_pow_val, mul_pow, Finset.prod_mul_distrib,
        ← pow_mul, Finset.prod_pow_eq_pow_sum, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
      ring
  · have hsum : (∑ i, (w i : ℤ) • pull e.toLinearMap ((l.M' : ℤ) • C.δ i)) =
        pull e.toLinearMap (∑ i, (w i : ℤ) • ((l.M' : ℤ) • C.δ i)) := by
      ext a b; simp [LinearMap.sum_apply, pull_apply]
    rw [hsum, evalZ_pull φ e.surjective]
    have hl := C.cone.linearOn_smul l.M' (fun i => (w i : ℝ)) (fun i => Nat.cast_nonneg _)
    refine Eq.trans ?_ hl
    unfold InvFun.evalZ
    congr 1
    funext a b
    simp [LinearMap.sum_apply]

end GlobalTheory.UChart

namespace GlobalTheory.UChart

theorem pull_trait : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (ψ : R →+* W), Function.Injective ψ → IsLocalHom ψ → ∀ (ϖ : W), Irreducible ϖ → ∀ (w : Fin C.m → ℕ), (∀ i, Associated (ψ (C.s i)) (ϖ ^ w i)) → ∀ κ : Sp (FractionRing W) ⟶ Sp (FractionRing R), κ ≫ jK R = jK W ≫ spMap ψ → ∃ (t : SAB H (Sp W)) (tK : SAB H (Sp (FractionRing W))) (P : PELUnif (maximalIdeal W) t), Nonempty (SABMap tK t (jK W)) ∧ Nonempty (SABMap tK Xo.univ.t ((κ ≫ C.y) ≫ pullback.fst _ _)) ∧ ∃ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] ∧ φ.evalZ be = ∑ i, (w i : ℝ) * φ.evalZ ((l.M' : ℤ) • C.δ i) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hR C W _ _ _ hW ψ hinj hloc ϖ _ w hw κ hκ
  choose v hv using hw
  obtain ⟨t, P, e, be, -, htK, -, hbe, hmon, hev⟩ :=
    trait_pull C hR W hW ϖ ψ hinj hloc w (fun i => (v i)⁻¹) (fun i => by rw [← hv i, mul_left_comm, Units.inv_mul, _root_.mul_one])
  obtain ⟨tK, h1, h2⟩ := htK κ hκ
  exact ⟨t, tK, P, h1, h2, be, hbe, hmon, hev⟩

end GlobalTheory.UChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastUnitLocusOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnitLocus

theorem isUnit_of_basicOpen_eq_top' {Y : Scheme.{0}} (s : Γ(Y, ⊤)) (h : Y.basicOpen s = ⊤) : IsUnit s :=
  Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => (Y.mem_basicOpen _ x hx).1 (h.ge hx)

theorem natCast_unit_locus (S' : Scheme.{0}) (d : ℕ) : ∃ U : S'.Opens,
    (∀ V : S'.Opens, V ≤ U → IsUnit ((d : ℕ) : Γ(V.toScheme, ⊤))) ∧
    ∀ (T : Scheme.{0}) (g : T ⟶ S'), IsUnit ((d : ℕ) : Γ(T, ⊤)) → Set.range g.base ⊆ (U : Set S') := by
  refine ⟨S'.basicOpen ((d : ℕ) : Γ(S', ⊤)), ?_, ?_⟩
  · intro V hV
    apply isUnit_of_basicOpen_eq_top'
    have e := Scheme.preimage_basicOpen_top V.ι ((d : ℕ) : Γ(S', ⊤))
    rw [map_natCast] at e
    rw [← e, eq_top_iff]
    intro x _
    show V.ι.base x ∈ S'.basicOpen _
    exact hV (show V.ι x ∈ (V : Set S') by rw [← Scheme.Opens.range_ι V]; exact ⟨x, rfl⟩)
  · intro T g hd
    rintro _ ⟨x, rfl⟩
    have e := Scheme.preimage_basicOpen_top g ((d : ℕ) : Γ(S', ⊤))
    rw [map_natCast, T.basicOpen_of_isUnit hd] at e
    have hx : x ∈ g ⁻¹ᵁ S'.basicOpen ((d : ℕ) : Γ(S', ⊤)) := by rw [e]; trivial
    exact hx

end GlobalTheory.UnitLocus
end

