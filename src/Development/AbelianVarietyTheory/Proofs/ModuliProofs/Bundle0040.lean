module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteMarkedDataInGenus
section
namespace GlobalTheory.MarkedGenus

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem exists_fin_representatives {α β : Type*} [Finite β] (c : α → β) :
    ∃ (r : ℕ) (g : Fin r → α), ∀ a, ∃ j, c (g j) = c a := by
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin (Set.range c)
  refine ⟨r, fun j => (e.symm j).2.choose, fun a => ⟨e ⟨c a, a, rfl⟩, ?_⟩⟩
  rw [(e.symm (e ⟨c a, a, rfl⟩)).2.choose_spec, Equiv.symm_apply_apply]

theorem finite_linearMap {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [Module.Finite R M] [Finite N] : Finite (M →ₗ[R] N) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  refine Finite.of_injective (fun φ : M →ₗ[R] N => fun x : (s : Set M) => φ x) ?_
  intro φ ψ h
  exact LinearMap.ext_on hs (fun x hx => congrFun h ⟨x, hx⟩)

theorem finite_quotient_nsmul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite ℤ R] [Module.Finite R M] {k : ℕ} (hk : 0 < k) :
    Finite (M ⧸ LinearMap.range (k • (LinearMap.id : M →ₗ[R] M))) := by
  set P := LinearMap.range (k • (LinearMap.id : M →ₗ[R] M))
  have hfin : Module.Finite ℤ (M ⧸ P) := Module.Finite.trans R (M ⧸ P)
  have hfg : AddGroup.FG (M ⧸ P) := Module.Finite.iff_addGroup_fg.mp hfin
  refine AddCommGroup.finite_of_fg_isAddTorsion _ (fun q => ?_)
  refine (isOfFinAddOrder_iff_nsmul_eq_zero).mpr ⟨k, hk, ?_⟩
  induction q using Submodule.Quotient.induction_on with
  | H m =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨m, by simp⟩

private lemma match_mod_lemma {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {k n : ℕ} (Dr : Fin n → Datum H) {A B : Datum H} (j1 j2 : Fin n)
    (e1 : A.La ≃ₗ[𝓞 E] (Dr j1).La) (e2 : B.La ≃ₗ[𝓞 E] (Dr j2).La)
    (he1 : ∀ x y, (Dr j1).EF (e1 x) (e1 y) = A.EF x y) (he2 : ∀ x y, (Dr j2).EF (e2 x) (e2 y) = B.EF x y)
    (fA : D.La →ₗ[𝓞 E] A.La) (fB : D.La →ₗ[𝓞 E] B.La)
    (h : (⟨j1, (LinearMap.range (k • (LinearMap.id : (Dr j1).La →ₗ[𝓞 E] (Dr j1).La))).mkQ.comp
        (e1.toLinearMap.comp fA)⟩ :
        Σ j : Fin n, D.La →ₗ[𝓞 E] ((Dr j).La ⧸ LinearMap.range (k • (LinearMap.id : (Dr j).La →ₗ[𝓞 E] (Dr j).La)))) =
      ⟨j2, (LinearMap.range (k • (LinearMap.id : (Dr j2).La →ₗ[𝓞 E] (Dr j2).La))).mkQ.comp
        (e2.toLinearMap.comp fB)⟩) :
    ∃ e : B.La ≃ₗ[𝓞 E] A.La, (∀ x y, A.EF (e x) (e y) = B.EF x y) ∧ ∀ x, ∃ y, e (fB x) = fA x + k • y := by
  obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp h
  have hm := eq_of_heq hh
  refine ⟨e2.trans e1.symm, fun x y => ?_, fun x => ?_⟩
  · rw [← he1]
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, he2]
  · have hx := LinearMap.congr_fun hm x
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe] at hx
    rw [Submodule.Quotient.eq] at hx
    obtain ⟨z, hz⟩ := hx
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at hz
    refine ⟨-(e1.symm z), e1.injective ?_⟩
    have h2 : e2 (fB x) = e1 (fA x) - k • z := by rw [hz]; abel
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, map_add (f := _), map_neg, map_nsmul, h2,
      smul_neg, sub_eq_add_neg]

theorem finite_marked_data_in_genus :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (k : ℕ) (ζ : ℂ), 0 < k → ∃ (r : ℕ) (Di : Fin r → Datum H) (fi : ∀ i, ℕ → D.La →ₗ[𝓞 E] (Di i).La) (νi : Fin r → ℕ → ℤ), (∀ i, ((Di i).p = D.p ∧ (Di i).q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, fi i (n * m) x = fi i n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, fi i n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = fi i n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ (Di i).EF (fi i n x) (fi i n x') - νi i n * D.EF x x') ∧ ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (νi i k : ℂ) / k)) ∧ ∀ (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') → ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν k : ℂ) / k) → ∃ (i : Fin r) (e : D'.La ≃ₗ[𝓞 E] (Di i).La), (∀ x y, (Di i).EF (e x) (e y) = D'.EF x y) ∧ ∀ x, ∃ y, e (f k x) = fi i k x + k • y := by
  intro E _ _ _ H D k ζ hk
  obtain ⟨n, Dr, hDr, hcls⟩ := GlobalTheory.DatumClasses.finite_data_of_signature E H D.p D.q
  let Q : Fin n → Type := fun j =>
    (Dr j).La ⧸ LinearMap.range (k • (LinearMap.id : (Dr j).La →ₗ[𝓞 E] (Dr j).La))
  have hQ : ∀ j, Finite (D.La →ₗ[𝓞 E] Q j) := fun j => by
    have := D.fin
    have := (Dr j).fin
    have : Finite (Q j) := finite_quotient_nsmul hk
    exact finite_linearMap
  let Cond : (D' : Datum H) → (ℕ → D.La →ₗ[𝓞 E] D'.La) → (ℕ → ℤ) → Prop := fun D' f ν =>
    (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧
      (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧
      ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') ∧
    ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν k : ℂ) / k)
  let α := {a : Σ D' : Datum H, (ℕ → D.La →ₗ[𝓞 E] D'.La) × (ℕ → ℤ) // Cond a.1 a.2.1 a.2.2}
  choose jf ef hef using fun a : α => hcls a.1.1 a.2.1.1 a.2.1.2.1
  let c : α → Σ j : Fin n, (D.La →ₗ[𝓞 E] Q j) := fun a =>
    ⟨jf a, (LinearMap.range (k • (LinearMap.id : (Dr (jf a)).La →ₗ[𝓞 E] (Dr (jf a)).La))).mkQ.comp
      ((ef a).toLinearMap.comp (a.1.2.1 k))⟩
  obtain ⟨r, g, hg⟩ := exists_fin_representatives c
  refine ⟨r, fun i => (g i).1.1, fun i => (g i).1.2.1, fun i => (g i).1.2.2, fun i => (g i).2, ?_⟩
  intro D' f ν hc hζ
  obtain ⟨i, hi⟩ := hg ⟨⟨D', f, ν⟩, hc, hζ⟩
  exact ⟨i, match_mod_lemma Dr _ _ (ef (g i)) (ef ⟨⟨D', f, ν⟩, hc, hζ⟩) (hef (g i)) (hef _) _ _ hi⟩

end GlobalTheory.MarkedGenus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankSymmAntilinearCommCMLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KS.DimPEL

theorem exists_sum_eigen {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module ℂ V]
    (F : 𝓞 E →+* Module.End ℂ V) (v : V) :
    ∃ w : (E →+* ℂ) → V, (∀ τ (a : 𝓞 E), F a (w τ) = τ (a : E) • w τ) ∧ v = ∑ τ, w τ := by
  classical
  let B := canonicalEmbedding.latticeBasis E
  let Φ : ((E →+* ℂ) → ℂ) →ₗ[ℂ] Module.End ℂ V := B.constr ℂ (fun i => F (RingOfIntegers.basis E i))
  have hB : ∀ i, B i = canonicalEmbedding E ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
    intro i
    simp [B, canonicalEmbedding.latticeBasis_apply, integralBasis_apply]
  have h1 : ∀ a : 𝓞 E, Φ (canonicalEmbedding E (a : E)) = F a := by
    intro a
    let L₁ : 𝓞 E →ₗ[ℤ] Module.End ℂ V :=
      (Φ.toAddMonoidHom.comp (((canonicalEmbedding E).comp (algebraMap (𝓞 E) E)).toAddMonoidHom)).toIntLinearMap
    let L₂ : 𝓞 E →ₗ[ℤ] Module.End ℂ V := F.toAddMonoidHom.toIntLinearMap
    have : L₁ = L₂ := by
      apply (RingOfIntegers.basis E).ext
      intro i
      change Φ (canonicalEmbedding E ((RingOfIntegers.basis E i : 𝓞 E) : E)) = F _
      rw [← hB]
      simp [Φ]
    exact LinearMap.congr_fun this a
  have h2 : ∀ (a : 𝓞 E) (x : (E →+* ℂ) → ℂ), Φ (canonicalEmbedding E (a : E) * x) = F a * Φ x := by
    intro a x
    have : Φ ∘ₗ LinearMap.mulLeft ℂ (canonicalEmbedding E (a : E)) = LinearMap.mulLeft ℂ (F a) ∘ₗ Φ := by
      apply B.ext
      intro i
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
      rw [hB, h1, ← map_mul F, ← h1, ← map_mul (canonicalEmbedding E)]
      rfl
    exact LinearMap.congr_fun this x
  refine ⟨fun τ => Φ (Pi.single τ 1) v, fun τ a => ?_, ?_⟩
  · have : canonicalEmbedding E (a : E) * Pi.single τ 1 = τ (a : E) • (Pi.single τ 1 : (E →+* ℂ) → ℂ) := by
      ext σ
      by_cases h : σ = τ
      · subst h; simp [canonicalEmbedding.apply_at]
      · simp [Pi.single_eq_of_ne h]
    rw [← Module.End.mul_apply, ← h2, this, map_smul, LinearMap.smul_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← LinearMap.sum_apply, ← map_sum, Finset.univ_sum_single]
      have := h1 1
      have e : Φ 1 = 1 := by simpa using this
      change v = Φ 1 v
      rw [e]
      rfl

theorem conj_eq_neg {z : ℂ} {d : ℕ} (h : z ^ 2 = -(d : ℂ)) (hd : 0 < d) : starRingEnd ℂ z = -z := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [sq] at hre him
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have : z.re = 0 := by
    have h3 : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact h4
    · rw [h4] at hre; nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [this]

abbrev Eig {E : Type} [Field E] [NumberField E] {g : ℕ} (F : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (τ : E →+* ℂ) :
    Submodule ℂ (Fin g → ℂ) := ⨅ a : 𝓞 E, Module.End.eigenspace (F a) (τ (a : E))

theorem mem_Eig {E : Type} [Field E] [NumberField E] {g : ℕ} (F : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (τ : E →+* ℂ)
    (v : Fin g → ℂ) : v ∈ Eig F τ ↔ ∀ a : 𝓞 E, F a v = τ (a : E) • v := by
  simp [Eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

theorem theta_mem {E : Type} [Field E] [NumberField E] {g : ℕ} (F : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (τ : E →+* ℂ)
    (Θ : Matrix (Fin g) (Fin g) ℂ) (hΘ : ∀ a, Comm Θ (F a)) (v : Fin g → ℂ) (hv : v ∈ Eig F τ) :
    Θ.mulVec (star v) ∈ Eig F (ComplexEmbedding.conjugate τ) := by
  rw [mem_Eig] at hv ⊢
  intro a
  rw [hΘ a v, hv, star_smul, Matrix.mulVec_smul, ComplexEmbedding.conjugate_coe_eq]
  rfl

theorem finrank_symm_comm_le (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g p q : ℕ) (ρ₀ : ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (F : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (S : Submodule ℂ (Matrix (Fin g) (Fin g) ℂ))
    (hρ : ρ₀ ^ 2 = -(H.d : ℂ)) (_hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hdim : ∀ τ : 𝓞 E →+* ℂ, Module.finrank ℂ ↥(⨅ a, Module.End.eigenspace (F a) (τ a)) = if τ H.rt = ρ₀ then p else q)
    (hS : ∀ Θ ∈ S, IsSymm Hm Θ ∧ ∀ a, Comm Θ (F a)) :
    Module.finrank ℂ S ≤ Module.finrank ℚ E / 2 * p * q := by
  classical
  have hd : 0 < H.d := H.d_prime.pos
  have hρ0 : ρ₀ ≠ 0 := by
    intro h
    rw [h] at hρ
    have : (H.d : ℂ) = 0 := by simpa using hρ
    exact hd.ne' (by exact_mod_cast this)
  have hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    intro τ
    have := congrArg (τ.comp (algebraMap (𝓞 E) E)) H.rt_sq
    simpa using this
  have hconj : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate τ (H.rt : E) = - τ (H.rt : E) := by
    intro τ
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact conj_eq_neg (hsq τ) hd
  have hne : ∀ τ : E →+* ℂ, τ (H.rt : E) = ρ₀ → ComplexEmbedding.conjugate τ (H.rt : E) ≠ ρ₀ := by
    intro τ h h'
    rw [hconj, h] at h'
    apply hρ0
    linear_combination (-1/2 : ℂ) * h'
  have heq : ∀ τ : E →+* ℂ, τ (H.rt : E) ≠ ρ₀ → ComplexEmbedding.conjugate τ (H.rt : E) = ρ₀ := by
    intro τ h
    rw [hconj]
    have : τ (H.rt : E) ^ 2 = ρ₀ ^ 2 := by rw [hsq, hρ]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h1 | h1
    · exact absurd h1 h
    · rw [h1, neg_neg]
  have hdim' : ∀ τ : E →+* ℂ, Module.finrank ℂ (Eig F τ) = if τ (H.rt : E) = ρ₀ then p else q :=
    fun τ => hdim (τ.comp (algebraMap (𝓞 E) E))
  let T := {τ : E →+* ℂ // τ (H.rt : E) = ρ₀}
  have hcard : Fintype.card T ≤ Module.finrank ℚ E / 2 := by
    have h1 : Fintype.card T ≤ Fintype.card {τ : E →+* ℂ // ¬ τ (H.rt : E) = ρ₀} := by
      refine Fintype.card_le_of_injective
        (fun τ => ⟨ComplexEmbedding.conjugate τ.1, hne τ.1 τ.2⟩) ?_
      intro σ τ h
      have h2 : ComplexEmbedding.conjugate σ.1 = ComplexEmbedding.conjugate τ.1 := congrArg Subtype.val h
      exact Subtype.ext (star_injective h2)
    rw [Fintype.card_subtype_compl, NumberField.Embeddings.card] at h1
    have h3 : Fintype.card T ≤ Fintype.card (E →+* ℂ) := Fintype.card_subtype_le _
    rw [NumberField.Embeddings.card] at h3
    change Fintype.card T ≤ _ - Fintype.card T at h1
    omega
  have hp : ∀ τ : T, Module.finrank ℂ (Eig F τ.1) = p := fun τ => by rw [hdim', if_pos τ.2]
  have hq : ∀ τ : T, Module.finrank ℂ (Eig F (ComplexEmbedding.conjugate τ.1)) = q :=
    fun τ => by rw [hdim', if_neg (hne τ.1 τ.2)]
  let b : ∀ τ : T, Module.Basis (Fin p) ℂ (Eig F τ.1) := fun τ => Module.finBasisOfFinrankEq ℂ _ (hp τ)
  let Ψ : S →ₗ[ℂ] (∀ τ : T, Fin p → Eig F (ComplexEmbedding.conjugate τ.1)) :=
    { toFun := fun Θ τ i => ⟨Θ.1.mulVec (star (b τ i : Fin g → ℂ)), theta_mem F τ.1 Θ.1 (hS Θ.1 Θ.2).2 _ (b τ i).2⟩
      map_add' := fun Θ Θ' => by
        funext τ i
        apply Subtype.ext
        simp [Matrix.add_mulVec]
      map_smul' := fun c Θ => by
        funext τ i
        apply Subtype.ext
        simp [Matrix.smul_mulVec] }
  have hinj : Function.Injective Ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro Θ hΘ
    obtain ⟨hs, hc⟩ := hS Θ.1 Θ.2
    have k1 : ∀ τ : E →+* ℂ, τ (H.rt : E) = ρ₀ → ∀ v ∈ Eig F τ, Θ.1.mulVec (star v) = 0 := by
      intro τ hτ v hv
      have hb : ∀ i, Θ.1.mulVec (star (b ⟨τ, hτ⟩ i : Fin g → ℂ)) = 0 := fun i =>
        congrArg Subtype.val (congrFun (congrFun hΘ ⟨τ, hτ⟩) i)
      have e := congrArg Subtype.val ((b ⟨τ, hτ⟩).sum_repr ⟨v, hv⟩)
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at e
      rw [← e, star_sum, Matrix.mulVec_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [star_smul, Matrix.mulVec_smul, hb, smul_zero]
    have k2 : ∀ τ : E →+* ℂ, ∀ v ∈ Eig F τ, Θ.1.mulVec (star v) = 0 := by
      intro τ v hv
      by_cases hτ : τ (H.rt : E) = ρ₀
      · exact k1 τ hτ v hv
      · by_contra h0
        have h1 := hpos _ h0
        rw [hs v, k1 _ (heq τ hτ) _ (theta_mem F τ Θ.1 hc v hv)] at h1
        simp [hermForm] at h1
    have k3 : ∀ v : Fin g → ℂ, Θ.1.mulVec (star v) = 0 := by
      intro v
      obtain ⟨w, hw, rfl⟩ := exists_sum_eigen F v
      rw [star_sum, Matrix.mulVec_sum]
      exact Finset.sum_eq_zero fun τ _ => k2 τ _ ((mem_Eig F τ _).2 (hw τ))
    apply Subtype.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    have := k3 (star v)
    rw [star_star] at this
    simpa using this
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi_fintype] at hle
  simp only [Module.finrank_pi_fintype, hq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
  calc Module.finrank ℂ S ≤ Fintype.card T * (p * q) := hle
    _ ≤ Module.finrank ℚ E / 2 * (p * q) := Nat.mul_le_mul_right _ hcard
    _ = _ := by ring

end GlobalTheory.KS.DimPEL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeometricallyConnectedOfIsPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.SemiAbelianDescent

theorem exists_section {Z : Scheme.{0}} {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (f : Z ⟶ Spec (CommRingCat.of Ω)) [IsIntegralHom f] [Surjective f] :
    ∃ s : Spec (CommRingCat.of Ω) ⟶ Z, s ≫ f = 𝟙 _ := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  have : Nonempty Z := ⟨(f.surjective (Nonempty.some inferInstance)).choose⟩
  obtain ⟨z, -, hz⟩ := (isClosed_univ (X := Z)).exists_closed_singleton Set.univ_nonempty
  rw [isClosed_singleton_iff_isClosedImmersion] at hz
  set g : Spec (Z.residueField z) ⟶ Spec (CommRingCat.of Ω) := Z.fromSpecResidueField z ≫ f with hg
  have : IsIntegralHom g := inferInstance
  have : IsIso (Spec.preimage g) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine IsAlgClosed.ringHom_bijective_of_isIntegral _ ?_
    rw [← IsIntegralHom.SpecMap_iff, Spec.map_preimage]
    infer_instance
  refine ⟨Spec.map (inv (Spec.preimage g)) ≫ Z.fromSpecResidueField z, ?_⟩
  calc (Spec.map (inv (Spec.preimage g)) ≫ Z.fromSpecResidueField z) ≫ f
      = Spec.map (inv (Spec.preimage g)) ≫ Spec.map (Spec.preimage g) := by
        rw [Category.assoc, Spec.map_preimage]
    _ = 𝟙 _ := by rw [← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id]

theorem exists_lift {X X' : Scheme.{0}} (π : X ⟶ X') [IsIntegralHom π] [Surjective π]
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (p : Spec (CommRingCat.of Ω) ⟶ X') :
    ∃ q : Spec (CommRingCat.of Ω) ⟶ X, q ≫ π = p := by
  obtain ⟨s, hs⟩ := exists_section (pullback.snd π p)
  refine ⟨s ≫ pullback.fst π p, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]

private theorem isClosed_range_diagonal_of_surjective_universallyClosed {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S) [Surjective j]
    {P : Scheme.{0}} (m : P ⟶ Limits.pullback f f) [UniversallyClosed m] (d : X ⟶ P)
    (hd : IsClosed (Set.range d)) (hc : d ≫ m = j ≫ pullback.diagonal f) :
    IsClosed (Set.range (pullback.diagonal f)) := by
  have key : Set.range (pullback.diagonal f) = m '' Set.range d := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := j.surjective y
      exact ⟨d x, ⟨x, rfl⟩, by rw [← Scheme.Hom.comp_apply, hc, Scheme.Hom.comp_apply]⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨j x, by rw [← Scheme.Hom.comp_apply, ← hc, Scheme.Hom.comp_apply]⟩
  rw [key]
  exact m.isClosedMap _ hd

theorem isSeparated_of_comp {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S)
    [Surjective j] [UniversallyClosed j] [IsSeparated (j ≫ f)] : IsSeparated f := by
  have hm := MorphismProperty.pullbackMap (P := @UniversallyClosed) (f := j ≫ f) (g := j ≫ f)
    (f' := f) (g' := f) (i₁ := j) (i₂ := j) ‹UniversallyClosed j› ‹UniversallyClosed j› rfl rfl
  have hcl := isClosed_range_diagonal_of_surjective_universallyClosed j f
    (pullback.map (j ≫ f) (j ≫ f) f f j j (𝟙 _) (Category.comp_id _) (Category.comp_id _)) (pullback.diagonal (j ≫ f))
    (pullback.diagonal (j ≫ f)).isClosedEmbedding.isClosed_range (pullback.comp_diagonal j f).symm
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hcl⟩

theorem quasiCompact_of_comp {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S)
    [Surjective j] [QuasiCompact (j ≫ f)] : QuasiCompact f := by
  refine ⟨fun U hU hU' => ?_⟩
  have h := (QuasiCompact.isCompact_preimage (f := j ≫ f) U hU hU').image j.continuous
  convert h using 1
  ext x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := j.surjective x
    exact ⟨y, by simpa using hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem geometricallyConnected_of_isPullback {X X' Y Y' : Scheme.{0}} {π : X ⟶ X'} [IsIntegralHom π]
    [Surjective π] {f : Y ⟶ X} {f' : Y' ⟶ X'} {φ : Y ⟶ Y'} (h : IsPullback φ f f' π)
    [GeometricallyConnected f] : GeometricallyConnected f' := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y => ?_⟩
  let ιK : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  obtain ⟨q, hq⟩ := exists_lift π (ιK ≫ y)
  have hA : ConnectedSpace ↥(pullback f q) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  have hιK : Surjective ιK := ⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  let M := (IsPullback.paste_horiz (IsPullback.of_hasPullback f q) h).isoPullback.hom ≫
    (pullback.congrHom rfl hq).hom ≫ (pullbackLeftPullbackSndIso f' y ιK).inv ≫
      pullback.fst (pullback.snd f' y) ιK
  have hM : Surjective M := by dsimp only [M]; infer_instance
  exact M.surjective.connectedSpace M.continuous

theorem isSemiAbelian_descends {X X' : Scheme.{0}} {π : X ⟶ X'} {G : Over X} [GrpObj G] {G' : Over X'}
    [GrpObj G'] [IsCommMonObj G'] {φ : G.left ⟶ G'.left} [IsIntegralHom π] [Surjective π]
    (h : IsGrpPullback G G' π φ) [Smooth G'.hom] (hG : IsSemiAbelian G) : IsSemiAbelian G' := by
  obtain ⟨hc, hsm, hsep, hqc, hgc, hfib⟩ := hG
  have hpb : IsPullback φ G.hom G'.hom π := h.1
  have hφi : IsIntegralHom φ := MorphismProperty.of_isPullback hpb.flip ‹IsIntegralHom π›
  have hφs : Surjective φ := MorphismProperty.of_isPullback hpb.flip ‹Surjective π›
  have hw : φ ≫ G'.hom = G.hom ≫ π := hpb.w
  have hsep' : IsSeparated G'.hom := by
    have : IsSeparated (φ ≫ G'.hom) := by rw [hw]; infer_instance
    exact isSeparated_of_comp φ G'.hom
  have hqc' : QuasiCompact G'.hom := by
    have : QuasiCompact (φ ≫ G'.hom) := by rw [hw]; infer_instance
    exact quasiCompact_of_comp φ G'.hom
  have hgc' : GeometricallyConnected G'.hom := geometricallyConnected_of_isPullback hpb
  refine ⟨‹_›, ‹_›, hsep', hqc', hgc', ?_⟩
  intro Ω _ _ p
  obtain ⟨q, hq⟩ := exists_lift π p
  obtain ⟨T⟩ := hfib Ω q
  have h1 := isGrpPullback_pullback G q
  have h2 := IsGrpPullback.comp h1 h
  have h3 := isGrpPullback_pullback G' p
  obtain ⟨e, he, -⟩ := grpPullback_iso (h2.congr hq rfl) h3
  exact ⟨torusExtOfIso e T⟩

theorem main : ∀ (X X' : Scheme.{0}) (π : X ⟶ X') (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G.left ⟶ G'.left), IsIntegralHom π → Surjective π → IsGrpPullback G G' π φ → Smooth G'.hom → IsSemiAbelian G → IsSemiAbelian G' ∧ ((∃ U : X.Opens, (U : Set X) = abLocus G ∧ IsProper (G.hom ∣_ U)) → (∃ U : X'.Opens, (U : Set X') = abLocus G' ∧ IsProper (G'.hom ∣_ U))) := by
  intro X X' π G _ G' _ _ φ hi hs h hsm hG
  have hG' : IsSemiAbelian G' := isSemiAbelian_descends h hG
  refine ⟨hG', ?_⟩
  rintro ⟨U, hU, hP⟩
  have hloc : ∀ x, π x ∈ abLocus G' ↔ x ∈ abLocus G := abLocus_pullback abLocusOne hG' h.1
  have hV : IsOpen (abLocus G') := by
    have hc : (abLocus G')ᶜ = π '' (U : Set X)ᶜ := by
      ext y
      obtain ⟨x, rfl⟩ := π.surjective y
      constructor
      · intro hy
        refine ⟨x, ?_, rfl⟩
        rw [Set.mem_compl_iff, hU, ← hloc]
        exact hy
      · rintro ⟨x', hx', hxx⟩
        rw [Set.mem_compl_iff, ← hxx, hloc, ← hU]
        exact hx'
    rw [← isClosed_compl_iff, hc]
    exact π.isClosedMap _ U.isOpen.isClosed_compl
  let V' : X'.Opens := ⟨abLocus G', hV⟩
  have hpre : π ⁻¹ᵁ V' = U := by
    ext x
    change π x ∈ abLocus G' ↔ x ∈ (U : Set X)
    rw [hU, hloc]
  rw [← hpre] at hP
  have hpb : IsPullback φ G.hom G'.hom π := h.1
  have hw : φ ≫ G'.hom = G.hom ≫ π := hpb.w
  have hφs : Surjective φ := MorphismProperty.of_isPullback hpb.flip ‹Surjective π›
  have hle : G.hom ⁻¹ᵁ (π ⁻¹ᵁ V') ≤ φ ⁻¹ᵁ (G'.hom ⁻¹ᵁ V') := by
    intro x hx
    change G'.hom (φ x) ∈ V'
    rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
    exact hx
  let a := φ.resLE (G'.hom ⁻¹ᵁ V') (G.hom ⁻¹ᵁ (π ⁻¹ᵁ V')) hle
  have heq : a ≫ (G'.hom ∣_ V') = (G.hom ∣_ (π ⁻¹ᵁ V')) ≫ (π ∣_ V') := by
    rw [← cancel_mono V'.ι]
    simp only [a, Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
      Scheme.Hom.resLE_comp_ι_assoc, hw]
  have ha : Surjective a := by
    constructor
    intro z
    obtain ⟨w, hw'⟩ := φ.surjective ((G'.hom ⁻¹ᵁ V').ι z)
    have hz : (G'.hom ⁻¹ᵁ V').ι z ∈ ((G'.hom ⁻¹ᵁ V' : G'.left.Opens) : Set G'.left) := by
      rw [← Scheme.Opens.range_ι (G'.hom ⁻¹ᵁ V')]
      exact ⟨z, rfl⟩
    have hm : w ∈ Set.range (G.hom ⁻¹ᵁ (π ⁻¹ᵁ V')).ι := by
      rw [Scheme.Opens.range_ι]
      change π (G.hom w) ∈ V'
      rw [← Scheme.Hom.comp_apply, ← hw, Scheme.Hom.comp_apply, hw']
      exact hz
    obtain ⟨w', rfl⟩ := hm
    refine ⟨w', (G'.hom ⁻¹ᵁ V').ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply, hw']
  have hsep : IsSeparated G'.hom := hG'.separated
  have hcomp : UniversallyClosed (a ≫ (G'.hom ∣_ V')) := by
    rw [heq]
    infer_instance
  have huc : UniversallyClosed (G'.hom ∣_ V') := UniversallyClosed.of_comp_surjective a _
  exact ⟨V', rfl, by constructor⟩

end GlobalTheory.SemiAbelianDescent
end

