module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.QzInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.DualGen
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.dualGen :
    ∀ (l : ℕ) [Fact l.Prime] (D : Type) [AddCommGroup D] [Module ℤ_[l] D] (r : ℕ), (∀ x : D, ∃ k : ℕ, (l : ℤ_[l]) ^ k • x = 0) → CardLe (Submodule.torsionBy ℤ_[l] D (l : ℤ_[l])) (l ^ r) →
      Tower.GenLE ℤ_[l] (D →ₗ[ℤ_[l]] QZ l) r := by
  intro l _ D _ _ r htors hcard
  classical
  obtain ⟨f, hf⟩ := embedQZ l D r htors hcard
  haveI := PropA.qzInj l
  refine ⟨Fintype.linearCombination ℤ_[l] (fun i => (LinearMap.proj i).comp f), ?_⟩
  intro φ
  obtain ⟨ψ, hψ⟩ := Module.Injective.out (R := ℤ_[l]) (Q := QZ l) f hf φ
  choose c hc using fun i => qzEnd l (ψ.comp (LinearMap.single ℤ_[l] (fun _ : Fin r => QZ l) i))
  refine ⟨c, ?_⟩
  ext d
  rw [Fintype.linearCombination_apply, ← hψ d]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  conv_rhs => rw [← Finset.univ_sum_single (f d)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 := hc i (f d i)
  simp only [LinearMap.comp_apply, LinearMap.single_apply] at h1
  exact h1.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IdxTwo
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem idxTwo_conj {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (U : Subgroup Γ) (S : Set Γ)
    (σ : Γ) (n : ℕ) (hc : ∀ u ∈ U, σ⁻¹ * u * σ ∈ U) (h2 : σ * σ ∈ U) (hS : ∀ s ∈ S, σ⁻¹ * s * σ ∈ S)
    (h : CardLe {φ : CharOff U S 2 // ∀ u u' : U, u'.1 = σ⁻¹ * u.1 * σ → φ.1 u' = φ.1 u} n) :
    CardLe (CharOff U S 2) (n ^ 2) := by
  let c : U → U := fun u => ⟨σ⁻¹ * u.1 * σ, hc u.1 u.2⟩
  have hcc : Continuous c :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hcm : ∀ a b : U, c (a * b) = c a * c b := by
    intro a b
    apply Subtype.ext
    show σ⁻¹ * (a.1 * b.1) * σ = σ⁻¹ * a.1 * σ * (σ⁻¹ * b.1 * σ)
    group
  have hmem : ∀ φ : CharOff U S 2, (fun u => φ.1 u + φ.1 (c u)) ∈ CharOff U S 2 := by
    intro φ
    obtain ⟨hl, hadd, hz⟩ := φ.2
    refine ⟨hl.add (hl.comp_continuous hcc), fun a b => ?_, fun u hu => ?_⟩
    · simp only [hcm, hadd]
      ring
    · simp only [hz u hu, hz (c u) (hS _ hu), add_zero]
  let f : CharOff U S 2 →+ CharOff U S 2 :=
    { toFun := fun φ => ⟨_, hmem φ⟩
      map_zero' := by
        apply Subtype.ext
        funext u
        simp
      map_add' := by
        intro a b
        apply Subtype.ext
        funext u
        simp only [Submodule.coe_add, Pi.add_apply]
        ring }
  have hff : ∀ x, f (f x) = 0 := by
    intro φ
    obtain ⟨-, hadd, -⟩ := φ.2
    have h1 : φ.1 1 = 0 := by
      have := hadd 1 1
      rw [mul_one] at this
      linear_combination -this
    have hcc' : ∀ u, φ.1 (c (c u)) = φ.1 u := by
      intro u
      have : c (c u) = (⟨σ * σ, h2⟩ : U)⁻¹ * u * ⟨σ * σ, h2⟩ := by
        apply Subtype.ext
        show σ⁻¹ * (σ⁻¹ * u.1 * σ) * σ = (σ * σ)⁻¹ * u.1 * (σ * σ)
        group
      have hinv : φ.1 (⟨σ * σ, h2⟩ : U)⁻¹ + φ.1 ⟨σ * σ, h2⟩ = 0 := by
        rw [← hadd, inv_mul_cancel, h1]
      rw [this, hadd, hadd]
      linear_combination hinv
    apply Subtype.ext
    funext u
    show φ.1 u + φ.1 (c u) + (φ.1 (c u) + φ.1 (c (c u))) = 0
    rw [hcc']
    generalize φ.1 u = a
    generalize φ.1 (c u) = b
    revert a b
    decide
  have hker : CardLe f.ker n := by
    refine CardLe.of_injective h (fun φ => ⟨φ.1, fun u u' hu => ?_⟩) ?_
    · have h0 : f φ.1 = 0 := φ.2
      have h3 : φ.1.1 u + φ.1.1 (c u) = 0 := congrArg (fun ψ : CharOff U S 2 => ψ.1 u) h0
      have hu' : u' = c u := Subtype.ext hu
      rw [hu']
      revert h3
      generalize φ.1.1 u = a
      generalize φ.1.1 (c u) = b
      revert a b
      decide
    · intro a b hab
      have hab' := congrArg Subtype.val hab
      exact Subtype.ext hab'
  exact sqZero _ f n hff hker

theorem UpperTheory.V.Two.idxTwo :
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (U V : Subgroup Γ) (S : Set Γ) (n : ℕ), U ≤ V → IsOpen (U.subgroupOf V : Set V) → U.relIndex V ∣ 2 → (∀ v ∈ V, ∀ s ∈ S, v⁻¹ * s * v ∈ S) → (∀ s ∈ S, s ∈ V → s ∈ U) →
      CardLe (CharOff V S 2) n → CardLe (CharOff U S 2) (n ^ 2) := by
  intro Γ _ _ _ U V S n hUV hopen hdvd hSV hSU hV
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · have hVU : V ≤ U := Subgroup.relIndex_eq_one.1 h1
    have : U = V := le_antisymm hUV hVU
    subst this
    exact hV.mono (Nat.le_self_pow two_ne_zero n)
  · have hnot : ¬ V ≤ U := fun hle => by
      rw [Subgroup.relIndex_eq_one.2 hle] at h2
      exact absurd h2 (by norm_num)
    obtain ⟨σ, hσV, hσU⟩ := SetLike.not_le_iff_exists.1 hnot
    have hidx : (U.subgroupOf V).index = 2 := h2
    have hnorm := Subgroup.normal_of_index_eq_two hidx
    refine idxTwo_conj U S σ n ?_ ?_ (fun s hs => hSV σ hσV s hs)
      (invTwo Γ U V S σ n hUV hσV hopen h2 hσU hSU hV)
    · intro u hu
      have := hnorm.conj_mem ⟨u, hUV hu⟩ (Subgroup.mem_subgroupOf.2 hu) (⟨σ, hσV⟩⁻¹)
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    · have := Subgroup.mul_self_mem_of_index_two hidx ⟨σ, hσV⟩
      rwa [Subgroup.mem_subgroupOf] at this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.OrbTwo
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.orbTwo :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M : AbF) (p c : ℕ), p.Prime → (p % 8 = 3 ∧ c = 2 ∨ p % 16 = 7 ∧ c = 4) → OrbLe (cycU 2 (abU Ω (withI M))) p (c * M.deg) := by
  intro Ω _ _ _ M p c hp hc
  classical
  obtain ⟨hsupAb, hdeg, hmem, hcyc⟩ := abBasic Ω
  have hK4 : (cycZ ℚ Ω 2).ker ≤ (galChar Ω 4).ker := (levChar Ω 2 2 ⊤).2
  have hV : cycU 2 (abU Ω (withI M)) = abU Ω M ⊓ (cycZ ℚ Ω 2).ker := by
    show abU Ω (M.sup (AbF.cyc 4)) ⊓ (cycZ ℚ Ω 2).ker = _
    rw [hsupAb, hcyc 4, inf_assoc, inf_eq_right.mpr hK4]
  haveI hWn : (abU Ω M).Normal := by
    haveI : NeZero M.m := ⟨M.pos.ne'⟩
    constructor
    intro g hg h
    rw [hmem M M.m dvd_rfl] at hg ⊢
    have hconj : galChar Ω M.m (h * g * h⁻¹) = galChar Ω M.m g := by
      rw [map_mul, map_mul, map_inv, mul_comm (galChar Ω M.m h), mul_inv_cancel_right]
    rw [hconj]
    exact hg
  rw [hV]
  by_cases hex : ∃ A₀ : ValuationSubring Ω, A₀.valuation (p : Ω) < 1
  · obtain ⟨A₀, hA₀⟩ := hex
    obtain ⟨hKD0, hKDle⟩ := decIndex Ω p c A₀ hp hc hA₀
    have hi : (abU Ω M).index = M.deg := (hdeg M).1
    have hW0 : (abU Ω M).index ≠ 0 := hi ▸ (hdeg M).2.1
    obtain ⟨hne, hle⟩ := supIndex (G ℚ Ω) (cycZ ℚ Ω 2).ker (abU Ω M) (Dec A₀) hW0 hKD0
    obtain ⟨T, hT, h1, h2⟩ := orbIndex Ω p (abU Ω M ⊓ (cycZ ℚ Ω 2).ker) A₀ hp hA₀ hne
    refine ⟨T, hT.trans ?_, h1, h2⟩
    calc _ ≤ (abU Ω M).index * ((cycZ ℚ Ω 2).ker ⊔ Dec A₀).index := hle
      _ ≤ M.deg * c := by rw [hi]; exact Nat.mul_le_mul_left _ hKDle
      _ = c * M.deg := Nat.mul_comm _ _
  · push_neg at hex
    exact ⟨∅, by simp, by simp, fun A hA => absurd hA (not_lt.mpr (hex A))⟩
end

