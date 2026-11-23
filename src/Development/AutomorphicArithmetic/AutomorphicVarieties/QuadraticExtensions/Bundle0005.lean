module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneTwo
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem not_lt_one_of_coprime {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p m : ℕ} (h : p.Coprime m)
    (hp : A.valuation (p : Ω) < 1) : ¬ A.valuation (m : Ω) < 1 := by
  intro hm
  have hz : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => A.valuation_le_one ⟨(z : Ω), intCast_mem A z⟩
  have h1 : ((p : ℤ) * Nat.gcdA p m + (m : ℤ) * Nat.gcdB p m : ℤ) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one h]
    rfl
  have hcast : (p : Ω) * (Nat.gcdA p m : Ω) + (m : Ω) * (Nat.gcdB p m : Ω) = 1 := by
    have := congrArg (Int.cast : ℤ → Ω) h1
    push_cast at this
    exact this
  have ha : A.valuation ((p : Ω) * (Nat.gcdA p m : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hz _)) hp
  have hb : A.valuation ((m : Ω) * (Nat.gcdB p m : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hz _)) hm
  have := lt_of_le_of_lt (A.valuation.map_add _ _) (max_lt ha hb)
  rw [hcast, map_one] at this
  exact lt_irrefl _ this

theorem UpperTheory.V.Two.ineTwo :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M : AbF) (p : ℕ) (A : ValuationSubring Ω), p.Coprime (2 * M.m) → A.valuation (p : Ω) < 1 → Ine (F := ℚ) A ≤ cycU 2 (abU Ω (withI M)) := by
  intro Ω _ _ _ M p A hcop hp
  have h2 : p.Coprime 2 := Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 M.m) hcop
  have hM : p.Coprime M.m := Nat.Coprime.coprime_dvd_right (dvd_mul_left M.m 2) hcop
  have hW : p.Coprime (withI M).m := by
    show p.Coprime (M.m * max 4 1)
    exact Nat.Coprime.mul_right hM (by simpa using Nat.Coprime.pow_right 2 h2)
  intro g hg
  refine ⟨?_, ?_⟩
  · have := ineChar Ω (withI M).m A (not_lt_one_of_coprime A hW hp) hg
    rw [MonoidHom.mem_ker] at this
    show galChar Ω (withI M).m g ∈ (withI M).H
    rw [this]
    exact Subgroup.one_mem _
  · exact (places ℚ Ω 2 A).2.2.2 (not_lt_one_of_coprime A h2 hp) hg
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.InvTwo
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem UpperTheory.V.Two.invTwo_sign (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (U V : Subgroup Γ) (S : Set Γ) (σ : Γ) (hσ : σ ∈ V) (ho : IsOpen (U.subgroupOf V : Set V)) (hi : U.relIndex V = 2)
    (hn : σ ∉ U) (hS : ∀ s ∈ S, s ∈ V → s ∈ U) :
    ∃ ε ∈ CharOff V S 2, ε ⟨σ, hσ⟩ = 1 ∧ ∀ v : V, v.1 ∈ U → ε v = 0 := by
  classical
  set H : Subgroup V := U.subgroupOf V with hH
  have hidx : H.index = 2 := hi
  have hσH : (⟨σ, hσ⟩ : V) ∉ H := by
    rw [hH, Subgroup.mem_subgroupOf]; exact hn
  have hcl : IsClosed (H : Set V) := H.isClosed_of_isOpen ho
  have h10 : (1 : ZMod 2) ≠ 0 := one_ne_zero
  let ε : V → ZMod 2 := fun v => if v ∈ H then 0 else 1
  have hmem : ε ∈ CharOff V S 2 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [IsLocallyConstant.iff_isOpen_fiber_apply]
      intro x
      by_cases hx : x ∈ H
      · convert ho using 1
        ext v
        by_cases hv : v ∈ H <;> simp [ε, hv, hx, h10]
      · convert hcl.isOpen_compl using 1
        ext v
        by_cases hv : v ∈ H <;> simp [ε, hv, hx, h10, h10.symm]
    · intro a b
      have hab := Subgroup.mul_mem_iff_of_index_two hidx (a := a) (b := b)
      by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;> simp [ε, ha, hb, hab] <;> decide
    · intro u hu
      have : u ∈ H := by
        rw [hH, Subgroup.mem_subgroupOf]; exact hS _ hu u.2
      simp [ε, this]
  refine ⟨ε, hmem, ?_, ?_⟩
  · simp [ε, hσH]
  · intro v hv
    have : v ∈ H := by
      rw [hH, Subgroup.mem_subgroupOf]; exact hv
    simp [ε, this]

theorem UpperTheory.V.Two.invTwo :
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (U V : Subgroup Γ) (S : Set Γ) (σ : Γ) (n : ℕ), U ≤ V → σ ∈ V → IsOpen (U.subgroupOf V : Set V) → U.relIndex V = 2 → σ ∉ U → (∀ s ∈ S, s ∈ V → s ∈ U) →
      CardLe (CharOff V S 2) n → CardLe {φ : CharOff U S 2 // ∀ u u' : U, u'.1 = σ⁻¹ * u.1 * σ → φ.1 u' = φ.1 u} n := by
  intro Γ _ _ _ U V S σ n hUV hσ ho hi hn hS hQ
  have two : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  classical
  obtain ⟨ε, hε, hεσ, hεU⟩ := UpperTheory.V.Two.invTwo_sign Γ U V S σ hσ ho hi hn hS
  have hσσ : σ * σ ∈ U := by
    have h2 : (U.subgroupOf V).index = 2 := hi
    have := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨σ, hσ⟩ : V)) (b := ⟨σ, hσ⟩)).mpr Iff.rfl
    rwa [Subgroup.mem_subgroupOf] at this
  set P := {φ : CharOff U S 2 // ∀ u u' : U, u'.1 = σ⁻¹ * u.1 * σ → φ.1 u' = φ.1 u} with hP
  let val : P → ZMod 2 := fun φ => (φ.1 : U → ZMod 2) ⟨σ * σ, hσσ⟩
  obtain ⟨φ0, hφ0⟩ : ∃ φ0 : P, ∀ φ : P, val φ ≠ 0 → val φ0 = 1 := by
    by_cases hex : ∃ φ : P, val φ ≠ 0
    · obtain ⟨φ, hφ⟩ := hex
      exact ⟨φ, fun _ _ => (two _).resolve_left hφ⟩
    · push_neg at hex
      exact ⟨⟨0, fun _ _ _ => rfl⟩, fun φ h => absurd (hex φ) h⟩
  let χ : P → U → ZMod 2 := fun φ =>
    if val φ = 0 then (φ.1 : U → ZMod 2) else (φ.1 : U → ZMod 2) + (φ0.1 : U → ZMod 2)
  have hχmem : ∀ φ, χ φ ∈ CharOff U S 2 := by
    intro φ
    simp only [χ]
    split_ifs
    · exact φ.1.2
    · exact add_mem φ.1.2 φ0.1.2
  have hχinv : ∀ φ, ∀ u u' : U, u'.1 = σ⁻¹ * u.1 * σ → χ φ u' = χ φ u := by
    intro φ u u' h
    simp only [χ]
    split_ifs
    · exact φ.2 u u' h
    · simp only [Pi.add_apply]
      rw [φ.2 u u' h, φ0.2 u u' h]
  have hχσ : ∀ φ, χ φ ⟨σ * σ, hσσ⟩ = 0 := by
    intro φ
    simp only [χ]
    split_ifs with h
    · exact h
    · have h1 : (φ.1 : U → ZMod 2) ⟨σ * σ, hσσ⟩ = 1 := (two _).resolve_left h
      have h2 : (φ0.1 : U → ZMod 2) ⟨σ * σ, hσσ⟩ = 1 := hφ0 φ h
      simp only [Pi.add_apply]
      rw [h1, h2]
      rfl
  have hext : ∀ φ, ∃ ψ ∈ CharOff V S 2, ψ ⟨σ, hσ⟩ = 0 ∧ ∀ u : U, ψ ⟨u, hUV u.2⟩ = χ φ u :=
    fun φ => UpperTheory.V.Two.extTwo Γ U V S hUV σ hσ hσσ ho hi hn hS (χ φ) (hχmem φ) (hχinv φ) (hχσ φ)
  choose ψ hψmem hψσ hψU using hext
  let f : P → CharOff V S 2 := fun φ =>
    ⟨ψ φ + (if val φ = 0 then 0 else ε), add_mem (hψmem φ) (by split_ifs; exact zero_mem _; exact hε)⟩
  refine UpperTheory.V.Two.CardLe.of_injective hQ f ?_
  intro φ φ' hff
  have hfun : ψ φ + (if val φ = 0 then 0 else ε) = ψ φ' + (if val φ' = 0 then 0 else ε) :=
    congrArg Subtype.val hff
  have hbranch : (val φ = 0 ↔ val φ' = 0) := by
    have := congrFun hfun ⟨σ, hσ⟩
    simp only [Pi.add_apply] at this
    rw [hψσ φ, hψσ φ'] at this
    by_cases h : val φ = 0 <;> by_cases h' : val φ' = 0 <;> simp [h, h', hεσ] at this ⊢
  have hχ : χ φ = χ φ' := by
    funext u
    have := congrFun hfun ⟨u, hUV u.2⟩
    simp only [Pi.add_apply] at this
    rw [hψU φ u, hψU φ' u] at this
    have hu : ε ⟨u, hUV u.2⟩ = 0 := hεU _ u.2
    split_ifs at this <;> simpa [hu] using this
  apply Subtype.ext
  apply Subtype.ext
  simp only [χ] at hχ
  by_cases h : val φ = 0
  · have h' := hbranch.mp h
    simpa [h, h'] using hχ
  · have h' : ¬ val φ' = 0 := fun h' => h (hbranch.mpr h')
    simp only [h, h', if_false] at hχ
    exact add_right_cancel hχ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.KerTwo
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem gen_of_dvd_two {Q : Type} [Group Q] (H : Subgroup Q) (h : H.index ∣ 2) :
    H.Normal ∧ ∃ γ : Q, ∀ u : Q, u ∈ H ∨ u * γ ∈ H := by
  rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h2
  · rw [Subgroup.index_eq_one] at h1
    subst h1
    exact ⟨inferInstance, 1, fun u => Or.inl trivial⟩
  · obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 h2
    exact ⟨Subgroup.normal_of_index_eq_two h2, a, fun u => (ha u).or.symm⟩

theorem UpperTheory.V.Two.kerTwo :
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (ρ : Representation ℤ_[2] Γ (QZ 2)) (U' U : Subgroup Γ) (h : U' ≤ U), ContAction ρ → U'.relIndex U ∣ 2 → Module.length ℤ_[2] (LinearMap.ker (resU ρ h)) ≤ 1 := by
  intro Γ _ _ _ ρ U' U h hρ hd
  obtain ⟨hN, γ, hγ⟩ := gen_of_dvd_two (U'.subgroupOf U) hd
  have hcl : U ≤ (Subgroup.zpowers γ.1 ⊔ U').topologicalClosure := by
    refine le_trans (fun u hu => ?_) (Subgroup.le_topologicalClosure _)
    rcases hγ ⟨u, hu⟩ with h1 | h1
    · exact Subgroup.mem_sup_right h1
    · have h2 : u * γ.1 ∈ Subgroup.zpowers γ.1 ⊔ U' := Subgroup.mem_sup_right h1
      exact (Subgroup.mul_mem_cancel_right _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))).1 h2
  have hstab : ∀ m ∈ H0U ρ U', ρ γ m - m ∈ H0U ρ U' := by
    intro m hm
    refine Submodule.sub_mem _ ?_ hm
    intro u
    have h1 : γ⁻¹ * ⟨u.1, h u.2⟩ * γ⁻¹⁻¹ ∈ U'.subgroupOf U :=
      hN.conj_mem _ (by simp [Subgroup.mem_subgroupOf]) _
    have h2 : γ.1⁻¹ * u.1 * γ.1 ∈ U' := by simpa [Subgroup.mem_subgroupOf] using h1
    have h3 : ρ (γ.1⁻¹ * u.1 * γ.1) m = m := hm ⟨_, h2⟩
    show ρ u.1 (ρ γ m) = ρ γ m
    conv_rhs => rw [← h3]
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  let T : H0U ρ U' →ₗ[ℤ_[2]] H0U ρ U' := (ρ γ - LinearMap.id).restrict (p := H0U ρ U') (q := H0U ρ U') hstab
  obtain ⟨φ, hφ⟩ := kerResGen1 _ Γ _ ρ hρ U' U h γ γ.2 hcl T fun _ => rfl
  refine subqLen 2 (H0U ρ U') _ _ (LinearMap.range T).mkQ φ (Submodule.mkQ_surjective _) hφ fun x => ?_
  obtain ⟨k, hk⟩ := hd
  have h1 := kerResSmul _ Γ _ ρ U' U h x.1 x.2
  refine Subtype.ext ?_
  show ((2 : ℕ) : ℤ_[2]) • x.1 = 0
  have h2 : (U'.relIndex U * k) • x.1 = 0 := by rw [mul_comm, mul_smul, h1, smul_zero]
  rw [← hk] at h2
  rw [Nat.cast_smul_eq_nsmul]
  exact h2
end

