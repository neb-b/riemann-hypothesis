module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PointLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SmoothHomWeightSumNeg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.DefIso
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem residue_eq_residueField_map_comp_res {O' C : Type} [CommRing O'] [IsLocalRing O'] [CommRing C] [Algebra O' C]
    [IsCO O' C] [IsLocalHom (algebraMap O' C)] :
    IsLocalRing.residue C =
      (IsLocalRing.ResidueField.map (algebraMap O' C)).comp (res O' C : C →+* ResidueField O') := by
  ext z
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O') z
  have h1 : (res O' C) z = (res O' C) (algebraMap O' C a) := by
    rw [← sub_eq_zero, ← map_sub, res_eq_zero_iff]
    exact ha
  have h2 : IsLocalRing.residue C z = IsLocalRing.residue C (algebraMap O' C a) := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact ha
  rw [RingHom.comp_apply, RingHom.coe_coe, h1, h2, AlgHom.commutes]
  exact (IsLocalRing.ResidueField.map_residue _ a).symm

private theorem nRep_isBar_comp_map_iff {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}
    {K K' : Type} [Field K] [CommRing K'] [Nontrivial K'] (f : k →+* K) (j : K →+* K')
    (σ : NRep F n K) : NRep.IsBar (j.comp f) (NRep.map j σ) ↔ NRep.IsBar f σ := by
  unfold NRep.IsBar
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun g i => j.injective (h1 g i), fun v i g => j.injective (h2 v i g)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun g i => congrArg j (h1 g i), fun v i g => congrArg j (h2 v i g)⟩

theorem UpperTheory.V.Fr.def_iso :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), ∀ (C : Type) [CommRing C] [Algebra L.O' C] [IsCO L.O' C] (ρ : NRep F n C), ρ.Cont (maximalIdeal C) → ρ.map (res L.O' C : C →+* ResidueField L.O') = L.ρ.map (res L.O' L.R : L.R →+* ResidueField L.O') → ∃! g : L.R →ₐ[L.O'] C, L.ρ.map (g : L.R →+* C) = ρ := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L C _ _ _ ρ hc hres
  have hOloc : IsLocalHom (algebraMap O L.O') := by
    refine ⟨fun a ha => ?_⟩
    by_contra h
    have hm : algebraMap O L.O' a ∈ maximalIdeal L.O' := by
      rw [← L.unr]
      exact Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal a).mpr h)
    exact (IsLocalRing.mem_maximalIdeal _).mp hm ha
  haveI : IsLocalHom (algebraMap L.O' C) := IsCO.isLocalHom
  haveI : IsLocalHom (algebraMap L.O' L.R) := IsCO.isLocalHom
  letI : Algebra O C := ((algebraMap L.O' C).comp (algebraMap O L.O')).toAlgebra
  haveI : IsScalarTower O L.O' C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hCloc : IsLocalHom (algebraMap O C) :=
    inferInstanceAs (IsLocalHom ((algebraMap L.O' C).comp (algebraMap O L.O')))
  have hCL : UpperTheory.V.CA.IsCL O C := by
    refine ⟨inferInstance, IsCO.complete (O := L.O'), hCloc, ?_⟩
    let φ : L.O' →ₐ[O] ResidueField C :=
      (IsScalarTower.toAlgHom O C (ResidueField C)).comp (IsScalarTower.toAlgHom O L.O' C)
    refine Module.Finite.of_surjective φ.toLinearMap ?_
    intro y
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := L.O') z
    refine ⟨a, ?_⟩
    show IsLocalRing.residue C (algebraMap L.O' C a) = IsLocalRing.residue C z
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← neg_sub]
    exact neg_mem ha
  let f0 : ResidueField O →+* ResidueField L.O' := IsLocalRing.ResidueField.map (algebraMap O L.O')
  let jC : ResidueField L.O' →+* ResidueField C := IsLocalRing.ResidueField.map (algebraMap L.O' C)
  let jR : ResidueField L.O' →+* ResidueField L.R :=
    IsLocalRing.ResidueField.map (algebraMap L.O' L.R)
  have hfC : IsResMap O C (jC.comp f0) := by
    intro a
    show jC (f0 (IsLocalRing.residue O a)) = _
    rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue]
    rfl
  have hfR : IsResMap O L.R (jR.comp f0) := by
    intro a
    show jR (f0 (IsLocalRing.residue O a)) = _
    rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue,
      IsScalarTower.algebraMap_apply O L.O' L.R a]
  have hbR := (loc_rho hF hn S x L).2.1 _ hfR
  rw [residue_eq_residueField_map_comp_res (O' := L.O') (C := L.R)] at hbR
  have hσ : NRep.IsBar f0 (NRep.map (res L.O' L.R : L.R →+* ResidueField L.O') L.ρ) :=
    (nRep_isBar_comp_map_iff f0 jR _).mp hbR
  have hbar : NRep.IsBar (jC.comp f0) (NRep.map (IsLocalRing.residue C) ρ) := by
    rw [residue_eq_residueField_map_comp_res (O' := L.O') (C := C)]
    show NRep.IsBar (jC.comp f0) (NRep.map jC (NRep.map (res L.O' C : C →+* ResidueField L.O') ρ))
    rw [hres]
    exact (nRep_isBar_comp_map_iff f0 jC _).mpr hσ
  obtain ⟨ξ, hξ, hξx⟩ := point_loc hF hn S C hCL (jC.comp f0) hfC ρ hc hbar
  have hx0 : S.x0 ≤ x := by
    unfold Space.x0
    exact Ideal.map_le_iff_le_comap.mpr (loc_flat hF hn S x L).2.2
  let ξ1 : S.A →ₐ[O] ResidueField L.O' := ((res L.O' C).restrictScalars O).comp ξ
  let ξ2 : S.A →ₐ[O] ResidueField L.O' := ((res L.O' L.R).restrictScalars O).comp L.ι
  have h12 : ξ1 = ξ2 := by
    refine ext_A hF hn S (ResidueField L.O') ξ1 ξ2 ?_ ?_ ?_
    · exact (congrArg (NRep.map (res L.O' C : C →+* ResidueField L.O')) hξ).trans hres
    · intro a ha
      refine Ideal.mem_comap.mpr ?_
      show res L.O' C (ξ a) ∈ _
      rw [(res_eq_zero_iff L.O' C (ξ a)).mpr (hξx ha)]
      exact zero_mem _
    · intro a ha
      have hm : a ∈ Ideal.comap (L.ι : S.A →+* L.R) (maximalIdeal L.R) := by
        rw [L.lies]
        exact hx0 ha
      refine Ideal.mem_comap.mpr ?_
      show res L.O' L.R (L.ι a) ∈ _
      rw [(res_eq_zero_iff L.O' L.R (L.ι a)).mpr hm]
      exact zero_mem _
  obtain ⟨g, hg, huniq⟩ := L.univ C ξ (fun a => AlgHom.congr_fun h12 a)
  have hgι : (g : L.R →+* C).comp (L.ι : S.A →+* L.R) = (ξ : S.A →+* C) := RingHom.ext hg
  refine ⟨g, ?_, fun g' hg' => huniq g' ?_⟩
  · show NRep.map ((g : L.R →+* C).comp (L.ι : S.A →+* L.R)) S.u = ρ
    rw [hgι]
    exact hξ
  · let ξ' : S.A →ₐ[O] C := (g'.restrictScalars O).comp L.ι
    have h' : ξ' = ξ := by
      refine ext_A hF hn S C ξ' ξ ?_ ?_ hξx
      · exact hg'.trans hξ.symm
      · intro a ha
        have hm : a ∈ Ideal.comap (L.ι : S.A →+* L.R) (maximalIdeal L.R) := by
          rw [L.lies]
          exact hx0 ha
        refine Ideal.mem_comap.mpr ?_
        show g' (L.ι a) ∈ maximalIdeal C
        rw [← res_eq_zero_iff L.O' C, res_map]
        exact (res_eq_zero_iff L.O' L.R _).mpr hm
    intro a
    exact AlgHom.congr_fun h' a
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ExistsNonzeroLowCocycle
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem exists_nonzero_low_cocycle :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ u : F.G0 → k, IsLocallyConstant u → (∀ g h : F.G0, u (g * h) = (F.Ψ h : k) * u g + u h) → (∀ g : F.G0, u (F.star g) = (((F.Ψ g)⁻¹ : kˣ) : k) * u g) → (∀ v, ∃ α : k, ∀ s, u (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - 1) * α) → u ≠ 0 → ∃ y a : F.G0 → k, F.Low k y a ∧ y ≠ 0 := by
  intro l _ k _ _ F C₀ hF u u1 u2 u3 u4 u5
  have h2 : (2 : k) ≠ 0 := by
    intro e
    have e' : ((2 : ℕ) : k) = 0 := by exact_mod_cast e
    rw [CharP.cast_eq_zero_iff k l] at e'
    exact hF.l_odd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 e')
  obtain ⟨-, -, s3, -, -⟩ := UpperTheory.V.Fr.star hF
  let P : F.G0 → k := fun g => F.Ψ g
  have P0 : ∀ g, P g ≠ 0 := fun g => Units.ne_zero _
  have Pm : ∀ g h, P (g * h) = P g * P h := fun g h => by simp [P]
  have Ps : ∀ g, P (F.star g) = (P g)⁻¹ := fun g => by simp only [P, s3, Units.val_inv_eq_inv_val]
  have Pl : IsLocallyConstant P := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun g => ⟨(fun h : F.G0 => (g : F.Γ)⁻¹ * h) ⁻¹' F.Ψ.ker,
      hF.Ψ_open.preimage (by fun_prop), by simp, fun h hh => ?_⟩
    have : F.Ψ ((g : F.Γ)⁻¹ * h) = 1 := hh
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    simp only [P, this]
  have u2' : ∀ g h, u (g * h) = P h * u g + u h := u2
  have u3' : ∀ g, u (F.star g) = (P g)⁻¹ * u g := fun g => by rw [u3, Units.val_inv_eq_inv_val]
  have hg : P F.g0 ^ 2 - 1 ≠ 0 := fun e => hF.baseSubgroup_spec (Units.ext (by rw [Units.val_pow_eq_pow_val]; exact sub_eq_zero.1 e))
  obtain ⟨δ, hδ⟩ : ∃ δ : k, δ * (P F.g0 ^ 2 - 1) = -(u F.g0 * (P F.g0 - 1)) := ⟨_, div_mul_cancel₀ _ hg⟩
  refine ⟨fun g => u g + δ * (P g - 1),
    fun g => δ ^ 2 - δ ^ 2 * (P g + (P g)⁻¹) / 2 - δ * (u g + (P g)⁻¹ * u g) + (P g)⁻¹ * u g ^ 2 / 2,
    ⟨?_, ?_, fun g h => ?_, fun g h => ?_, fun g => ?_, ?_, fun v => ?_⟩, fun e => u5 ?_⟩
  · exact (u1.prodMk Pl).comp fun z => z.1 + δ * (z.2 - 1)
  · exact (u1.prodMk Pl).comp fun z =>
      δ ^ 2 - δ ^ 2 * (z.2 + z.2⁻¹) / 2 - δ * (z.1 + z.2⁻¹ * z.1) + z.2⁻¹ * z.1 ^ 2 / 2
  · show _ = P h * _ + _
    rw [u2', Pm]; ring
  · rw [Units.val_inv_eq_inv_val]
    show _ = P h * _ + _ + (P g)⁻¹ * _
    have := P0 g
    have := P0 h
    simp only [u2', Pm, u3', Ps]
    field_simp
    ring
  · have := P0 g
    simp only [u3', Ps]
    field_simp
    ring
  · have := P0 F.g0
    simp only [u3', Ps]
    field_simp
    linear_combination hδ
  · obtain ⟨α, hα⟩ := u4 v
    refine ⟨δ + α, α - δ, α ^ 2 / 2 - δ * α - δ ^ 2 / 2, fun s => ?_⟩
    have h1 : u (F.loc0 v s) = (P (F.loc0 v s) - 1) * α := hα s
    have := P0 (F.loc0 v s)
    rw [Units.val_inv_eq_inv_val]
    show _ = (P (F.loc0 v s) - 1) * _ ∧ _ = (1 - (P (F.loc0 v s))⁻¹) * _ ∧
      _ = (P (F.loc0 v s) - (P (F.loc0 v s))⁻¹) * _ - (1 - (P (F.loc0 v s))⁻¹) * _
    simp only [u3', Ps, h1]
    refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring
  · have e1 : ∀ g, u g + δ * (P g - 1) = 0 := congrFun e
    have e2 := e1 (F.star F.g0)
    have e3 := e1 F.g0
    have := P0 F.g0
    rw [u3', Ps] at e2
    field_simp at e2
    have e4 : 2 * δ * (P F.g0 ^ 2 - 1) = 0 := by linear_combination (P F.g0 + 1) * e3 - (P F.g0 + 1) * e2
    have e5 : δ = 0 := by simpa [h2, hg] using e4
    funext g
    simpa [e5] using e1 g

section

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
  {F : Frame l (ResidueField O)} {C₀ : ℕ} (hF : F.Ok C₀) (S : Space O F 3)
include hF

private theorem at_ex (Q : Type) [CommRing Q] [Nontrivial Q] [Algebra (ResidueField O) Q] {y a : F.G0 → Q}
    (h : F.Low Q y a) : ∃ ξ : S.A →+* Q, S.At ξ y a := by
  obtain ⟨ρ, h1, h2, h3, h4, h5⟩ := UpperTheory.lowerTriangular_conj_antidiag hF Q y a h
  obtain ⟨ξ, h6, rfl⟩ := UpperTheory.smoothHom_weight_sum_neg hF (Or.inr rfl) S Q ρ h1 h2 h3
  refine ⟨ξ, h6, Ideal.span_le.2 ?_, h4, h5⟩
  rintro _ ⟨g, i, j, hij, rfl⟩
  have : (S.u.map ξ).r g i j ∈ (S.u.map ξ).triM := Ideal.subset_span ⟨g, i, j, hij, rfl⟩
  rwa [h2, Ideal.mem_bot] at this

private theorem at_uniq {Q : Type} [CommRing Q] [Algebra (ResidueField O) Q] {y a : F.G0 → Q} {ξ ξ' : S.A →+* Q}
    (h : S.At ξ y a) (h' : S.At ξ' y a) : ξ' = ξ := by
  obtain ⟨h1, -, h2⟩ := UpperTheory.smoothCharacter_extends_to_open_subgroup hF (Or.inr rfl) S Q ξ h.fpt
  obtain ⟨h1', -, -⟩ := UpperTheory.smoothCharacter_extends_to_open_subgroup hF (Or.inr rfl) S Q ξ' h'.fpt
  refine h2 ξ' h'.fpt fun g i j => ?_
  rcases lt_trichotomy i j with hij | rfl | hij
  · have hm : S.u.r g i j ∈ S.u.triM := Ideal.subset_span ⟨g, i, j, hij, rfl⟩
    exact (h'.low hm).trans (h.low hm).symm
  · exact (h1'.1 g i).trans (h1.1 g i).symm
  have hc : (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 1) ∨ (i = 2 ∧ j = 0) := by omega
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [h.hy, h'.hy]
  · have h5 : S.u.r (F.star g) 1 0 = S.u.r g 2 1 := (UpperTheory.V.Fr.star hF).2.2.2.2 S.u g 1 0
    rw [← h5, h.hy, h'.hy]
  · rw [h.ha, h'.ha]

private theorem at_res (p : PrimeSpectrum S.A) (hp : p ∈ S.BB) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra (ResidueField O) K) (ξ : S.A →+* K) (y a : F.G0 → K),
      RingHom.ker ξ = p.asIdeal ∧ S.At ξ y a ∧ F.Low K y a := by
  obtain ⟨K, _, _, ξ, h1, h2, h3⟩ := UpperTheory.smoothDual_exact hF (Or.inr rfl) S p hp
  obtain ⟨h4, h5, -⟩ := UpperTheory.smoothCharacter_extends_to_open_subgroup hF (Or.inr rfl) S K ξ h2
  refine ⟨K, inferInstance, inferInstance, ξ, _, _, h1, ⟨h2, h3, fun _ => rfl, fun _ => rfl⟩,
    UpperTheory.one_add_maximalIdeal_subset_units hF K (S.u.map ξ) h4 (Ideal.span_eq_bot.2 ?_) h5⟩
  rintro _ ⟨g, i, j, hij, rfl⟩
  exact h3 (Ideal.subset_span ⟨g, i, j, hij, rfl⟩)

private theorem line {K : Type} [Field K] [Algebra (ResidueField O) K] {Y A : F.G0 → Polynomial K}
    (h : F.Low (Polynomial K) Y A) :
    ∃ η : PrimeSpectrum S.A, S.mB ≤ S.π η.asIdeal ∧ (S.u.ee ≤ η.asIdeal → Y = 0) ∧
      ∀ (c : K) (ξ : S.A →+* K) (y a : F.G0 → K), S.At ξ y a → (∀ g, (Y g).eval c = y g) →
        (∀ g, (A g).eval c = a g) → η.asIdeal ≤ RingHom.ker ξ := by
  obtain ⟨ζ, hζ⟩ := at_ex hF S _ h
  refine ⟨⟨RingHom.ker ζ, RingHom.ker_isPrime ζ⟩, Ideal.map_le_iff_le_comap.1 hζ.fpt.x0, fun he => ?_,
    fun c ξ y a hξ hy ha x hx => ?_⟩
  · funext g
    rw [← hζ.hy]
    exact he (Ideal.subset_span ⟨g, 1, 0, by decide, rfl⟩)
  · let φ : Polynomial K →ₐ[ResidueField O] K := (Polynomial.aeval c : Polynomial K →ₐ[K] K).restrictScalars _
    have h1 := hζ.comp φ
    have e1 : (fun g => φ (Y g)) = y := funext fun g => by simpa [φ] using hy g
    have e2 : (fun g => φ (A g)) = a := funext fun g => by simpa [φ] using ha g
    rw [e1, e2] at h1
    rw [← at_uniq hF S hξ h1]
    have : ζ x = 0 := hx
    show φ (ζ x) = 0
    rw [this, map_zero]

end

theorem UpperTheory.V.Fr.preconnected_rank_three :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 3, S.BB.Nonempty ∧ IsPreconnected S.BB ∧ S.BB ⊆ closure (S.BB \ {p | S.u.ee ≤ p.asIdeal}) := by
  intro l _ O _ _ _ _ F C₀ hF S
  obtain ⟨b, hb, hb0⟩ := UpperTheory.exists_mem_strS_ne_zero_of_frameOk hF
  obtain ⟨u, u1, u2, u3, u4, u5⟩ := UpperTheory.exists_locallyConstant_twistedCocycle_ne_zero_of_frameOk hF
  obtain ⟨y₀, a₀, h₀, hy₀⟩ := exists_nonzero_low_cocycle hF u u1 u2 u3 u4 u5
  have hl : F.Low (ResidueField O) 0 b := by
    have := (Frame.Low.zero (F := F)).comb 0 hb
    simp only [Pi.zero_apply, mul_zero, zero_add] at this
    exact this
  obtain ⟨ξ₀, hξ₀⟩ := at_ex hF S _ hl
  let p₀ : PrimeSpectrum S.A := ⟨RingHom.ker ξ₀, RingHom.ker_isPrime ξ₀⟩
  have hp₀ : p₀ ∈ S.BB := ⟨Ideal.map_le_iff_le_comap.1 hξ₀.fpt.x0, fun h => hb0 (funext fun g => by
    rw [← hξ₀.ha]
    exact h (Ideal.subset_span ⟨g, 2, 0, by decide, rfl⟩))⟩
  refine ⟨⟨p₀, hp₀⟩, isPreconnected_of_forall p₀ fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨K, _, _, ξ, y, a, h1, h2, h3⟩ := at_res hF S p hp
    let c : K →ₐ[ResidueField O] Polynomial K := IsScalarTower.toAlgHom _ _ _
    let i : ResidueField O →ₐ[ResidueField O] K := Algebra.ofId _ _
    obtain ⟨η, e1, -, e2⟩ := line hF S ((h3.map c).comb Polynomial.X
      (Frame.strS_mul (1 - Polynomial.X) (Frame.strS_map (c.comp i).toLinearMap hb)))
    have l1 : η ≤ p := by
      have := e2 1 ξ y a h2 (fun g => by simp [c]) (fun g => by simp [c])
      rwa [h1] at this
    have l0 : η ≤ p₀ := fun x hx => by
      have := e2 0 _ _ _ (hξ₀.comp i) (fun g => by simp [c]) (fun g => by simp [c, i]) hx
      exact (map_eq_zero i).1 this
    have hη : η ∈ S.BB := ⟨e1, fun h => hp.2 (h.trans l1)⟩
    refine ⟨{η, p, p₀}, ?_, by simp, by simp, isPreconnected_singleton.subset_closure (s := {η}) (by simp) ?_⟩
    · rintro q (rfl | rfl | rfl) <;> assumption
    · rintro q (rfl | rfl | rfl)
      · exact subset_closure rfl
      · exact (PrimeSpectrum.le_iff_mem_closure _ _).1 l1
      · exact (PrimeSpectrum.le_iff_mem_closure _ _).1 l0
  · by_cases he : S.u.ee ≤ p.asIdeal
    swap
    · exact subset_closure ⟨hp, he⟩
    obtain ⟨K, _, _, ξ, y, a, h1, h2, h3⟩ := at_res hF S p hp
    obtain rfl : y = 0 := funext fun g => by
      rw [← h2.hy]
      exact (h1 ▸ he) (Ideal.subset_span ⟨g, 1, 0, by decide, rfl⟩)
    let c : K →ₐ[ResidueField O] Polynomial K := IsScalarTower.toAlgHom _ _ _
    let i : ResidueField O →ₐ[ResidueField O] K := Algebra.ofId _ _
    obtain ⟨η, e1, e3, e2⟩ := line hF S ((h₀.map (c.comp i)).comb Polynomial.X (Frame.strS_map c.toLinearMap h3.strS))
    have l1 : η ≤ p := by
      have := e2 0 ξ 0 a h2 (fun g => by simp [c]) (fun g => by simp [c])
      rwa [h1] at this
    have hη : η ∈ S.BB \ {p | S.u.ee ≤ p.asIdeal} := ⟨⟨e1, fun h => hp.2 (h.trans l1)⟩, fun h => hy₀ (funext fun g => by
      have := congrFun (e3 h) g
      simpa [c, i] using this)⟩
    exact closure_mono (Set.singleton_subset_iff.2 hη) ((PrimeSpectrum.le_iff_mem_closure _ _).1 l1)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocalDeformationTraceModMaximal
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.local_deformation_trace_mod_maximal :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), (maximalIdeal O).map (algebraMap O L.R) ≤ maximalIdeal L.R ∧ (∀ (g : F.G0) (i : Fin n), F.Ψ g = 1 → L.ρ.r g i i - 1 ∈ maximalIdeal L.R) ∧ ∀ (P : Ideal L.R) [IsLocalRing (L.R ⧸ P)], (maximalIdeal O).map (algebraMap O L.R) ≤ P → Finite (ResidueField (L.R ⧸ P)) ∧ (∀ y ∈ maximalIdeal L.R, Ideal.Quotient.mk P y ∈ maximalIdeal (L.R ⧸ P)) ∧ (L.ρ.map (Ideal.Quotient.mk P)).Cont (maximalIdeal (L.R ⧸ P)) ∧ ∃ f : ResidueField O →+* L.R ⧸ P, (∀ a : O, Ideal.Quotient.mk P (algebraMap O L.R a) = f (residue O a)) ∧ ((L.ρ.map (Ideal.Quotient.mk P)).map (residue (L.R ⧸ P))).IsBar ((residue (L.R ⧸ P)).comp f) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L
  obtain ⟨hc, hb, -⟩ := UpperTheory.V.Fr.loc_rho hF hn S x L
  have hm : ∀ a ∈ maximalIdeal O, algebraMap O L.R a ∈ maximalIdeal L.R := fun a ha => by
    have h1 : algebraMap O L.O' a ∈ maximalIdeal L.O' := L.unr ▸ Ideal.mem_map_of_mem _ ha
    rw [IsScalarTower.algebraMap_apply O L.O' L.R]
    exact map_nonunit (algebraMap L.O' L.R) _ h1
  haveI hloc : IsLocalHom (algebraMap O L.R) := ⟨fun a ha => by
    by_contra hna
    exact hm a hna ha⟩
  have hb0 := hb (ResidueField.map (algebraMap O L.R)) fun a => ResidueField.map_residue _ _
  refine ⟨Ideal.map_le_iff_le_comap.2 hm, fun g i hg => ?_, fun P _ hP => ?_⟩
  · have h := hb0.1 g i
    rw [hg, NRep.map_r] at h
    rw [← residue_eq_zero_iff, map_sub, h]
    simp
  haveI hlocP : IsLocalHom (Ideal.Quotient.mk P) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hmP : ∀ y ∈ maximalIdeal L.R, Ideal.Quotient.mk P y ∈ maximalIdeal (L.R ⧸ P) :=
    fun y hy => map_nonunit (Ideal.Quotient.mk P) y hy
  have hle : ∀ N : ℕ, maximalIdeal L.R ^ N ≤ (maximalIdeal (L.R ⧸ P) ^ N).comap (Ideal.Quotient.mk P) := fun N =>
    le_trans (Ideal.pow_right_mono (fun y hy => hmP y hy) N) (Ideal.le_comap_pow _ N)
  refine ⟨?_, hmP, ⟨fun i j N => ?_, fun v i N => ?_⟩, ?_⟩
  · haveI : Finite (ResidueField L.R) := Finite.of_surjective _ (resMap_bijective L.O' L.R).2
    refine Finite.of_surjective (ResidueField.map (Ideal.Quotient.mk P)) fun y => ?_
    obtain ⟨y, rfl⟩ := residue_surjective y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨residue _ y, ResidueField.map_residue _ _⟩
  · exact (hc.1 i j N).comp (Ideal.quotientMap _ (Ideal.Quotient.mk P) (hle N))
  · exact (hc.2 v i N).comp (Ideal.quotientMap _ (Ideal.Quotient.mk P) (hle N))
  · let f : ResidueField O →+* L.R ⧸ P :=
      Ideal.Quotient.lift (maximalIdeal O) ((Ideal.Quotient.mk P).comp (algebraMap O L.R))
        fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hP (Ideal.mem_map_of_mem _ ha))
    have hf : ∀ a : O, Ideal.Quotient.mk P (algebraMap O L.R a) = f (residue O a) := fun a => rfl
    have key : ∀ (y : L.R) (t : ResidueField O), residue L.R y = ResidueField.map (algebraMap O L.R) t →
        residue (L.R ⧸ P) (Ideal.Quotient.mk P y) = residue (L.R ⧸ P) (f t) := fun y t h => by
      obtain ⟨a, rfl⟩ := residue_surjective t
      rw [← hf, ← ResidueField.map_residue (Ideal.Quotient.mk P), h, ResidueField.map_residue,
        ResidueField.map_residue]
    exact ⟨f, hf, fun g i => key _ _ (hb0.1 g i), fun v i g => key _ _ (hb0.2 v i g)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrRes
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem residue_eq_map_algebraMap_comp_res_of_isCO {O' C : Type} [CommRing O'] [IsLocalRing O'] [CommRing C] [Algebra O' C]
    [IsCO O' C] [IsLocalHom (algebraMap O' C)] :
    IsLocalRing.residue C =
      (IsLocalRing.ResidueField.map (algebraMap O' C)).comp (res O' C : C →+* ResidueField O') := by
  ext z
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O') z
  have h1 : (res O' C) z = (res O' C) (algebraMap O' C a) := by
    rw [← sub_eq_zero, ← map_sub, res_eq_zero_iff]
    exact ha
  have h2 : IsLocalRing.residue C z = IsLocalRing.residue C (algebraMap O' C a) := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact ha
  rw [RingHom.comp_apply, RingHom.coe_coe, h1, h2, AlgHom.commutes]
  exact (IsLocalRing.ResidueField.map_residue _ a).symm

private theorem nRep_isBar_of_isBar_comp_map {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}
    {K K' : Type} [Field K] [CommRing K'] [Nontrivial K'] (f : k →+* K) (j : K →+* K')
    (σ : NRep F n K) (h : NRep.IsBar (j.comp f) (NRep.map j σ)) : NRep.IsBar f σ := by
  unfold NRep.IsBar at h ⊢
  exact ⟨fun g i => j.injective (h.1 g i), fun v i g => j.injective (h.2 v i g)⟩

theorem UpperTheory.V.Fr.pr_res :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), (∃ φ : ResidueField O →+* ResidueField L.O', (L.ρ.bar L.O').IsBar φ) ∧ ((∀ g, UpT ((L.ρ.bar L.O').r g)) ∨ ∀ g, UpT ((L.ρ.bar L.O').r g)ᵀ) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L
  have hOloc : IsLocalHom (algebraMap O L.O') := by
    refine ⟨fun a ha => ?_⟩
    by_contra h
    have hm : algebraMap O L.O' a ∈ maximalIdeal L.O' := by
      rw [← L.unr]
      exact Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal a).mpr h)
    exact (IsLocalRing.mem_maximalIdeal _).mp hm ha
  haveI : IsLocalHom (algebraMap L.O' L.R) := IsCO.isLocalHom
  let f0 : ResidueField O →+* ResidueField L.O' := IsLocalRing.ResidueField.map (algebraMap O L.O')
  let jR : ResidueField L.O' →+* ResidueField L.R :=
    IsLocalRing.ResidueField.map (algebraMap L.O' L.R)
  have hloc := loc_rho hF hn S x L
  refine ⟨⟨f0, ?_⟩, ?_⟩
  · have hfR : IsResMap O L.R (jR.comp f0) := by
      intro a
      show jR (f0 (IsLocalRing.residue O a)) = _
      rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue,
        IsScalarTower.algebraMap_apply O L.O' L.R a]
    have hbR := hloc.2.1 _ hfR
    rw [residue_eq_map_algebraMap_comp_res_of_isCO (O' := L.O') (C := L.R)] at hbR
    exact nRep_isBar_of_isBar_comp_map f0 jR _ hbR
  · by_cases hP : S.u.triP ≤ x
    · left
      have hle : L.ρ.triP ≤ maximalIdeal L.R := by
        rw [(hloc.2.2.1 (maximalIdeal L.R)).1]
        show S.u.triP ≤ Ideal.comap (L.ι : S.A →+* L.R) (maximalIdeal L.R)
        rw [L.lies]
        exact hP
      intro g i j hji
      have hm : L.ρ.r g i j ∈ maximalIdeal L.R := by
        refine hle ?_
        unfold NRep.triP
        exact Ideal.subset_span ⟨g, i, j, hji, rfl⟩
      show res L.O' L.R (L.ρ.r g i j) = 0
      exact (res_eq_zero_iff _ _ _).mpr hm
    · right
      have hle := (hloc.2.2.2 hP).2
      intro g i j hji
      have hm : L.ρ.r g j i ∈ maximalIdeal L.R := by
        refine hle ?_
        unfold NRep.triM
        exact Ideal.subset_span ⟨g, j, i, hji, rfl⟩
      show res L.O' L.R (L.ρ.r g j i) = 0
      exact (res_eq_zero_iff _ _ _).mpr hm
end

