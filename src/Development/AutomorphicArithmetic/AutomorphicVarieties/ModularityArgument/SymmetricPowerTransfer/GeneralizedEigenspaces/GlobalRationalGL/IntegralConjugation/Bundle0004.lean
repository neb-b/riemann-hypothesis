module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0624
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0003
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.ExistsUnr
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Dict.Br.QuadraticCharacterExistence

open scoped WithZero

private theorem exists_unr {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (c : ℂˣ) :
    ∃ χ : Kˣ →* ℂˣ, (∀ u : Oˣ, χ (Units.map (algebraMap O K : O →* K) u) = 1) ∧
      ∀ (ϖ : O) (x : Kˣ), Irreducible ϖ → (x : K) = algebraMap O K ϖ → χ x = c := by
  let w : HeightOneSpectrum O := IsDiscreteValuationRing.maximalIdeal O
  let f : Kˣ →* Multiplicative ℤ :=
    (WithZero.unitsWithZeroEquiv (α := Multiplicative ℤ)).toMonoidHom.comp
      (Units.map ((w.valuation K : Valuation K ℤᵐ⁰) : K →* ℤᵐ⁰))
  have hf : ∀ (x : Kˣ) (n : Multiplicative ℤ), w.valuation K (x : K) = (n : ℤᵐ⁰) → f x = n := by
    intro x n h
    apply WithZero.coe_injective
    exact (WithZero.coe_unitsWithZeroEquiv_eq_units_val _).trans h
  refine ⟨(zpowersHom ℂˣ c⁻¹).comp f, fun u => ?_, fun ϖ x hϖ hx => ?_⟩
  · have h1 : w.valuation K (Units.map (algebraMap O K : O →* K) u : K) = ((1 : Multiplicative ℤ) : ℤᵐ⁰) := by
      rw [Units.coe_map, MonoidHom.coe_coe, HeightOneSpectrum.valuation_of_algebraMap, WithZero.coe_one,
        HeightOneSpectrum.intValuation_eq_one_iff]
      exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit
    rw [MonoidHom.comp_apply, hf _ _ h1, map_one]
  · have h1 : w.valuation K (x : K) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : ℤᵐ⁰) := by
      rw [hx, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero hϖ.maximalIdeal_eq]
      rfl
    rw [MonoidHom.comp_apply, hf _ _ h1]
    simp [zpowersHom_apply]

private theorem delta_ne {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L) : R.Δ ≠ 0 := by
  intro h
  have h1 : (QuadraticAlgebra.omega : Lsq (Lp L) R.Δ) * QuadraticAlgebra.omega = 0 := by
    ext <;> simp [h]
  have h2 : R.e QuadraticAlgebra.omega = 0 := by
    have := congrArg R.e h1
    rw [map_mul, map_zero] at this
    exact mul_self_eq_zero.1 this
  have h3 : (QuadraticAlgebra.omega : Lsq (Lp L) R.Δ) = 0 := by
    exact (map_eq_zero_iff R.e R.e.injective).1 h2
  have := congrArg QuadraticAlgebra.im h3
  simp at this

private theorem hs_one {K : Type} [Field K] [CharZero K] {D : K} (h0 : D ≠ 0) (h : IsSquare D) (x : K) : hs D x = 1 := by
  obtain ⟨r, rfl⟩ := h
  have hr : r ≠ 0 := fun e => h0 (by rw [e, mul_zero])
  refine if_pos ⟨(x + 1) / 2, (x - 1) / (2 * r), ?_⟩
  field_simp
  ring

private theorem hs_neg {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    {D : K} (L : IsLoc O D) (hD : ¬ IsSquare D) {p : O} (hp : Irreducible p) : hs D (algebraMap O K p) = -1 := by
  haveI := L.frac
  obtain ⟨ε, s, hs0, rfl⟩ := L.even
  have hp' : algebraMap O K p ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hp.ne_zero
  refine if_neg fun ⟨a, b, e⟩ => L.not_even hp ?_
  have e' : a ^ 2 - algebraMap O K ε * (s * b) ^ 2 = algebraMap O K p := by rw [← e]; ring
  exact e' ▸ L.even_of_norm ε (fun ⟨r, hr⟩ => hD ⟨r * s, by rw [hr]; ring⟩) (e' ▸ hp')

end UpperTheory.V.Z.Sym.Dict.Br.QuadraticCharacterExistence

open UpperTheory.V.Z.Sym.Dict.Br.QuadraticCharacterExistence in
theorem UpperTheory.V.Z.Sym.Dict.Br.chiEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L), ∃ χ : ∀ v : Pl (Lp L), (Kv v)ˣ →* ℂˣ, (∀ v : Pl (Lp L), (2 : 𝓞 (Lp L)) ∉ v.asIdeal ∨ IsSquare (cv v R.Δ) → IsChi (Ov v) (cv v R.Δ) (χ v)) := by
  intro L _ _ _ R
  have key : ∀ v : Pl (Lp L), ∃ χ : (Kv v)ˣ →* ℂˣ,
      (2 : 𝓞 (Lp L)) ∉ v.asIdeal ∨ IsSquare (cv v R.Δ) → IsChi (Ov v) (cv v R.Δ) χ := by
    intro v
    obtain ⟨hf, -, hfin, -⟩ := locBase (Lp L) v
    haveI := hf
    haveI := hfin
    have hq : (Nat.card (IsLocalRing.ResidueField (Ov v)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 Nat.card_pos.ne'
    by_cases hsq : IsSquare (cv v R.Δ)
    · haveI : CharZero (Kv v) := charZero_of_injective_ringHom (cv v).injective
      have hΔ : cv v R.Δ ≠ 0 := (map_ne_zero _).2 (delta_ne R)
      obtain ⟨χ, h1, h2⟩ := exists_unr (O := Ov v) (K := Kv v) (Units.mk0 _ (div_ne_zero one_ne_zero hq))
      refine ⟨χ, fun _ => ⟨h1, fun ϖ x hϖ hx => ?_⟩⟩
      rw [h2 ϖ x hϖ hx, hs_one hΔ hsq]
      rfl
    · obtain ⟨χ, h1, h2⟩ := exists_unr (O := Ov v) (K := Kv v)
        (Units.mk0 _ (div_ne_zero (neg_ne_zero.2 one_ne_zero) hq))
      refine ⟨χ, fun h => ⟨h1, fun ϖ x hϖ hx => ?_⟩⟩
      have hL := R.loc v (h.resolve_right hsq)
      rw [h2 ϖ x hϖ hx, hx, hs_neg hL hsq hϖ]
      rfl
  choose χ hχ using key
  exact ⟨χ, hχ⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.IsoAbs
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem continuous_of_val_iff {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    [IsNonarchimedeanLocalField k'] (i : k ≃+* k')
    (h : ∀ a b, valuation k' (i a) ≤ valuation k' (i b) ↔ valuation k a ≤ valuation k b) :
    Continuous i := by
  refine continuous_of_continuousAt_zero (i : k →+* k').toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  change Filter.Tendsto i (nhds 0) (nhds 0)
  rw [(IsValuativeTopology.hasBasis_nhds_zero' k').tendsto_right_iff]
  intro r hr
  obtain ⟨c, rfl⟩ := valuation_surjective r
  have hc : valuation k (i.symm c) ≠ 0 := by
    intro h0
    have h2 := (h (i.symm c) 0).2 (by simp [h0])
    simp only [RingEquiv.apply_symm_apply, map_zero, le_zero_iff] at h2
    exact hr h2
  have hm : {x : k | valuation k x < valuation k (i.symm c)} ∈ nhds (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mpr ⟨_, hc, subset_rfl⟩
  filter_upwards [hm] with a ha
  have h3 := h (i.symm c) a
  rw [RingEquiv.apply_symm_apply] at h3
  exact not_le.1 fun h4 => absurd (h3.1 h4) (not_le.2 ha)

theorem UpperTheory.V.Z.Sym.Dict.Br.isoAbs :
    ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), IsoOk i → ∀ (z : ℂ) (a : kˣ), absPow k' z (Units.map (i : k →* k') a) = absPow k z a := by
  intro k k' _ _ _ _ _ _ _ _ i hi z a
  have h1 := (isoVal k k' i hi).1
  have hc : Continuous i := continuous_of_val_iff i h1
  have hc' : Continuous i.symm := continuous_of_val_iff i.symm fun a b => by
    have := h1 (i.symm a) (i.symm b)
    simpa only [RingEquiv.apply_symm_apply] using this.symm
  have hn := GlobalTheory.SplitWeil.nabs_map_of_homeomorph i hc hc' a
  ext
  rw [val_absPow, val_absPow]
  exact congrArg (fun t : ℝ => (t : ℂ) ^ z) hn
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.IsoJ
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.isoJ :
    ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), IsoOk i → (∀ (V : Sig.Lev k) (V' : Sig.Lev k'), V.c = V'.c → (∀ a, Units.map (i : k →* k') a ∈ V'.H ↔ a ∈ V.H) → ∀ (n : ℕ) (g : GL (Fin n) k), GeneralLinearGroup.map (i : k →+* k') g ∈ V'.J n ↔ g ∈ V.J n) ∧ ∀ (n : ℕ) (g : GL (Fin n) k), GeneralLinearGroup.map (i : k →+* k') g ∈ KO k' (Fin n) ↔ g ∈ KO k (Fin n) := by
  intro k k' _ _ _ _ _ _ _ _ i hi
  obtain ⟨hv, hu, -, -⟩ := isoVal k k' i hi
  have hent : ∀ (n : ℕ) (g : GL (Fin n) k) (a b : Fin n),
      (GeneralLinearGroup.map (i : k →+* k') g : Matrix (Fin n) (Fin n) k') a b = i ((g : Matrix (Fin n) (Fin n) k) a b) := by
    intro n g a b
    rfl
  have h1 : ∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1 := hi.int
  refine ⟨?_, ?_⟩
  · intro V V' hc hH n g
    rw [Sig.memJ, Sig.memJ]
    simp only [hent, h1]
    have hpow : ∀ x : k, valuation k' (i x) ≤ valuation k' ↑(Hi.unif k') ^ (V'.c + 1) ↔
        valuation k x ≤ valuation k ↑(Hi.unif k) ^ (V.c + 1) := by
      intro x
      rw [← hu, hc, ← map_pow, ← map_pow, ← map_pow, hv]
    simp only [hpow]
    have hd : ∀ x : k, (∃ u ∈ V'.H, (u : k') = i x) ↔ (∃ u ∈ V.H, (u : k) = x) := by
      intro x
      constructor
      · rintro ⟨u, hu', he⟩
        refine ⟨Units.map (i.symm : k' →* k) u, ?_, ?_⟩
        · rw [← hH]
          convert hu'
          ext
          simp
        · simp [he]
      · rintro ⟨u, hu', he⟩
        refine ⟨Units.map (i : k →* k') u, (hH u).2 hu', ?_⟩
        simp [he]
    simp only [hd]
  · intro n g
    rw [Hi.GlAx.mem_KO, Hi.GlAx.mem_KO, Hi.GlAx.bd_zero, Hi.GlAx.bd_zero, Hi.GlAx.bd_zero, Hi.GlAx.bd_zero,
      ← map_inv]
    exact and_congr (forall_congr' fun a => forall_congr' fun b => h1 _)
      (forall_congr' fun a => forall_congr' fun b => h1 _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.MapOne
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem star_map {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L)
    (x : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ)) :
    ((x.map R.e).map (IsCMField.complexConj L))ᵀ = (star x).map R.e := by
  ext i j
  simp [Matrix.star_apply, R.e_star]

private theorem map_mul' {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L)
    (x y : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ)) :
    (x * y).map R.e = x.map R.e * y.map R.e :=
  map_mul (R.e : Lsq (Lp L) R.Δ →+* L).mapMatrix x y

private theorem map_one' {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L) :
    (1 : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ)).map R.e = 1 :=
  map_one (R.e : Lsq (Lp L) R.Δ →+* L).mapMatrix

private theorem map_det' {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L)
    (x : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ)) :
    (x.map R.e).det = R.e x.det :=
  ((R.e : Lsq (Lp L) R.Δ →+* L).map_det x).symm

theorem UpperTheory.V.Z.Sym.Dict.Br.rSEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L), ∃ r : SU R.Δ ≃* ↥(ratU L 2 ⊓ SUA L), (∀ γ w, mL w (r γ : UA L 2) = (mt (γ : DX R.Δ)).map fun x => algebraMap L (Kw w) (R.e x)) ∧ ∀ γ (τ : L →+* ℂ), (cEmb τ (r γ : UA L 2) : Matrix (Fin 2) (Fin 2) ℂ) = (mt (γ : DX R.Δ)).map fun x => τ (R.e x) := by
  intro L _ _ _ R
  have hrf := ratFacts L 2
  obtain ⟨hs1, hs2⟩ := suIff (Lp L) R.Δ
  let E : GL (Fin 2) (Lsq (Lp L) R.Δ) →* GL (Fin 2) L :=
    GeneralLinearGroup.map (R.e : Lsq (Lp L) R.Δ →+* L)
  have hEc : ∀ g, (E g : Matrix (Fin 2) (Fin 2) L) = (g : Matrix (Fin 2) (Fin 2) _).map R.e := fun g => rfl
  have hdet1 : ∀ γ : SU R.Δ, (mt (γ : DX R.Δ)).det = 1 := by
    intro γ
    have h : GeneralLinearGroup.det ((γ : DX R.Δ) : GL (Fin 2) (Lsq (Lp L) R.Δ)) = 1 := γ.2
    simpa using congrArg Units.val h
  have hstar : ∀ γ : SU R.Δ, star (mt (γ : DX R.Δ)) * mt (γ : DX R.Δ) = 1 := by
    intro γ
    rw [(hs1 γ).1, hdet1, one_smul]
  have hdetE : ∀ γ : SU R.Δ, GeneralLinearGroup.det (E ((γ : DX R.Δ) : GL (Fin 2) (Lsq (Lp L) R.Δ))) = 1 := by
    intro γ
    apply Units.ext
    have : (E ((γ : DX R.Δ) : GL (Fin 2) (Lsq (Lp L) R.Δ)) : Matrix (Fin 2) (Fin 2) L).det = 1 := by
      rw [hEc, map_det', hdet1, map_one]
    simpa using this
  have hmem : ∀ γ : SU R.Δ, ratGL L 2 (E ((γ : DX R.Δ) : GL (Fin 2) (Lsq (Lp L) R.Δ))) ∈ UA L 2 := by
    intro γ
    rw [(hrf _).1, hEc, star_map, ← map_mul', hstar, map_one']
  let φ1 : SU R.Δ →* UA L 2 :=
    ((ratGL L 2).comp (E.comp ((DX R.Δ).subtype.comp (SU R.Δ).subtype))).codRestrict (UA L 2) hmem
  have hφ1 : ∀ γ, ((φ1 γ : UA L 2) : GlobalTheory.CuspRep.GA L 2) = ratGL L 2 (E ((γ : DX R.Δ) : GL (Fin 2) (Lsq (Lp L) R.Δ))) := fun _ => rfl
  have hmem2 : ∀ γ, φ1 γ ∈ ratU L 2 ⊓ SUA L := by
    intro γ
    refine ⟨?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.2 ⟨_, rfl⟩
    · show GeneralLinearGroup.det ((φ1 γ : UA L 2) : GlobalTheory.CuspRep.GA L 2) = 1
      rw [hφ1]
      exact (((hrf _).2.2 (hmem γ)).2.2).2 (hdetE γ)
  let φ2 : SU R.Δ →* ↥(ratU L 2 ⊓ SUA L) := φ1.codRestrict _ hmem2
  have hinj : Function.Injective φ2 := by
    intro a b hab
    have h1 : ((φ1 a : UA L 2) : GlobalTheory.CuspRep.GA L 2) = ((φ1 b : UA L 2) : GlobalTheory.CuspRep.GA L 2) :=
      congrArg (fun x : ↥(ratU L 2 ⊓ SUA L) => ((x : UA L 2) : GlobalTheory.CuspRep.GA L 2)) hab
    rw [hφ1, hφ1] at h1
    have h2 := (hrf (E 1)).2.1 h1
    have h3 : mt (a : DX R.Δ) = mt (b : DX R.Δ) := by
      have h4 := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L)) h2
      simp only [hEc] at h4
      exact Matrix.ext fun i j => R.e.injective (congrFun (congrFun h4 i) j)
    exact Subtype.ext (Subtype.ext (Units.ext h3))
  have hsurj : Function.Surjective φ2 := by
    rintro ⟨x, hx1, hx2⟩
    obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.1 hx1
    have hgU : ratGL L 2 g ∈ UA L 2 := hg ▸ x.2
    have hdx : GeneralLinearGroup.det ((x : UA L 2) : GlobalTheory.CuspRep.GA L 2) = 1 := hx2
    have hdg : GeneralLinearGroup.det g = 1 := by
      apply ((hrf g).2.2 hgU).2.2.1
      rw [hg]; exact hdx
    have hconj := ((hrf g).1).1 hgU
    let m : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ) := (g : Matrix (Fin 2) (Fin 2) L).map R.e.symm
    have hm : m.map R.e = g := by
      ext i j; simp [m]
    have hms : star m * m = 1 := by
      have h1 : (star m * m).map R.e = (1 : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ)).map R.e := by
        rw [map_mul', ← star_map, hm, hconj, map_one']
      exact Matrix.ext fun i j => R.e.injective (congrFun (congrFun h1 i) j)
    have hmd : m.det = 1 := by
      apply R.e.injective
      rw [← map_det', hm, map_one]
      simpa using congrArg Units.val hdg
    obtain ⟨h, hh⟩ := hs2 m hms hmd
    have hSU : h ∈ SU R.Δ := by
      show GeneralLinearGroup.det (h : GL (Fin 2) (Lsq (Lp L) R.Δ)) = 1
      apply Units.ext
      have : (mt h).det = 1 := hh ▸ hmd
      simpa using this
    refine ⟨⟨h, hSU⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    show ratGL L 2 (E (h : GL (Fin 2) (Lsq (Lp L) R.Δ))) = _
    rw [← hg]
    congr 1
    apply Units.ext
    rw [hEc]
    show (mt h).map R.e = _
    rw [hh, hm]
  refine ⟨MulEquiv.ofBijective φ2 ⟨hinj, hsurj⟩, ?_, ?_⟩
  · intro γ w
    have := ((hrf _).2.2 (hmem γ)).1 w
    exact this.trans (by rw [hEc]; ext i j; rfl)
  · intro γ τ
    have := ((hrf _).2.2 (hmem γ)).2.1 τ
    exact this.trans (by rw [hEc]; ext i j; rfl)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.MemKGLIff
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem mem_KGL_iff {L : Type} [Field L] [NumberField L] [IsCMField L] (w : Plc L) {n : ℕ}
    (x : GL (Fin n) (Kw w)) : x ∈ GlobalTheory.LFun.KGL w (n := n) ↔
      (∀ i j, (x : Matrix (Fin n) (Fin n) (Kw w)) i j ∈ w.adicCompletionIntegers L) ∧
      ∀ i j, ((x⁻¹ : GL (Fin n) (Kw w)) : Matrix (Fin n) (Fin n) (Kw w)) i j ∈ w.adicCompletionIntegers L := by
  rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL, GlobalTheory.SplitFlip.mem_KO_iff]
  have h : ∀ y : Kw w, y ∈ 𝒪[Kw w] ↔ y ∈ w.adicCompletionIntegers L := fun y => ((intsOv L w).2 y).symm
  simp only [h]

theorem UpperTheory.V.Z.Sym.Dict.Br.okG :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L), (∀ (g : GA B.Δ) v, g.1 v ∈ KU (Ov v) _ ↔ ∀ w, un w = v → cLoc w (B.bG g : UA L 3) ∈ GlobalTheory.LFun.KGL w (n := 3)) ∧ (∀ (g : GA B.Δ) v, g.1 v = 1 ↔ ∀ w, un w = v → cLoc w (B.bG g : UA L 3) = 1) ∧ ∀ w (S : B.toRingBr.Split w) (g : GA B.Δ), cLoc w (B.bG g : UA L 3) = GeneralLinearGroup.map (S.i : Kv (un w) →+* Kw w) (Sig.eU S.hs (g.1 (un w))) := by
  intro L _ _ _ B
  have hm : ∀ (g : GA B.Δ) (w : Plc L) (i j : Fin 3),
      (cLoc w (B.bG g : UA L 3) : Matrix (Fin 3) (Fin 3) (Kw w)) i j
        = B.ρ _ w rfl ((g.1 (un w) : Matrix (Fin 3) (Fin 3) _) i j) :=
    fun g w i j => congrFun (congrFun (B.bG_loc g w) i) j
  have hi : ∀ (g : GA B.Δ) (w : Plc L) (i j : Fin 3),
      (((cLoc w (B.bG g : UA L 3))⁻¹ : GL (Fin 3) (Kw w)) : Matrix (Fin 3) (Fin 3) (Kw w)) i j
        = B.ρ _ w rfl (star ((g.1 (un w) : Matrix (Fin 3) (Fin 3) _) j i)) := by
    intro g w i j
    have h := hm g⁻¹ w i j
    rw [B.bG.map_inv, InvMemClass.coe_inv, map_inv] at h
    exact h
  refine ⟨fun g v => ?_, fun g v => ?_, fun w S g => ?_⟩
  · constructor
    · intro hK w h
      subst h
      rw [mem_KGL_iff]
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · rw [hm]
        exact (B.ρ_int _ _).1 (hK i j).1 w rfl
      · rw [hi]
        exact (B.ρ_int _ _).1 (hK j i).2 w rfl
    · intro H i j
      refine ⟨(B.ρ_int _ _).2 fun w h => ?_, (B.ρ_int _ _).2 fun w h => ?_⟩
      · subst h
        have := ((mem_KGL_iff _ _).1 (H w rfl)).1 i j
        rwa [hm] at this
      · subst h
        have := ((mem_KGL_iff _ _).1 (H w rfl)).2 j i
        rwa [hi] at this
  · constructor
    · intro h1 w h
      subst h
      apply Units.ext
      have := B.bG_loc g w
      rw [h1] at this
      refine this.trans ?_
      exact Matrix.map_one _ (map_zero _) (map_one _)
    · intro H
      apply Subtype.ext
      refine Matrix.ext fun i j => ?_
      apply sub_eq_zero.1
      apply B.ρ_inj
      intro w h
      cases h
      have e2 := hm g w i j
      rw [H w rfl, Units.val_one] at e2
      have e3 : B.ρ _ w rfl ((1 : Matrix (Fin 3) (Fin 3) (Lsq (Kv (un w)) (cv (un w) B.Δ))) i j) = (1 : Matrix (Fin 3) (Fin 3) (Kw w)) i j :=
        congrFun (congrFun (Matrix.map_one (B.ρ _ w rfl) (map_zero _) (map_one _)) i) j
      rw [map_sub, ← e2]
      exact sub_eq_zero.2 e3.symm
  · apply Units.ext
    refine (B.bG_loc g w).trans ?_
    refine Matrix.ext fun i j => ?_
    exact S.ρ_eq _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.PhiGUnitary
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private noncomputable def phiG {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L) :
    U3 R.Δ →* GL (Fin 3) L :=
  (GeneralLinearGroup.map (R.e : Lsq (Lp L) R.Δ →+* L)).comp Unitary.toUnits

private theorem phiG_coe {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L) (γ : U3 R.Δ) :
    (phiG R γ : Matrix (Fin 3) (Fin 3) L) = (γ : Matrix (Fin 3) (Fin 3) _).map fun x => R.e x := rfl

private theorem phiG_unitary {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L) (γ : U3 R.Δ) :
    ((phiG R γ : Matrix (Fin 3) (Fin 3) L).map (IsCMField.complexConj L))ᵀ * (phiG R γ : Matrix (Fin 3) (Fin 3) L) = 1 := by
  have h : star (γ : Matrix (Fin 3) (Fin 3) (Lsq (Lp L) R.Δ)) * (γ : Matrix (Fin 3) (Fin 3) (Lsq (Lp L) R.Δ)) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp γ.2
  have e1 : ((phiG R γ : Matrix (Fin 3) (Fin 3) L).map (IsCMField.complexConj L))ᵀ =
      (star (γ : Matrix (Fin 3) (Fin 3) (Lsq (Lp L) R.Δ))).map fun x => R.e x := by
    ext i j
    simp [phiG_coe, Matrix.star_apply, R.e_star]
  rw [e1, phiG_coe]
  have e2 := congrArg (fun m => m.map (R.e : Lsq (Lp L) R.Δ →+* L)) h
  simp only [Matrix.map_mul] at e2
  simpa using e2

theorem UpperTheory.V.Z.Sym.Dict.Br.rGEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L), ∃ r : U3 R.Δ ≃* ratU L 3, (∀ γ w, mL w (r γ : UA L 3) = (γ : Matrix (Fin 3) (Fin 3) _).map fun x => algebraMap L (Kw w) (R.e x)) ∧ ∀ γ (τ : L →+* ℂ), (cEmb τ (r γ : UA L 3) : Matrix (Fin 3) (Fin 3) ℂ) = (γ : Matrix (Fin 3) (Fin 3) _).map fun x => τ (R.e x) := by
  intro L _ _ _ R
  have hU : ∀ γ : U3 R.Δ, ratGL L 3 (phiG R γ) ∈ UA L 3 := fun γ =>
    (ratFacts L 3 (phiG R γ)).1.mpr (phiG_unitary R γ)
  let f : U3 R.Δ →* ratU L 3 :=
    { toFun := fun γ => ⟨⟨ratGL L 3 (phiG R γ), hU γ⟩, Subgroup.mem_subgroupOf.mpr ⟨phiG R γ, rfl⟩⟩
      map_one' := by
        apply Subtype.ext; apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext; apply Subtype.ext
        simp }
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : ratGL L 3 (phiG R a) = ratGL L 3 (phiG R b) := congrArg Subtype.val (congrArg Subtype.val hab)
    have h2 := (ratFacts L 3 1).2.1 h1
    have h3 : (phiG R a : Matrix (Fin 3) (Fin 3) L) = phiG R b := congrArg Units.val h2
    apply Subtype.ext
    exact Matrix.ext fun i j => R.e.injective (congrFun (congrFun h3 i) j)
  have hsurj : Function.Surjective f := by
    rintro ⟨⟨x, hx⟩, hr⟩
    obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.mp hr
    change ratGL L 3 g = x at hg
    subst hg
    have hc := (ratFacts L 3 g).1.mp hx
    let M : Matrix (Fin 3) (Fin 3) (Lsq (Lp L) R.Δ) := (g : Matrix (Fin 3) (Fin 3) L).map fun x => R.e.symm x
    have hM : star M * M = 1 := by
      have e1 : star M = (((g : Matrix (Fin 3) (Fin 3) L).map (IsCMField.complexConj L))ᵀ).map fun x => R.e.symm x := by
        refine Matrix.ext fun i j => R.e.injective ?_
        simp [M, Matrix.star_apply, R.e_star]
      have e2 := congrArg (fun m => m.map (R.e.symm : L →+* Lsq (Lp L) R.Δ)) hc
      simp only [Matrix.map_mul] at e2
      rw [e1]
      simpa [M] using e2
    refine ⟨⟨M, Matrix.mem_unitaryGroup_iff'.mpr hM⟩, ?_⟩
    have hp : phiG R ⟨M, Matrix.mem_unitaryGroup_iff'.mpr hM⟩ = g := by
      apply Units.ext
      ext i j
      simp [phiG_coe, M]
    apply Subtype.ext; apply Subtype.ext
    exact congrArg (ratGL L 3) hp
  refine ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, ?_, ?_⟩
  · intro γ w
    exact ((ratFacts L 3 (phiG R γ)).2.2 (hU γ)).1 w
  · intro γ τ
    exact ((ratFacts L 3 (phiG R γ)).2.2 (hU γ)).2.1 τ
end

