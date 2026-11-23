module

public import Mathlib
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.Bundle0003
public import ReciprocityTheory.GaloisValuations.GlobalA
public import GroundTheory.GlobalFields.CompletionAtPlace.Inertia
public import GroundTheory.LocalFields.UnramifiedGalois
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.Bundle0004
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsRep
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsChi
section
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion ValuativeRel

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem natCast_card_pow_sub_one_notMem (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (hn : n ≠ 0) :
    ((Nat.card 𝓀[v.adicCompletion F] ^ n - 1 : ℕ) : 𝓞 F) ∉ v.asIdeal := by
  intro h
  have h1 := (GroundTheory.Global.ringOfIntegersToInteger_mem_maximalIdeal_iff v _).2 h
  rw [map_natCast] at h1
  apply GroundTheory.LocalField.natCast_card_pow_sub_one_ne_zero (K := v.adicCompletion F) hn
  rw [← map_natCast (IsLocalRing.residue 𝒪[v.adicCompletion F])]
  exact (IsLocalRing.residue_eq_zero_iff _).2 h1

theorem valuation_le_one_of_pow_eq_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ}
    (hm : m ≠ 0) {x : Ω} (hx : x ^ m = 1) : A.valuation x ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have : A.valuation x ^ m = 1 := by rw [← Valuation.map_pow, hx, Valuation.map_one]
  exact (one_lt_pow₀ h hm).ne' this

set_option maxHeartbeats 1000000 in
theorem exists_chi' (Kf : FiniteSubfield) [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
    (v : HeightOneSpectrum (𝓞 Kf.1)) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : IsPlaceOver A v)
    (N : ℕ+)
    (ι : AlgebraicClosure ℚ →ₐ[Kf.1] AlgebraicClosure (v.adicCompletion Kf.1))
    (ev : (AlgebraicClosure (v.adicCompletion Kf.1) ≃ₐ[v.adicCompletion Kf.1]
        AlgebraicClosure (v.adicCompletion Kf.1)) ≃* Dec (F := Kf.1) A)
    (hev : ∀ σ x, ι (((ev σ : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) x) = σ (ι x)) :
    ∃ χ : Dec (F := Kf.1) A → ZMod (N : ℕ),
      (∀ g h, χ (g * h) = χ g + χ h) ∧
      (∀ g : Dec (F := Kf.1) A, (g : G Kf.1 (AlgebraicClosure ℚ)) ∈ Ine (F := Kf.1) A → χ g = 0) ∧
      (∀ g : Dec (F := Kf.1) A, IsFrob (F := Kf.1) A (normV v) (g : G Kf.1 (AlgebraicClosure ℚ)) →
        χ g = 1) ∧
      Continuous χ ∧
      ∀ σ, χ (ev σ) = urChar (v.adicCompletion Kf.1) (AlgebraicClosure (v.adicCompletion Kf.1)) N σ := by

  classical
  have hm0 : (Nat.card 𝓀[v.adicCompletion Kf.1] ^ (N : ℕ) - 1) ≠ 0 := by
    have := GroundTheory.LocalField.one_lt_card_residueField_pow (K := v.adicCompletion Kf.1) N.ne_zero
    omega
  haveI : NeZero (Nat.card 𝓀[v.adicCompletion Kf.1] ^ (N : ℕ) - 1) := ⟨hm0⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (Nat.card 𝓀[v.adicCompletion Kf.1] ^ (N : ℕ) - 1)
  have hιξ : IsPrimitiveRoot (ι ξ) (Nat.card 𝓀[v.adicCompletion Kf.1] ^ (N : ℕ) - 1) := hξ.map_of_injective ι.toRingHom.injective
  have hmA : ¬ A.valuation (((Nat.card 𝓀[v.adicCompletion Kf.1] ^ (N : ℕ) - 1) : ℕ) : AlgebraicClosure ℚ) < 1 := by
    intro h
    apply natCast_card_pow_sub_one_notMem Kf.1 v N.ne_zero
    refine (hA _).1 ?_
    simpa using h
  let χ : Dec (F := Kf.1) A → ZMod (N : ℕ) := fun g =>
    urChar (v.adicCompletion Kf.1) (AlgebraicClosure (v.adicCompletion Kf.1)) N (ev.symm g)
  have hχ : ∀ g, χ g = unramifiedCoord (v.adicCompletion Kf.1) (ev.symm g) N := fun g => rfl
  have hχev : ∀ σ, χ (ev σ) =
      urChar (v.adicCompletion Kf.1) (AlgebraicClosure (v.adicCompletion Kf.1)) N σ := fun σ => by
    show urChar _ _ N (ev.symm (ev σ)) = _
    rw [MulEquiv.symm_apply_apply]
  clear_value χ
  have key : ∀ (g : Dec (F := Kf.1) A) (a : ℕ),
      (a : ZMod (N : ℕ)) = χ g ↔ (g : G Kf.1 (AlgebraicClosure ℚ)) ξ = ξ ^ Nat.card 𝓀[v.adicCompletion Kf.1] ^ a := by
    intro g a
    rw [hχ, natCast_eq_unramifiedCoord_iff hιξ (ev.symm g) a, ← hev (ev.symm g) ξ,
      MulEquiv.apply_symm_apply, ← map_pow]
    exact ι.toRingHom.injective.eq_iff
  refine ⟨χ, fun g h => ?_, fun g hg => ?_, fun g hg => ?_, ?_, fun σ => ?_⟩
  · rw [hχ, hχ, hχ, map_mul, unramifiedCoord_mul]
  · have hgx := hg.2 ξ (valuation_le_one_of_pow_eq_one A hm0 hξ.pow_eq_one)
    have e : (g : G Kf.1 (AlgebraicClosure ℚ)) ξ = ξ :=
      eq_of_pow_eq_one A hmA (by rw [← map_pow, hξ.pow_eq_one, map_one]) hξ.pow_eq_one hgx
    have := (key g 0).2 (by rw [pow_zero, pow_one]; exact e)
    rw [← this, Nat.cast_zero]
  · have hgx := hg.2 ξ (valuation_le_one_of_pow_eq_one A hm0 hξ.pow_eq_one)
    have hN : normV v = Nat.card 𝓀[v.adicCompletion Kf.1] := (natCard_residueField_integer v).symm
    rw [hN] at hgx
    have e : (g : G Kf.1 (AlgebraicClosure ℚ)) ξ = ξ ^ Nat.card 𝓀[v.adicCompletion Kf.1] :=
      eq_of_pow_eq_one A hmA (by rw [← map_pow, hξ.pow_eq_one, map_one])
        (by rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]) hgx
    have := (key g 1).2 (by rw [pow_one]; exact e)
    rw [← this, Nat.cast_one]
  · refine continuous_def.2 fun s _ => ?_
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨Subtype.val ⁻¹' {τ : G Kf.1 (AlgebraicClosure ℚ) | τ ξ = (g : G Kf.1 (AlgebraicClosure ℚ)) ξ},
      fun g' hg' => ?_, continuous_subtype_val.isOpen_preimage _
        (isOpen_setOf_apply (F := Kf.1) ξ (fun y => y = (g : G Kf.1 (AlgebraicClosure ℚ)) ξ)), rfl⟩
    have h1 := (key g (χ g).val).1 (ZMod.natCast_zmod_val _)
    have h2 : (((χ g).val : ℕ) : ZMod (N : ℕ)) = χ g' := (key g' (χ g).val).2 (by
      rw [show (g' : G Kf.1 (AlgebraicClosure ℚ)) ξ = (g : G Kf.1 (AlgebraicClosure ℚ)) ξ from hg', h1])
    rw [ZMod.natCast_zmod_val] at h2
    show χ g' ∈ s
    rw [← h2]; exact hg
  · exact hχev σ

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsData
section
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
  GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

structure FoundData (Kf : FiniteSubfield) [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
    (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) (l r : ℕ) [Fact l.Prime] (ζ : AlgebraicClosure ℚ)
    (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M) where
  e : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) ≃ₜ*
    galUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))
  he : ∀ (σ : G Kf.1 (AlgebraicClosure ℚ))
    (y : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))),
    ((e (toGS (AlgebraicClosure ℚ) _ σ) y :
      maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) :
        AlgebraicClosure ℚ) = σ (y : AlgebraicClosure ℚ)
  ιs : ∀ v : (S : Set (HeightOneSpectrum (𝓞 Kf.1))), AlgebraicClosure ℚ →ₐ[Kf.1]
    AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)
  ev : ∀ v : S, (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
      (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ≃* Dec (F := Kf.1) (Av v)
  hev_cont : ∀ v, Continuous (ev v) ∧ Continuous (ev v).symm
  hev : ∀ (v : S) σ, e (locFam S Av v (ev v σ)) =
    gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩ σ
  hιs : ∀ (v : S) σ x, ιs ⟨v.1, Finset.mem_coe.2 v.2⟩
    (((ev v σ : Dec (F := Kf.1) (Av v)) : G Kf.1 (AlgebraicClosure ℚ)) x) =
      σ (ιs ⟨v.1, Finset.mem_coe.2 v.2⟩ x)
  A : Rep.{0} (ULift.{0} ℤ)
    (galUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))
  isDiscrete : IsDiscreteRep A
  eM : M ≃+ A.V
  hM : ∀ g m, eM (ρ g m) = A.ρ (e g) (eM m)
  eD : TDual (ZMod (l ^ r)) M ≃+
    (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) A).V
  hD : ∀ g f, eD (twDual μ ρ g f) =
    (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) A).ρ (e g) (eD f)
  hDζ : ∀ f m, ((((Additive.toMul ((eD f : A.V →ₗ[ULift.{0} ℤ] _) (eM m)) :
      rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ)
        (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) :
      (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) :
        maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) :
          AlgebraicClosure ℚ) = ζ ^ (f m).val

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsHasse
section
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

section Hasse

variable {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem urChar_mul (N : ℕ+) (g h : Gal(Ω/K)) :
    urChar K Ω N (g * h) = urChar K Ω N g + urChar K Ω N h := by
  simp only [urChar, map_mul, toAdd_mul, map_add (f := _)]

theorem urChar_one (N : ℕ+) : urChar K Ω N 1 = 0 := by
  simp only [urChar, map_one, toAdd_one, map_zero]

theorem urChar_of_ker (N : ℕ+) {g : Gal(Ω/K)} (hg : unramifiedDegree K Ω g = 1) :
    urChar K Ω N g = 0 := by
  simp only [urChar, hg, toAdd_one, map_zero]

theorem urChar_of_deg_one (N : ℕ+) {g : Gal(Ω/K)}
    (hg : unramifiedDegree K Ω g = Multiplicative.ofAdd 1) : urChar K Ω N g = 1 := by
  simp only [urChar, hg, toAdd_ofAdd, map_one]

theorem continuous_urChar (N : ℕ+) : Continuous (urChar K Ω N) :=
  continuous_unramifiedCoord (K := K) (Ω := Ω) N

def urPsi (N : ℕ+) : Additive Gal(Ω/K) →ₜ+ QZ where
  toFun a := zmodToQZ (N : ℕ) (urChar K Ω N (Additive.toMul a))
  map_zero' := by simp only [toMul_zero, urChar_one, map_zero]
  map_add' a b := by simp only [toMul_add, urChar_mul, map_add (f := _)]
  continuous_toFun :=
    (continuous_of_discreteTopology.comp (continuous_urChar (K := K) (Ω := Ω) N)).comp
      continuous_toMul

theorem reprIco_urPsi (N : ℕ+) (g : Gal(Ω/K)) :
    reprIco (charAdd (urPsi (K := K) (Ω := Ω) N) (Additive.ofMul g)) =
      ((urChar K Ω N g).val : ℚ) / (N : ℕ) := by
  rw [charAdd_apply]
  have h1 : (urPsi (K := K) (Ω := Ω) N) (Additive.ofMul g) =
      QZ.mk (((urChar K Ω N g).val : ℤ) / ((N : ℕ) : ℤ)) := by
    show zmodToQZ (N : ℕ) (urChar K Ω N g) = _
    conv_lhs => rw [← ZMod.intCast_zmod_cast (urChar K Ω N g)]
    rw [zmodToQZ_intCast, ZMod.cast_eq_val]
    push_cast
    rfl
  rw [h1]
  have h2 : QZ.toAddCircle (QZ.mk (((urChar K Ω N g).val : ℤ) / ((N : ℕ) : ℤ))) =
      ((((urChar K Ω N g).val : ℚ) / (N : ℕ) : ℚ) : AddCircle (1 : ℚ)) := by
    simp [QZ.mk]
  rw [h2, reprIco_coe]
  have hN : (0 : ℚ) < (N : ℕ) := by exact_mod_cast N.pos
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hN]
  exact_mod_cast ZMod.val_lt (urChar K Ω N g)

theorem charCocycle_urPsi (N : ℕ+) (g h : Gal(Ω/K)) :
    ((N : ℕ) : ℤ) * charCocycle (charAdd (urPsi (K := K) (Ω := Ω) N)) (g, h) =
      ((urChar K Ω N g).val : ℤ) + (urChar K Ω N h).val - (urChar K Ω N (g * h)).val := by
  have e := charCocycle_cast (charAdd (urPsi (K := K) (Ω := Ω) N)) g h
  rw [reprIco_urPsi, reprIco_urPsi, reprIco_urPsi] at e
  have hN : ((N : ℕ) : ℚ) ≠ 0 := by exact_mod_cast N.ne_zero
  have : (((N : ℕ) : ℤ) * charCocycle (charAdd (urPsi (K := K) (Ω := Ω) N)) (g, h) : ℚ) =
      (((urChar K Ω N g).val : ℤ) + (urChar K Ω N h).val - (urChar K Ω N (g * h)).val : ℤ) := by
    push_cast
    rw [e]
    field_simp
  exact_mod_cast this

end Hasse

section HasseC

variable {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem brauerInv_galCupClass_urPsi (N : ℕ+) (ϖ : Kˣ) (hϖ : ord (ϖ : K) = 1) :
    brauerInvZOfIsSepClosure K Ω (galCupClass K Ω (urPsi (K := K) (Ω := Ω) N) ϖ) =
      zmodToQZ (N : ℕ) 1 := by
  obtain ⟨σ, hσ⟩ := unramifiedDegree_surjective (K := K) (Ω := Ω) (Multiplicative.ofAdd 1)
  letI := algebraicValuativeRel K Ω
  letI := algebraicTopology K Ω
  haveI := algebraicTopology_isValuativeTopology K Ω
  haveI := algebraicValuativeRel_valuativeExtension K Ω
  have hψ : ∀ g ∈ (unramifiedDegree K Ω).ker,
      (urPsi (K := K) (Ω := Ω) N) (Additive.ofMul g) = 0 := by
    intro g hg
    show zmodToQZ (N : ℕ) (urChar K Ω N g) = 0
    rw [urChar_of_ker N (MonoidHom.mem_ker.1 hg), map_zero]
  have key := brauerInvZ_galCupClass_of_unramified (urPsi (K := K) (Ω := Ω) N) hψ hσ ϖ
  show brauerInvZ K Ω _ = _
  rw [key, hϖ, one_smul]
  show zmodToQZ (N : ℕ) (urChar K Ω N σ) = _
  rw [urChar_of_deg_one N hσ]

end HasseC

section HasseMain

variable {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem hasse_kummer_unram' (N : ℕ+)
    (ϖ : Kˣ) (hϖ : ord (ϖ : K) = 1) (Y : Ω) (hY : Y ^ (N : ℕ) = algebraMap K Ω ϖ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ N) (κ : Gal(Ω/K) → ZMod (N : ℕ))
    (hκ : ∀ g : Gal(Ω/K), g Y = ζ ^ (κ g).val * Y)
    (c : cocycles (galUnitsZ K Ω) 2)
    (hc : ∀ s : Fin 2 → Gal(Ω/K), ((Additive.toMul (cochainOf _ (cocycleι _ 2 c) s) : Ωˣ) : Ω) =
      ζ ^ (κ (s 0) * urChar K Ω N (s 1)).val) :
    brauerInvZOfIsSepClosure K Ω (cohomologyπ _ 2 c) = - zmodToQZ (N : ℕ) 1 := by
  classical
  have hN0 : (N : ℕ) ≠ 0 := N.ne_zero
  have hϖ0 : algebraMap K Ω (ϖ : K) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K Ω).injective).2 ϖ.ne_zero
  have hY0 : Y ≠ 0 := by
    rintro rfl
    rw [zero_pow hN0] at hY
    exact hϖ0 hY.symm
  let ψ := urPsi (K := K) (Ω := Ω) N
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupCharClassProf (galUnitsZ K Ω) ψ (unitsInvariant K Ω ϖ)
  let Yu : Ωˣ := Units.mk0 Y hY0
  let bf : Gal(Ω/K) → (galUnitsZ K Ω).V := fun h =>
    Additive.ofMul (Yu ^ (urChar K Ω N h).val)
  have hbf_lc : IsLocallyConstant fun t : Fin 1 → Gal(Ω/K) => bf (t 0) := by
    have h1 : IsLocallyConstant (urChar K Ω N) :=
      (IsLocallyConstant.iff_continuous _).2 (continuous_urChar (K := K) (Ω := Ω) N)
    exact (h1.comp fun u => Additive.ofMul (Yu ^ u.val)).comp_continuous (continuous_apply 0)
  have hsum : cohomologyπ _ 2 c + cohomologyπ _ 2 w = 0 := by
    rw [← map_add (f := _)]
    refine (PositivityTheory.LocalTateOrthogonality.Gcoh.pi_succ_eq_zero_iff (galUnitsZ K Ω) 1 (c + w)).2
      ⟨fun t => bf (t 0), hbf_lc, ?_⟩
    have hd := PositivityTheory.LocalTateOrthogonality.Gcoh.d_comp (galUnitsZ K Ω).ρ (galUnitsZ K Ω) (AddEquiv.refl _)
      (fun _ _ => rfl) 1 (fun t => bf (t 0))
    simp only [AddEquiv.refl_apply] at hd
    rw [hd]
    funext s
    rw [PositivityTheory.LocalTateOrthogonality.Gcoh.dn_one, map_add (f := _), cochainOf_add, Pi.add_apply]
    have hwc' := hwc s
    have hc' := hc s
    set a0 := (urChar K Ω N (s 0)).val with ha0
    set a1 := (urChar K Ω N (s 1)).val with ha1
    set a01 := (urChar K Ω N (s 0 * s 1)).val with ha01
    set cc := charCocycle (charAdd ψ) (s 0, s 1) with hcc
    have hrel : ((N : ℕ) : ℤ) * cc = (a0 : ℤ) + a1 - a01 := charCocycle_urPsi N (s 0) (s 1)
    apply Additive.toMul.injective
    apply Units.ext
    rw [hwc']
    simp only [toMul_add, toMul_sub, toMul_zsmul, Units.val_mul, Units.val_div_eq_div_val,
      Units.val_zpow_eq_zpow_val, bf]
    rw [hc', coe_unitsInvariant]
    have hL : ((Additive.toMul (((zRepOfMonoidEnd (galUnitsHom K Ω)) (s 0))
          (Additive.ofMul (Yu ^ (urChar K Ω N (s 1)).val)) -
          Additive.ofMul (Yu ^ (urChar K Ω N (s 0 * s 1)).val) +
          Additive.ofMul (Yu ^ (urChar K Ω N (s 0)).val)) : Ωˣ) : Ω) =
        (s 0) Y ^ a1 * (Y ^ a01)⁻¹ * Y ^ a0 := by
      show ((Additive.toMul ((Additive.ofMul (galUnitsHom K Ω (s 0) (Yu ^ a1)) : Additive Ωˣ) -
          Additive.ofMul (Yu ^ a01) + Additive.ofMul (Yu ^ a0)) : Ωˣ) : Ω) = _
      simp only [toMul_add, toMul_sub, toMul_ofMul, Units.val_mul, Units.val_div_eq_div_val,
        coe_galUnitsHom_apply, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Yu, Units.val_mk0,
        map_pow, div_eq_mul_inv]
    refine Eq.trans hL ?_
    rw [hκ (s 0), mul_pow]
    have hYz : Y ^ a1 * (Y ^ a01)⁻¹ * Y ^ a0 = (algebraMap K Ω (ϖ : K)) ^ cc := by
      rw [← hY, show (Y ^ (N : ℕ)) ^ cc = Y ^ (((N : ℕ) : ℤ) * cc) by rw [zpow_mul, zpow_natCast],
        hrel, zpow_sub₀ hY0, zpow_add₀ hY0, zpow_natCast, zpow_natCast, zpow_natCast]
      ring
    have hζN : ζ ^ (N : ℕ) = 1 := hζ.pow_eq_one
    have hzk : (ζ ^ (κ (s 0)).val) ^ a1 = ζ ^ (κ (s 0) * urChar K Ω N (s 1)).val := by
      rw [← pow_mul, ZMod.val_mul]
      conv_lhs => rw [← Nat.div_add_mod ((κ (s 0)).val * a1) (N : ℕ), pow_add, pow_mul, hζN,
        one_pow, one_mul]
    rw [← hzk, ← hYz]
    ring
  have hc0 : cohomologyπ _ 2 c = - cohomologyπ _ 2 w := eq_neg_of_add_eq_zero_left hsum
  rw [hc0, map_neg, hw]
  exact congrArg Neg.neg (brauerInv_galCupClass_urPsi (K := K) (Ω := Ω) N ϖ hϖ)

end HasseMain

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsKummer
section
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem exists_kummer' (F : Type) [Field F] [NumberField F] {l r : ℕ} [Fact l.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [Algebra F (AlgebraicClosure ℚ)]
    [IsAlgClosure F (AlgebraicClosure ℚ)]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r)) (a : F) (ha : a ≠ 0)
    (y : AlgebraicClosure ℚ) (hy : y ^ (l ^ r) = algebraMap F (AlgebraicClosure ℚ) a) :
    ∃ κ : Dec (F := F) A → ZMod (l ^ r),
      (∀ g : Dec (F := F) A, (g : G F (AlgebraicClosure ℚ)) y = ζ ^ (κ g).val * y) ∧
      Continuous κ ∧
      ∀ g h : Dec (F := F) A, κ (g * h) =
        κ g + ((cycMod F (AlgebraicClosure ℚ) l r (g : G F (AlgebraicClosure ℚ)) : (ZMod (l ^ r))ˣ) :
          ZMod (l ^ r)) * κ h := by
  classical
  have hN0 : l ^ r ≠ 0 := pow_ne_zero r (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ r) := ⟨hN0⟩
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, zero_pow hN0] at hy
    exact ha ((algebraMap F (AlgebraicClosure ℚ)).injective (by rw [← hy, map_zero]))

  have hroot : ∀ σ : G F (AlgebraicClosure ℚ), (σ y / y) ^ (l ^ r) = 1 := by
    intro σ
    rw [div_pow, ← map_pow, hy, AlgEquiv.commutes, ← hy, div_self (pow_ne_zero _ hy0)]
  have hex : ∀ σ : G F (AlgebraicClosure ℚ), ∃ i < l ^ r, ζ ^ i = σ y / y := fun σ => hζ.eq_pow_of_pow_eq_one (hroot σ)
  have hmod : ∀ a b : ℕ, ζ ^ a = ζ ^ b ↔ a ≡ b [MOD l ^ r] := by
    intro a b
    have hu : IsPrimitiveRoot (hζ.isUnit hN0).unit (l ^ r) :=
      IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
    have e : ζ ^ a = ζ ^ b ↔ (hζ.isUnit hN0).unit ^ a = (hζ.isUnit hN0).unit ^ b := by
      rw [Units.ext_iff]; simp
    rw [e, pow_eq_pow_iff_modEq, ← hu.eq_orderOf]

  have huniq : ∀ a b : ℕ, ζ ^ a * y = ζ ^ b * y → (a : ZMod (l ^ r)) = b := by
    intro a b h
    have h' : ζ ^ a = ζ ^ b := mul_right_cancel₀ hy0 h
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr ((hmod a b).mp h')
  let κ : Dec (F := F) A → ZMod (l ^ r) := fun g => ((hex (g : G F (AlgebraicClosure ℚ))).choose : ZMod (l ^ r))
  have hκ : ∀ g : Dec (F := F) A, (g : G F (AlgebraicClosure ℚ)) y = ζ ^ (κ g).val * y := by
    intro g
    have h1 := (hex (g : G F (AlgebraicClosure ℚ))).choose_spec
    have hv : (κ g).val = (hex (g : G F (AlgebraicClosure ℚ))).choose := ZMod.val_cast_of_lt h1.1
    rw [hv, h1.2, div_mul_cancel₀ _ hy0]
  have hκ_iff : ∀ (g : Dec (F := F) A) (b : ZMod (l ^ r)),
      κ g = b ↔ (g : G F (AlgebraicClosure ℚ)) y = ζ ^ b.val * y := by
    intro g b
    constructor
    · rintro rfl; exact hκ g
    · intro h
      have := huniq _ _ ((hκ g).symm.trans h)
      rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at this
  have : Algebra.IsIntegral F (AlgebraicClosure ℚ) := by
    have : Algebra.IsAlgebraic F (AlgebraicClosure ℚ) := IsAlgClosure.isAlgebraic
    infer_instance
  refine ⟨κ, hκ, ?_, ?_⟩
  · rw [continuous_discrete_rng]
    intro b
    have hset : κ ⁻¹' {b} = Subtype.val ⁻¹' {τ : G F (AlgebraicClosure ℚ) | τ y = ζ ^ b.val * y} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
      exact hκ_iff g b
    rw [hset]
    exact (isOpen_setOf_apply (F := F) y (fun z => z = ζ ^ b.val * y)).preimage continuous_subtype_val
  · intro g h
    set c := ((cycMod F (AlgebraicClosure ℚ) l r (g : G F (AlgebraicClosure ℚ)) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) with hc
    have hgζ : (g : G F (AlgebraicClosure ℚ)) ζ = ζ ^ c.val := by
      have hspec := cyclotomicCharacter.spec (L := AlgebraicClosure ℚ) l
        (MulSemiringAction.toRingAut (G F (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ) (g : G F (AlgebraicClosure ℚ))) ζ hζ.pow_eq_one
      exact hspec.trans (by rw [hc]; rfl)
    rw [hκ_iff]
    have e1 : ((g * h : Dec (F := F) A) : G F (AlgebraicClosure ℚ)) y = (g : G F (AlgebraicClosure ℚ)) ((h : G F (AlgebraicClosure ℚ)) y) := rfl
    rw [e1, hκ h, map_mul, map_pow, hgζ, hκ g, ← pow_mul, ← mul_assoc, ← pow_add]
    congr 1
    apply (hmod _ _).mpr
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring

end PositivityTheory.Lit1.PTN
end
end

