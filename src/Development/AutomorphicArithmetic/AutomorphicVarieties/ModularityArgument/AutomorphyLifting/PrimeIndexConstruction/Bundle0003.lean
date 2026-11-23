module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadraticInductionGL2Alt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.AutomorphyRankFourPolarizedAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0240
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.AwOne
section
theorem UpperTheory.V.Z.Win.Birth.awOne :
    UpperTheory.V.Z.Win.Birth.AwOne := by
  intro F Ω _ _ _ _ _ _ l _ n hn ι r π hπ hwin π' _ hπ'
  obtain ⟨t, ht⟩ := hwin
  refine ⟨t, fun v => UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.suppSmo F n hn π π' ?_ t v (ht v)⟩
  filter_upwards [hπ.2, hπ'.2] with w h1 h2
  obtain ⟨B, hB, hE⟩ := h1
  obtain ⟨B', hB', hE'⟩ := h2
  have e : B = B' := (UpperTheory.hecke_eigenvalue_basic_properties F Ω l ι w).2.2 n r B B' hE hE'
  exact ⟨B, hB, e ▸ hB'⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.RankFourAutomorphyOfTensor
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2 UpperTheory.V.Sd.S3 UpperTheory.V.Cu

namespace UpperTheory.V.Z.Win.Birth

theorem mkCsdW {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} [IsCMField F]
    {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} (h : UpperTheory.GalN.V.AutCsd0 ι r) (_ : Continuous r → WitA ι r) : IsAutCsd ι r := h

theorem mkCsdW' {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} [IsCMField F]
    {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} (h : UpperTheory.GalN.V.AutCsd0 ι r) (u : Continuous r → WitA ι r) : IsAutCsdA ι r := ⟨h, u⟩

def SphOfUnrW : Prop :=
  ∀ (M Ω : Type) [Field M] [NumberField M] [IsCMField M] [Field Ω] [Algebra M Ω] [IsAlgClosure M Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (r : G M Ω →* GL (Fin n) (Qbar l)) (π : CuspSub M n), Continuous r → Sol.Pol ι r →
    (CG.mk π).IsRegAlg → AttC ι r π → AllW ι r → ∀ w : HeightOneSpectrum (𝓞 M), ((l : ℕ) : 𝓞 M) ∉ w.asIdeal →
    ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ s ∈ Ine (F := M) A, r s = 1) → ∃ B, (CG.mk π).HasSat w B

def BadOfW : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (K' L M : IntermediateField ℚ Ω)
    [NumberField L] [NumberField M] [IsCMField M] [Algebra L M] [IsScalarTower L M Ω] [IsAlgClosure M Ω] [IsGalois L M], M = K' ⊔ L →
    ∀ (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (r : G M Ω →* GL (Fin 2) (Qbar l)) (π : CuspSub M 2), GoodAt K' L ρ → Continuous r → Af.Sol.Pol ι r →
    (CG.mk π).IsRegAlg → AttC ι r π → AllW ι r →
    (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := M) A, ρ (resQ M s) = 1 → r s = 1) → Z.InvariantSubmoduleMonicPolynomial.E.SplitBad L π

def IndAutLP : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D)
    (k₀ : IntermediateField ℚ Ω) [NumberField k₀] [IsTotallyReal k₀] (φ : G ℚ Ω →* (Qbar l)ˣ) (ι : Qbar l ≃+* ℂ) (k t : ℕ)
    (r : G k₀ Ω →* GL (Fin 2) (Qbar l)) (α β : (Qbar l)ˣ) (R : G ℚ Ω →* GL (Fin 4) (Qbar l)) (δ : G T.F Ω →* (Qbar l)ˣ),
    IndDat T k₀ φ ι k t r α β R δ → PR ι r → IsAutC ι (R.comp (resQ T.L)) ∧ AllW ι (R.comp (resQ T.L))

def OffW {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (K' : IntermediateField ℚ Ω)
    (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (R : G ℚ Ω →* GL (Fin 4) (Qbar l)) : Prop :=
  ∀ (L : IntermediateField ℚ Ω) [NumberField L] [_root_.NumberField.IsTotallyComplex L], IsAbelianGalois ℚ L → ¬ K' ≤ L → GoodAt K' L ρ →
    IsIrr (R.comp (resQ L)) → AllW ι (R.comp (resQ L))

def RankFourAutomorphyOfTensor : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (K' : IntermediateField ℚ Ω) [NumberField K'], Module.finrank ℚ K' = 2 → IsTotallyComplex K' →
    ∀ ρ : G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous ρ → IsAutR ι ρ → IrrOpen ρ → PR ι ρ →
    ∀ (g0 : G ℚ Ω) (m : ℕ) (c₁ : Coef l) (κ : G K' Ω →* (Qbar l)ˣ), g0 ∉ K'.fixingSubgroup →
    (∃ τ s, TauDat ι K' g0 (m * 1) c₁ τ s (κ ^ 1)) →
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ 9 ∧ ∀ (ρ₁ τ : G ℚ Ω →* M2 c₁.O) s, RepIso ρ (mapRep (algebraMap c₁.O (PadicAlgCl l)) ρ₁).toHomUnits →
      TauDat ι K' g0 (m * j) c₁ τ s (κ ^ j) → AutOffS ι K' ρ (tenB ρ₁ τ) ∧ OffW ι K' ρ (tenB ρ₁ τ)

def AwChain : Prop :=
  ∀ (F E M Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M]
    [Field Ω] [Algebra F E] [Algebra E M] [Algebra F Ω] [Algebra E Ω] [Algebra M Ω] [IsScalarTower F E Ω] [IsScalarTower E M Ω] [IsAlgClosure F Ω]
    [IsAlgClosure M Ω] [IsGalois E M] [Group.IsSolvable (M ≃ₐ[E] M)], Module.finrank F E = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : G F Ω →* GL (Fin 2) (Qbar l)) (κ : G E Ω →* (Qbar l)ˣ), Continuous r → PR ι r → Sd.IsAlgChar ι κ →
    IsIrr ((r.comp (galEmb F E Ω)).comp (galEmb E M Ω)) → AllW ι ((tw (r.comp (galEmb F E Ω)) κ).comp (galEmb E M Ω))

def PotOrd : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (m : Fin n → ℤ) (ψ : Fin n → G F Ω →* (Qbar l)ˣ) (κ : G F Ω →* (Qbar l)ˣ), (∀ i j, m i ≠ m j + 1) →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → OrdAt r m ψ A) →
    ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → PotUnl (tw r κ) v

end UpperTheory.V.Z.Win.Birth
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.SphPlain
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.RoadU GlobalTheory.LocLanglands UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.Birth

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem ofChar_ne_nu (θ : kˣ →* ℂˣ) (hθ : IsSmoothChar θ) : IrrGL.ofChar θ hθ ≠ (IrrGL.ofChar θ hθ).nu 1 := by
  intro e
  rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at e
  have h1 : absPow k 1 = 1 := mul_left_cancel (a := θ) (by rw [mul_one]; exact e.symm)
  have h2 : absPow k ((1 : ℝ) : ℂ) = 1 := by simpa using h1
  exact one_ne_zero (absPow_ofReal_eq_one.1 h2)

private theorem carrier_of_len {D : Segment k} (h : D.len = 1) : D.carrier = {D.first} := by
  ext x
  rw [Segment.mem_carrier, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain rfl : n = 0 := by omega
    simp
  · rintro rfl
    exact ⟨0, by omega, by simp⟩

private theorem linked_of_len {D D' : Segment k} (h : D.len = 1) (h' : D'.len = 1) (θ : kˣ →* ℂˣ) (hθ : IsSmoothChar θ)
    (e' : D'.first = IrrGL.ofChar θ hθ) (e : D.first = D'.first.nu 1) : D.Linked D' := by
  have hne : D.first ≠ D'.first := by
    rw [e, e']
    exact fun h => ofChar_ne_nu θ hθ h.symm
  rw [Segment.Linked, carrier_of_len h, carrier_of_len h']
  refine ⟨⟨Segment.ofChar θ hθ 2 (by norm_num), ?_⟩, ?_, ?_⟩
  · have hf : (Segment.ofChar θ hθ 2 (by norm_num)).first = D'.first := e'.symm
    have hl : (Segment.ofChar θ hθ 2 (by norm_num)).len = 2 := rfl
    ext x
    simp only [Segment.mem_carrier, Set.mem_union, Set.mem_singleton_iff]
    rw [hl, hf]
    constructor
    · rintro ⟨n, hn, rfl⟩
      obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
      · right
        simp
      · left
        simpa using e.symm
    · rintro (rfl | rfl)
      · exact ⟨1, by omega, by simpa using e.symm⟩
      · exact ⟨0, by omega, by simp⟩
  · simpa using hne
  · simpa using hne.symm

end Local

theorem plainTor_of_sph {E : Type} [Field E] [NumberField E] {N : ℕ} (hN : 1 ≤ N) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin N) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B)
    (hg : IsGeneric σ.ρ) : PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) := by
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨ξ, hξ, ϖ, hs, -, -, -⟩ := GlobalTheory.SatSupp.hasSupport_of_hasSatGL E N hN w σ B hB
  obtain ⟨α, -, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ B).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hB⟩)
  obtain ⟨h, Δ, y, hd, hun, hL, ⟨φ⟩⟩ := GlobalTheory.RgGu.Holds.genericUnlinkedGL_holds _ N σ.V σ.ρ σ.smooth σ.irred hg
  have hsub : IsSubquotient σ.ρ (prodIrr y hd) :=
    IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective
  have hsp := GlobalTheory.LocLanglands.SphFac.isSpherical_factor _ h N y hd σ.V σ.ρ hsub hα.2.1
  have h1 : ∀ i, (y i).1 = 1 := fun i => GlobalTheory.TempSat.deg_eq_one_of_isLSeg (hL i) (hsp i)
  have hlen : ∀ i, (Δ i).len = 1 := fun i => by
    have h2 := (hL i).deg_eq
    rw [h1 i, Segment.deg] at h2
    exact Nat.eq_one_of_mul_eq_one_right h2
  have hG : GlobalTheory.Published.GeometricLemma :=
    GlobalTheory.geometricLemma_of_filtration GlobalTheory.Laid.bzfin_holds GlobalTheory.geometricLemmaFiltration_holds
  have hs2 : HasSupport σ.ρ (∑ i, (Δ i).ms) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (fun i => (hL i).hasSupport) σ.irred hsub
  have he : ∑ i, (Δ i).ms = chars ξ hξ :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG GlobalTheory.Laid.bzfin_holds hs2
      (hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm)
  refine ⟨chars ξ hξ, hs, fun z hz => ?_, fun a ha b hb e => ?_⟩
  · obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
    rfl
  · obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 hb
    rw [← he] at ha hb
    obtain ⟨i, -, hi⟩ := Multiset.mem_sum.1 ha
    obtain ⟨i', -, hi'⟩ := Multiset.mem_sum.1 hb
    have ea : a = (Δ i).first := by
      have := Segment.mem_ms.1 hi
      rwa [carrier_of_len (hlen i)] at this
    have eb : b = (Δ i').first := by
      have := Segment.mem_ms.1 hi'
      rwa [carrier_of_len (hlen i')] at this
    subst ea
    by_cases hii : i = i'
    · subst hii
      rw [← eb] at e
      subst hj
      exact ofChar_ne_nu _ _ e
    · exact hun i i' hii (linked_of_len (hlen i) (hlen i') (ξ j) (hξ j) (eb ▸ hj.symm) (eb ▸ e))

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

open Matrix in
theorem plainAtR_of_hasSat {n : ℕ} (hn : 1 ≤ n) (π : TR.CuspSub F n) (v : HeightOneSpectrum (𝓞 F)) (B : Multiset ℂˣ)
    (hB : π.HasSat v B) : PlainAtR π v := by
  intro σ hσ
  refine plainTor_of_sph hn v σ B ?_ (isGeneric_of_isLocCompR n π v σ hσ)
  obtain ⟨f, hf0, hf⟩ := hσ
  let Intertwiners := {T : σ.V →ₗ[ℂ] π.V // ∀ g x, T (σ.ρ g x) = π.locRep v g (T x)}
  let W : Submodule ℂ π.V := ⨆ T : Intertwiners, LinearMap.range T.1
  have commute_mem (T : Module.End ℂ π.V) (hT : ∀ g x, T (π.locRep v g x) = π.locRep v g (T x)) :
      ∀ x ∈ W, T x ∈ W := by
    refine iSup_le (a := Submodule.comap T W) (fun S => ?_)
    rintro _ ⟨x, rfl⟩
    exact Submodule.mem_iSup_of_mem (⟨T ∘ₗ S.1, fun g y => by
      rw [LinearMap.comp_apply, S.2, hT]; rfl⟩ : Intertwiners) ⟨x, rfl⟩
  have loc_mem (g : GL (Fin n) (v.adicCompletion F)) : ∀ x ∈ W, π.locRep v g x ∈ W := by
    refine iSup_le (a := Submodule.comap (π.locRep v g) W) (fun T => ?_)
    rintro _ ⟨x, rfl⟩
    exact Submodule.mem_iSup_of_mem T ⟨σ.ρ g x, T.2 g x⟩
  have op_mem (o : TR.Op F n) : ∀ x ∈ W, π.op o x ∈ W := by
    intro x hx
    cases o with
    | fin k =>
      let g := GeneralLinearGroup.map (pLoc F v) k
      let k' := (locGL F n v g)⁻¹ * k
      have hk' : GeneralLinearGroup.map (pLoc F v) k' = 1 := GlobalTheory.CuspRep.LocEx.map_pLoc_inv_mul v k
      have h := loc_mem g _ (commute_mem (π.finPart k') (fun u y => by
        simp only [TR.CuspSub.locRep, MonoidHom.comp_apply]
        rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul,
          GlobalTheory.CuspRep.LocUniq.comm_locGL v hk']) x hx)
      change π.finPart k x ∈ W
      rwa [TR.CuspSub.locRep, MonoidHom.comp_apply, ← mul_apply_eq_comp, ← map_mul,
        show locGL F n v g * k' = k from mul_inv_cancel_left _ _] at h
    | cpt k =>
      exact commute_mem (π.op (.cpt k)) (fun g y => by
        apply Subtype.ext
        change (TR.rt F n (TR.infGL F n (Unitary.toUnits k)) * TR.rt F n (finGL F n (locGL F n v g))) y.1 =
          (TR.rt F n (finGL F n (locGL F n v g)) * TR.rt F n (TR.infGL F n (Unitary.toUnits k))) y.1
        rw [← map_mul, ← map_mul, TR.infGL_comm]) x hx
    | lie X =>
      exact commute_mem (π.op (.lie X)) (fun g y => Subtype.ext
        (LinearMap.congr_fun (TR.lie_rt_fin X (locGL F n v g)) y.1)) x hx
  have htop : W = ⊤ := by
    have hinj := Submodule.map_injective_of_injective π.V.injective_subtype
    rcases π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
      rintro o _ ⟨x, hx, rfl⟩
      exact ⟨_, op_mem o x hx, rfl⟩) with h | h
    · have hbot : W = ⊥ := hinj (h.trans (Submodule.map_bot _).symm)
      exact (hf0 (LinearMap.range_eq_bot.1 ((iSup_eq_bot.1 hbot) (⟨f, hf⟩ : Intertwiners)))).elim
    · exact hinj (h.trans (Submodule.map_subtype_top _).symm)
  obtain ⟨x, hx⟩ := hB.exists_vec
  have hxW : x ∈ W := htop ▸ Submodule.mem_top
  obtain ⟨y, hy0, hy⟩ := GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup (π.locRep v) σ.ρ σ.irred
    (fun T : Intertwiners => T.1) (fun T => T.2) (GlobalTheory.LFun.KGL v (n := n) : Set _) x hx.1
    (fun k hk => GlobalTheory.LGrp.mem_fixed.1 hx.2.1 k hk) hxW
  refine ⟨(Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.LGrp.mem_fixed.2 hy, hy0⟩, ?_⟩
  intro z hz hz0
  have hker : LinearMap.ker f = ⊥ := ((GlobalTheory.CuspRep.isIrreducible_iff σ.ρ).1 σ.irred).2 _ (fun g u hu => by
    rw [LinearMap.mem_ker] at hu ⊢
    rw [hf, hu, map_zero]) |>.resolve_right fun h => hf0 (LinearMap.ker_eq_top.1 h)
  have hinj := LinearMap.ker_eq_bot.1 hker
  exact GlobalTheory.LFun.IsSatVecGL.of_map f hf hinj
    (hB.2 _ (GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← hf, GlobalTheory.LGrp.mem_fixed.1 hz k hk])
      (fun h => hz0 (hinj (h.trans (map_zero f).symm))))

end UpperTheory.V.Z.Win.Birth
end
end

