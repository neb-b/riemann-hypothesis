module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ConjAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeIsomorphicFields
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0855
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2750
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.PowEqOneOfKills

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.BcSplit
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Kato.WeilSphericalRecords

private theorem isIrr_comp {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k} {φ : Γ' →* Γ}
    (h : ∀ g, ∃ g', r g = r (φ g')) (hr : IsIrr r) : IsIrr (r.comp φ) :=
  ⟨hr.1, fun _ _ _ => trivial, fun W hW hi => hr.2.2 W hW fun g v hv => by
    obtain ⟨g', e⟩ := h g
    rw [e]
    exact hi g' v hv⟩

private theorem range_of_sign {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
    [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (hK : Module.finrank ℚ K = 2) {H : Type} [Group H] {r : G ℚ Ω →* H} {s : G ℚ Ω}
    (hs : s ∉ (Bc.res ℚ Ω K).range) (h1 : r s = 1) (g : G ℚ Ω) : ∃ g', r g = r (Bc.res ℚ Ω K g') := by
  obtain ⟨δ, -, -, ⟨ha, hb⟩, -⟩ := UpperTheory.exists_quadratic_sign_character ℚ K Ω l hK
  by_cases hg : δ g = 1
  · obtain ⟨g', rfl⟩ := (ha g).1 hg
    exact ⟨g', rfl⟩
  · have e : δ (g * s) = 1 := by
      rw [map_mul, (hb g).resolve_left hg, (hb s).resolve_left (mt (ha s).1 hs)]
      simp
    obtain ⟨g', e'⟩ := (ha _).1 e
    exact ⟨g', by rw [e', map_mul, h1, mul_one]⟩

private theorem dualTw_det {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) :
    DualTw r (Matrix.GeneralLinearGroup.det.comp r) := by
  refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], ?_, ?_⟩, fun s => ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_two]
  · have e : (r s : Matrix (Fin 2) (Fin 2) k) = !![(r s : Matrix (Fin 2) (Fin 2) k) 0 0, (r s : Matrix (Fin 2) (Fin 2) k) 0 1;
        (r s : Matrix (Fin 2) (Fin 2) k) 1 0, (r s : Matrix (Fin 2) (Fin 2) k) 1 1] := Matrix.eta_fin_two _
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply, Matrix.coe_units_inv]
    rw [e, Matrix.det_fin_two_of]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem polar_of_lift (hP : Hypotheses₂) {K Ω : Type} [Field K] [NumberField K] [IsCMField K] (hK : Module.finrank ℚ K = 2)
    {l : ℕ} [Fact l.Prime] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω]
    (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin 2) (Qbar l)) (wt : ℤ) (θ : G ℚ Ω →* (Qbar l)ˣ) (π : TR.CuspSub ℚ 2)
    (Q : CuspSub K 2) (hBC : Br.IsBC0 π Q) (hC : AttC ι (r.comp (Bc.res ℚ Ω K)) Q) (hθ : IsCycWt l wt θ) (hd : DualTw r θ) :
    ∃ χ, GlobalTheory.ContraPair.PolarizedPair Q χ := by
  haveI : IsScalarTower ℚ (maximalRealSubfield K) Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsAlgClosure (maximalRealSubfield K) Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩
  have hθ' : IsCycWt l (wt + (((2 : ℕ) : ℤ) - 1))
      (θ.comp (Bc.res ℚ Ω (maximalRealSubfield K)) * cycBar (maximalRealSubfield K) Ω l ^ (((2 : ℕ) : ℤ) - 1)) := by
    obtain ⟨M, χ, hM, hχ, rfl⟩ := hθ
    refine ⟨M, χ.comp (Bc.res ℚ Ω (maximalRealSubfield K)), hM, fun s hs => hχ _ hs, ?_⟩
    rw [zpow_add, mul_right_comm]
    rfl
  obtain ⟨hc, χ, art, a, ha⟩ := UpperTheory.exists_algebraic_heckeChar_cyclotomic hP.litN.aut.art _ Ω l ι _ _ hθ'
  have hL : IsLAdicCharOf ι χ _ := ⟨hc, art, a, ha⟩
  obtain ⟨χ', μ', hL', hN, hres, hs⟩ := UpperTheory.heckeChar_sign_fixed K Ω hK l ι χ _ hL 2
  have hres' : μ'.comp (Bc.res (maximalRealSubfield K) Ω K) =
      θ.comp (Bc.res ℚ Ω K) * cycBar K Ω l ^ (((2 : ℕ) : ℤ) - 1) := hres.trans rfl
  refine ⟨χ', hs, UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse hP.litN.aut.js.1 hP.litN.aut.gk K 2 one_le_two Q _ ?_⟩
  have hd' : DualTw (r.comp (Bc.res ℚ Ω K)) (θ.comp (Bc.res ℚ Ω K)) := let ⟨Q, hQ⟩ := hd; ⟨Q, fun s => hQ _⟩
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  filter_upwards [Bc.normGal K Ω l ι χ' μ' hL', Br.bcConj0 ℚ K 2 π Q hBC, hC.2, hl] with w ⟨hu, he⟩ ⟨B, hB, hB'⟩ ⟨B₁, hB₁, hF⟩ hw
  obtain rfl := hB.unique hB₁
  rw [hres'] at he
  exact ⟨hu, B, B, hB, hB', UpperTheory.frobenius_eigenvalues_dual K Ω l ι 2 _ _ hd' w hw B _ hF he⟩

private theorem qV_eq {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : Formalism.UG.qV E w = Ideal.absNorm w.asIdeal := by
  rw [Formalism.UG.qV]

private theorem absNorm_rat {l : ℕ} (hp : l.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    Ideal.absNorm v.asIdeal = l := by
  have hN : Ideal.absNorm (Ideal.span {((l : ℕ) : 𝓞 ℚ)}) = l := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]
  have hd : Ideal.absNorm v.asIdeal ∣ l :=
    hN ▸ Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hv)
  refine ((Nat.dvd_prime hp).1 hd).resolve_left ?_
  rw [Ideal.absNorm_eq_one_iff]
  exact v.isPrime.ne_top

private theorem sat_iff (hP : Hypotheses₂) {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Algebra ℚ K]
    (π : TR.CuspSub ℚ 2) (Q : CuspSub K 2) (hBC : IsBC π Q) (v : HeightOneSpectrum (𝓞 ℚ)) (w : HeightOneSpectrum (𝓞 K))
    (i : v.adicCompletion ℚ ≃+* w.adicCompletion K) (hi : IsCompl i) (B : Multiset ℂˣ) :
    π.HasSat v B ↔ (CG.mk Q).HasSat w B := by
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR hP ℚ 2 π v
  obtain ⟨⟨σ', hσ'⟩, hiso'⟩ := locCompC hP K 2 Q w
  have hc := hi.1
  obtain ⟨e, he⟩ := hBC.split v w i hi.1 hi.2 σ σ' hσ hσ'
  have c1 := (satLoc hP ℚ 2 v σ).2 _ π.finPart (hiso σ hσ) B
  have c2 := (satLoc hP K 2 w σ').2 _ Q.finPart (hiso' σ' hσ') B
  have hq : Formalism.UG.qV K w = Formalism.UG.qV ℚ v := by
    rw [qV_eq, qV_eq, GlobalTheory.LiftAbsPow.absNorm_eq i hc]
  refine ⟨fun hB => (CG.hasSat_mk _ _ _).2 (c2.2 (GlobalTheory.IsoPull.hasSatGL_of_ringEquiv i (GlobalTheory.LiftAbsPow.v_map_eq i hc) hq e
    (fun g x => (he g x).symm) (c1.1 hB))), fun hB => c1.2 ?_⟩
  refine GlobalTheory.IsoPull.hasSatGL_of_ringEquiv i.symm (fun y => ?_) hq.symm e.symm (fun g x => ?_) (c2.1 ((CG.hasSat_mk _ _ _).1 hB))
  · have := GlobalTheory.LiftAbsPow.v_map_eq i hc (i.symm y)
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  · apply e.injective
    rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]
    congr 2
    exact (Units.ext (Matrix.ext fun _ _ => (i.apply_symm_apply _)) :
      Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) = g)

end UpperTheory.V.Z.Kato.WeilSphericalRecords
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.DecConj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC
open scoped Pointwise

private theorem gap_pow {C : Type} [CommGroup C] (x : C) (a b : ℤ) (m : ℕ)
    (h : (x ^ a) ^ m = (x ^ b * x) ^ m) : x ^ ((m : ℤ) * (a - b - 1)) = 1 := by
  have h' : x ^ (a * m) = x ^ ((b + 1) * m) := by
    rw [zpow_mul, zpow_mul, zpow_add_one, zpow_natCast, zpow_natCast, h]
  have hc : (m : ℤ) * (a - b - 1) = a * m - (b + 1) * m := by ring
  rw [hc, zpow_sub, h', mul_inv_cancel]

private theorem exp_ne (e : ℕ) (he : 1 ≤ e) (m : ℕ) (hm : 1 ≤ m) (i j : Fin 2) :
    (m : ℤ) * ((![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i - (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) j - 1) ≠ 0 := by
  refine mul_ne_zero (by exact_mod_cast (by omega : m ≠ 0)) ?_
  fin_cases i <;> fin_cases j <;> simp <;> omega

private def decConj {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A B : ValuationSubring Ω) (γ : G F Ω) (h : γ • A = B) :
    ↥(Dec (F := F) B) →* ↥(Dec (F := F) A) where
  toFun u := ⟨γ⁻¹ * u * γ, by
    have hu := mem_Dec.1 u.2
    rw [mem_Dec, mul_smul, mul_smul, h, hu, ← h, inv_smul_smul]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.potOf :
    PotOf := by
  intro F Ω _ _ _ _ _ l _ e he r w A κ hl hA hE
  obtain ⟨⟨g, hg⟩, hI⟩ := hE
  have hvA : A.valuation (l : Ω) < 1 := by
    have h1 := (hA (l : 𝓞 F)).2 hl
    simpa using h1
  have hv : ∀ (t : Dec (F := F) A), (t : G F Ω) ∈ Ine A → ∀ i : Fin 2,
      κ i t = cycBar F Ω l ↑t ^ ((![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i) := by
    intro t ht i
    fin_cases i
    · exact (hI t ht).1
    · exact (hI t ht).2
  intro A' hA'
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hA hA'
  refine ⟨fun i => (κ i).comp (decConj A A' σ hσ), ?_, ?_⟩
  · refine ⟨g * r σ⁻¹, fun s => ?_⟩
    have hc : ((decConj A A' σ hσ s : Dec (F := F) A) : G F Ω) = σ⁻¹ * ↑s * σ := rfl
    have key : g * r σ⁻¹ * r ↑s * (g * r σ⁻¹)⁻¹ = g * r ↑(decConj A A' σ hσ s) * g⁻¹ := by
      rw [hc, map_mul, map_mul, map_inv]
      group
    rw [key]
    exact hg _
  · intro i j m hm heq
    obtain ⟨g0, hg0, hn⟩ := Ws.Pt.cycIne F Ω l A hvA _ (exp_ne e he m hm i j)
    have hA'σ : σ⁻¹ • A' = A := by rw [← hσ, inv_smul_smul]
    have hg1 : σ * g0 * σ⁻¹ ∈ Ine A' := by
      have h2 := (Two.ineConj F Ω σ⁻¹).1 A' g0 (by rw [hA'σ]; exact hg0)
      rwa [inv_inv] at h2
    have ht : decConj A A' σ hσ ⟨σ * g0 * σ⁻¹, Ine_le_Dec A' hg1⟩ = ⟨g0, Ine_le_Dec A hg0⟩ :=
      Subtype.ext (by
        show σ⁻¹ * (σ * g0 * σ⁻¹) * σ = g0
        group)
    have hcyc : cycBar F Ω l (σ * g0 * σ⁻¹) = cycBar F Ω l g0 := by
      rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]
    have h3 := DFunLike.congr_fun heq ⟨σ * g0 * σ⁻¹, Ine_le_Dec A' hg1⟩
    simp only [MonoidHom.pow_apply, MonoidHom.mul_apply, MonoidHom.comp_apply,
      Subgroup.coe_subtype] at h3
    rw [ht, hv _ hg0 i, hv _ hg0 j, hcyc] at h3
    exact hn (gap_pow (cycBar F Ω l g0) _ _ m h3)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.IrrOfTw
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC

namespace UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistWitness

private theorem irr_of_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (φ : Γ →* kˣ)
    (h : IsIrr (tw r φ)) : IsIrr r := by
  obtain ⟨hne, -, hmin⟩ := h
  refine ⟨hne, fun _ _ _ => Submodule.mem_top, fun U _ hU => hmin U le_top fun s v hv => ?_⟩
  have e : (tw r φ s : Matrix (Fin n) (Fin n) k).mulVec v =
      (φ s : k) • (r s : Matrix (Fin n) (Fin n) k).mulVec v := by
    rw [tw_val, Matrix.smul_mulVec]
  rw [e]
  exact U.smul_mem _ (hU s v hv)

private theorem comp_tw {Γ Δ k : Type} [Group Γ] [Group Δ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (φ : Γ →* kˣ)
    (f : Δ →* Γ) : (tw r φ).comp f = tw (r.comp f) (φ.comp f) := by
  refine MonoidHom.ext fun s => Units.ext ?_
  simp only [MonoidHom.comp_apply, tw_val]

private theorem open_ker {K Ω C : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω]
    [Algebra ℚ K] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω] [Group C] {M : ℕ} (hM : 1 ≤ M) {φ : G ℚ Ω →* C}
    (hφ : KillsMu M φ) :
    IsOpen ((φ.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)).ker : Set (G K Ω)) := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hM] using hζ
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := K) ζ).mem_nhds ?_) fun s hs => ?_)
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · simp only [Set.mem_iInter] at hs
    exact hφ _ fun ζ hζ => hs ζ hζ

end UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistWitness

end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.IsFrobOfRs
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC
open scoped Pointwise

section Res

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra ℚ K] [Algebra K Ω] [IsScalarTower ℚ K Ω]

private abbrev rs : G K Ω →* G ℚ Ω := AlgEquiv.restrictScalarsHom ℚ

private theorem rs_smul (s : G K Ω) (A : ValuationSubring Ω) : (rs s : G ℚ Ω) • A = s • A := by
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

private theorem rs_mem_Dec {s : G K Ω} {A : ValuationSubring Ω} :
    (rs s : G ℚ Ω) ∈ Dec (F := ℚ) A ↔ s ∈ Dec (F := K) A := by
  rw [mem_Dec, mem_Dec, rs_smul]

private theorem rs_mem_Ine {s : G K Ω} {A : ValuationSubring Ω} (hs : s ∈ Ine (F := K) A) :
    (rs s : G ℚ Ω) ∈ Ine (F := ℚ) A :=
  ⟨rs_mem_Dec.2 hs.1, hs.2⟩

private theorem isFrob_of_rs {s : G K Ω} {A : ValuationSubring Ω} {q : ℕ} (hs : IsFrob A q (rs s : G ℚ Ω)) :
    IsFrob A q s :=
  ⟨rs_mem_Dec.1 hs.1, hs.2⟩

private theorem exists_rs (σ : G ℚ Ω) (h : ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω x) :
    ∃ s : G K Ω, rs s = σ :=
  ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) h, AlgEquiv.ext fun _ => rfl⟩

private theorem cycBar_rs (l : ℕ) [Fact l.Prime] (s : G K Ω) : cycBar ℚ Ω l (rs s) = cycBar K Ω l s := by
  have h : MulSemiringAction.toRingAut (G ℚ Ω) Ω (rs s) = MulSemiringAction.toRingAut (G K Ω) Ω s :=
    RingEquiv.ext fun _ => rfl
  simp only [cycBar, cycZ, MonoidHom.comp_apply, h]

private def resDec (A : ValuationSubring Ω) : ↥(Dec (F := K) A) →* ↥(Dec (F := ℚ) A) :=
  (rs.comp (Dec (F := K) A).subtype).codRestrict (Dec (F := ℚ) A) fun s => rs_mem_Dec.2 s.2

private theorem exact_res {l : ℕ} [Fact l.Prime] {e : ℕ} {V : G ℚ Ω →* GL (Fin 2) (Qbar l)}
    {A : ValuationSubring Ω} {κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ} (h : Exact e V A κ) :
    Exact e (V.comp (rs : G K Ω →* G ℚ Ω)) A fun i => (κ i).comp (resDec A) := by
  obtain ⟨⟨g, hg⟩, hI⟩ := h
  refine ⟨⟨g, fun s => hg (resDec A s)⟩, fun s hs => ?_⟩
  have h2 := hI (resDec A s) (rs_mem_Ine hs)
  have h3 : cycBar ℚ Ω l ((resDec A s : ↥(Dec (F := ℚ) A)) : G ℚ Ω) = cycBar K Ω l s := cycBar_rs l (s : G K Ω)
  rw [h3] at h2
  exact h2

private theorem frobIn_res {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {e q : ℕ} {A : ValuationSubring Ω}
    {κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ} {B : Multiset ℂˣ}
    (hfix : ∀ g ∈ Dec (F := ℚ) A, ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x)
    (h : FrobIn ι e q A (fun i => (κ i).comp (resDec (K := K) A)) B) : FrobIn ι e q A κ B := by
  intro σ hσ
  obtain ⟨s, hs⟩ := exists_rs (K := K) (σ : G ℚ Ω) (hfix _ σ.2)
  have hd : s ∈ Dec (F := K) A := rs_mem_Dec.1 (hs ▸ σ.2)
  have hr : resDec A (⟨s, hd⟩ : ↥(Dec (F := K) A)) = σ := Subtype.ext hs
  obtain ⟨b, hb, he⟩ := h ⟨s, hd⟩ (isFrob_of_rs (by rw [hs]; exact hσ))
  refine ⟨b, hb, ?_⟩
  have h3 : cycBar ℚ Ω l (σ : G ℚ Ω) = cycBar K Ω l s := by rw [← hs]; exact cycBar_rs l s
  rw [h3]
  have h4 : ((κ 0).comp (resDec (K := K) A)) ⟨s, hd⟩ = κ 0 σ := by
    rw [MonoidHom.comp_apply, hr]
  rw [← h4]
  exact he

end Res

theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.locQ :
    PlainRec → PlainOf → RecTExists → BcSplit → PotOf → LocK → LocQ := by
  intro hPR hPO hRT hBC hPot hLK l _ hl2 Ω _ _ _ ι e he V π hc hirr hM hreg hatt v A κ hlv hA hE hor
  obtain ⟨K, _, _, _, _, _, _, P, w, hfr, hirrK, hregP, hpol, hattP, hAw, hlw, hnorm, hfix, hsat⟩ :=
    hBC l hl2 Ω ι V π hc hirr hM hreg hatt v A hlv hA
  have hEx := exact_res (K := K) hE
  have hcK : Continuous (V.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) :=
    hc.comp (UpperTheory.V.Af.continuous_restrictScalarsHom _ _ _)
  have hWP : PlainAt P w := by
    rcases hor with hW | ⟨B, hB⟩
    · have hWA := hW K hfr hirrK
      obtain ⟨rc, hrc⟩ := hRT K Ω A w hAw
      have hpu := hPot K Ω l e he _ w A _ hlw hAw hEx
      intro σ hσ
      exact (guard_of hPR hregP hattP hWA (Or.inr (Or.inr hpu)) hrc hσ).1
    · exact (hPO K 2 (by norm_num) P w).2 ⟨B, (hsat B).1 hB⟩
  obtain ⟨⟨B₀, hB₀⟩, hF⟩ := hLK K Ω l hl2 ι e he _ P hcK hregP hpol hattP w A _ hlw hAw hEx hWP
  refine ⟨⟨B₀, (hsat B₀).2 hB₀⟩, fun B hB => ?_⟩
  have h := hF B ((hsat B).1 hB)
  rw [hnorm] at h
  exact frobIn_res hfix h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.KatoTwoW
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Z.Win

namespace UpperTheory.V.Z.Kato.WeilSphericalRecords

def KatoTwoW : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    (e N : ℕ) (θ ψ : G ℚ Ω →* (Qbar l)ˣ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)), Used l Ω K e N θ ψ W →
    ∀ (ι : Qbar l ≃+* ℂ) (f : Af.Newform (2 * e + 1)), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ)))) → WitAQ ι W →
      Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W 1)) ∧ Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W θ))

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}

theorem kUse (hK : KatoTwo) (D : Dat Ω K c e ψ) {θ ψ' : G ℚ Ω →* (Qbar l)ˣ} {W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)}
    (u : Used l Ω K e N θ ψ' W) (ι : Qbar l ≃+* ℂ) (h : D.IsModular ι W) :
    Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W 1)) ∧ Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W θ)) :=
  h.elim fun f hf => hK l Ω K e N θ ψ' W u ι f hf

theorem kUse' (hK : KatoTwoW) (_ : Dat Ω K c e ψ) {θ ψ' : G ℚ Ω →* (Qbar l)ˣ} {W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)}
    (u : Used l Ω K e N θ ψ' W) (ι : Qbar l ≃+* ℂ)
    (h : (∃ f : Af.Newform (2 * e + 1), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ WitAQ ι W) :
    Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W 1)) ∧ Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W θ)) :=
  h.1.elim fun f hf => hK l Ω K e N θ ψ' W u ι f hf h.2

end UpperTheory.V.Z.Kato.WeilSphericalRecords
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.RecFrob
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.CuspRep Polynomial
open UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Kato.WeilSphericalRecords

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem root_diag {n : ℕ} (α : Fin n → ℂˣ) (y : WD h)
    (e : y = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w ((1 - (n : ℝ)) / 2))) (φ : ↥(Weil h)) (hd : deg φ = 1) (z : ℂ)
    (hz : (WD.charPol y φ).IsRoot z) : ∃ b ∈ algSat n (normV w) (Finset.univ.val.map α), z * b = 1 := by
  subst e
  rw [WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, hd] at hz
  rw [Polynomial.IsRoot, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hz
  obtain ⟨i, -, hi⟩ := hz
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero, zpow_one] at hi
  have hq : (((normV w : ℕ) : ℂ) ^ ((((1 : ℝ) - n) / 2 : ℝ) : ℂ)) * ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = 1 := by
    have h0 : ((normV w : ℕ) : ℂ) ≠ 0 := by
      have := GlobalTheory.WeilDeligne.one_lt_normV w
      exact_mod_cast (by omega : (normV w : ℕ) ≠ 0)
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, ← Complex.cpow_add _ _ h0]
    have : ((((1 : ℝ) - n) / 2 : ℝ) : ℂ) + ((((n : ℝ) - 1) / 2 : ℝ) : ℂ) = 0 := by
      push_cast
      ring
    rw [this, Complex.cpow_zero]
  refine ⟨((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α i : ℂ), ?_, ?_⟩
  · rw [algSat, Multiset.mem_map]
    refine ⟨(α i : ℂ), ?_, rfl⟩
    simp only [Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton, Multiset.map_map]
    exact Multiset.mem_map_of_mem (fun j => ((α j : ℂˣ) : ℂ)) (Finset.mem_univ i)
  · rw [hi]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, coe_qPow]
    have ha : (α i : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
    exact hq

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.CuspRep.ParLaws in
private theorem algNorm_diag {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (L : LawsT a ha rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧
      rc (algNorm σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w ((1 - (n : ℝ)) / 2)) := by
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.main GlobalTheory.bernsteinZelevinskyFiniteness_holds (w.adicCompletion E) n
    ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩ (GlobalTheory.TempSatUnr.isSpherical_of_hasSatGL hB)
  refine ⟨α, hB.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα), ?_⟩
  have hx : GlobalTheory.SmGL.HasSatake (IrrGL.of σ.ρ σ.smooth σ.irred).rep α :=
    ⟨(IrrGL.of σ.ρ σ.smooth σ.irred).2.rep.irr, fixed_ne_bot_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred) hα.2.1,
      (IsSubquotient.of_surjective (IrrGL.equivOf σ.ρ σ.smooth σ.irred).toIntertwiningMap (IrrGL.equivOf σ.ρ σ.smooth σ.irred).toLinearEquiv.surjective).trans hα.2.2⟩
  have e := GlobalTheory.RecT.SphLaw.sat ((GlobalTheory.RecT.lawsT_iff a ha rc).2 L) (IrrGL.of σ.ρ σ.smooth σ.irred) α hx
  rw [algNorm, L.nu, e, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
  simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]
  change (_ : ℂ) * ((_ : ℂ) * v i) = _ * (_ * v i)
  ring

end UpperTheory.V.Z.Kato.WeilSphericalRecords
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWitAlt
section
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC

theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.sphOfWit :
    TwWit → LocQ → SphOfWit := by
  intro hT hL l _ hl2 Ω _ _ _ ι e he W hWc hWi hWd hwit M φ hM hφ A w κ hA hlw hfl hk π hreg hatt
  obtain ⟨N, hN, hWk⟩ := hWd
  have hMN : 0 < N * M := Nat.mul_pos hN hM
  have hVc : Continuous (tw W φ) := GlobalTheory.Ord2.TwDet.tw_cont hWc (GlobalTheory.Ord2.SrcForm.cont_of_kills hM hφ)
  have hVi : IsIrr (tw W φ) :=
    ⟨hWi.1, fun _ _ _ => trivial, fun U hU hi =>
      hWi.2.2 U hU fun g v hv => (GlobalTheory.Ord2.SrcForm.isInv_tw W φ U).1 hi g v hv⟩
  have hVd : ∃ K : ℕ, 1 ≤ K ∧ KillsMu K (GlobalTheory.Ord2.dt (tw W φ)) := by
    refine ⟨N * M, hMN, ?_⟩
    rw [GlobalTheory.Ord2.TwDet.dt_tw, pow_two]
    exact GlobalTheory.Ord2.TwDet.killsMu_mul
      (GlobalTheory.Ord2.TwDet.killsMu_mul (GlobalTheory.Ord2.TwDet.killsMu_dvd hφ (dvd_mul_left M N)) (GlobalTheory.Ord2.TwDet.killsMu_dvd hφ (dvd_mul_left M N)))
      (GlobalTheory.Ord2.TwDet.killsMu_dvd hWk (dvd_mul_right N M))
  exact (hL l hl2 Ω ι e he (tw W φ) π hVc hVi hVd hreg hatt w A κ hlw hA ⟨hfl, hk⟩
    (Or.inl (hT l Ω ι 2 W M φ hM hφ hwit))).1
end

