module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0761
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.IntCrit
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0212

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Slopes
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

private theorem norm_normV {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (l : ℕ) [Fact l.Prime]
    (hw : (l : 𝓞 F) ∉ w.asIdeal) : ‖((normV w : ℕ) : Qbar l)‖ = 1 := by
  classical
  have hl : l.Prime := Fact.out
  have hN : ¬ l ∣ normV w := by
    intro hdvd
    letI := Ideal.Quotient.field w.asIdeal
    haveI : Finite (𝓞 F ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
    letI := Fintype.ofFinite (𝓞 F ⧸ w.asIdeal)
    obtain ⟨p, hchar⟩ := CharP.exists (𝓞 F ⧸ w.asIdeal)
    have hp : p.Prime := CharP.char_is_prime (𝓞 F ⧸ w.asIdeal) p
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 F ⧸ w.asIdeal) p
    have hcard : normV w = p ^ (n : ℕ) := by rw [normV, Nat.card_eq_fintype_card, hn]
    rw [hcard] at hdvd
    have hlp : l = p := (Nat.prime_dvd_prime_iff_eq hl hp).1 (hl.dvd_of_dvd_pow hdvd)
    apply hw
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, hlp]
    exact CharP.cast_eq_zero _ p
  have h1 : ‖((normV w : ℕ) : ℚ_[l])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl).2 hN
  rw [← h1, ← map_natCast (algebraMap ℚ_[l] (Qbar l))]
  exact norm_algebraMap' _ _

private theorem frob_unit {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) (hr : Continuous r) (w : HeightOneSpectrum (𝓞 F))
    (B : Multiset ℂ) (h : FrobEig ι r w B) : ∀ b ∈ B, ‖ι.symm b‖ = 1 := by
  intro b hb
  have hA := isPlaceOver_placeOf Ω w
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  have e := (h _ hA).2 σ hσ
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  refine Lib.norm_root_eq_one r hr σ⁻¹ _ ?_
  apply ι.injective
  have h2 : ((r σ⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom).eval b = 0 := by
    rw [e, Polynomial.eval_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.map_map]
    exact Multiset.mem_map.2 ⟨b, hb, by simp⟩
  have h3 := Polynomial.eval₂_at_apply (p := (r σ⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly) ι.toRingHom (ι.symm b)
  rw [map_zero]
  rw [Polynomial.eval_map] at h2
  refine h3.symm.trans ?_
  rwa [show ι.toRingHom (ι.symm b) = b from ι.apply_symm_apply b]

theorem slopesOf (hP : Hypotheses₂) {F : Type} [Field F] [NumberField F] {n : ℕ} (m : Fin n → ℤ) {p : ℕ} (hp : p.Prime)
    (w : HeightOneSpectrum (𝓞 F)) (hw : (p : 𝓞 F) ∈ w.asIdeal) (hd : ¬ (p : ℤ) ∣ discr F)
    (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B)
    (H : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), ∃ r : G F (AlgebraicClosure F) →* GL (Fin n) (Qbar l), Continuous r ∧
      ((l : 𝓞 F) ∉ w.asIdeal → ∀ (A : ValuationSubring (AlgebraicClosure F)) (h : IsPlaceOver A w)
        (rc : IrrGL (k := w.adicCompletion F) → WD h), IsRec h rc → IsWDOf ι r (rc (algNorm σ))) ∧
      ∀ (A : ValuationSubring (AlgebraicClosure F)) (h : IsPlaceOver A w)
        (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
        (Bw : LocBridge l F (AlgebraicClosure F) (Dec (F := F) A) O) (hj : Induces Bw),
        (GlobalTheory.SmGL.IsSpherical σ.ρ → IsCrysAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype)) ∧
        (∀ (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) τ (Finset.univ.val.map fun i => -m i)) ∧
        (GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion F) (Fin n)) ≠ ⊥ → ∀ rc, IsRec h rc →
          wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype) = rc (algNorm σ))) :
    SlopesIn (normV w) m (algSat n (normV w) B) := by
  have hK := GlobalTheory.SmGL.SphCompletion.KO_completion w n
  obtain ⟨x, hx0, hx, -⟩ := hB.exists_vec
  have hfix : ∀ U, U ≤ GlobalTheory.LFun.KGL w (n := n) → GlobalTheory.PRep.fixed σ.ρ U ≠ ⊥ := fun U hU =>
    (Submodule.ne_bot_iff _).2 ⟨x, GlobalTheory.LGrp.mem_fixed.2 fun k hk => GlobalTheory.LGrp.mem_fixed.1 hx k (hU hk), hx0⟩
  have hsph : GlobalTheory.SmGL.IsSpherical σ.ρ := hfix _ hK.le
  have hiw := hfix _ ((GlobalTheory.SmGL.iwahori_le_KO _ _).trans hK.le)
  have key : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), ∀ b ∈ algSat n (normV w) B,
      (∀ a : ℤ, (∀ i, -a ≤ m i) → ‖ι.symm ((normV w : ℂ) ^ a * b⁻¹)‖ ≤ 1) ∧
        ∀ a : ℤ, (∀ i, m i ≤ a) → ‖ι.symm ((normV w : ℂ) ^ a * b)‖ ≤ 1 := by
    intro l _ ι
    obtain ⟨r, hr, h1, h2⟩ := H l ι
    by_cases hl : (l : 𝓞 F) ∈ w.asIdeal
    · obtain rfl : l = p := by
        by_contra hne
        have hc : IsCoprime (l : 𝓞 F) (p : 𝓞 F) :=
          Nat.Coprime.cast ((Nat.coprime_primes Fact.out hp).2 hne)
        obtain ⟨a, b, e⟩ := hc
        exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
          (e ▸ add_mem (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hw)))
      have hA := isPlaceOver_placeOf (AlgebraicClosure F) w
      obtain ⟨j, L0, hj, hLL⟩ := GlobalTheory.PlaceBridge.exists_locBridge l F (AlgebraicClosure F) w _ hl hA
      obtain ⟨Bw, hBj, -⟩ := hLL L0 le_rfl
      have hI : Induces Bw := fun x => by rw [hBj]; exact hj x
      obtain ⟨c1, c2, c3⟩ := h2 _ hA _ Bw hI
      have L := hP.litN.loc
      obtain ⟨rc, hrc⟩ := L.llc F _ _ w hA
      have hrc' := GlobalTheory.LocLanglands.isRec_of_isRecLit L.dzc L.dzi L.exh L.multi L.cos L.zel L.geo L.bz F _ _ w hA rc hrc
      exact crysSlopes hP F _ l hd ι n m r hr w _ hA _ Bw hI (c1 hsph) c2 σ B hB rc hrc' (c3 hiw rc hrc')
    · intro b hb
      have hu := frob_unit ι r hr w _ (satFrob hP F _ l ι n r hr w hl σ B hB (h1 hl)) b hb
      have hq := norm_normV w l hl
      constructor <;> intro a _ <;> simp [hu, hq]
  intro b hb
  exact ⟨fun a ha => Lib.isIntegral_of_norm_le _ fun l _ ι => (key l ι b hb).1 a ha, fun a ha => Lib.isIntegral_of_norm_le _ fun l _ ι => (key l ι b hb).2 a ha⟩

end UpperTheory.V.Af
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SstConj
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.CoeffExt TensorProduct Module

namespace UpperTheory.V.Af

theorem isSst_of_coord {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
    {LL LL' : Type} [Field LL] [Field LL'] [Algebra ℚ_[l] LL] [Algebra ℚ_[l] LL'] [Algebra LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    [Module LL' V'] [IsScalarTower ℚ_[l] LL' V'] [IsScalarTower LL LL' V']
    {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL' ↥(GK K) V'}
    {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[LL] (ι → V)} (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i))
    (hι : finrank LL LL' = Fintype.card ι) [Nonempty ι] (h : IsSst P ρ) : IsSst P ρ' := by
  unfold IsSst at h ⊢
  have e : ↥(Dst P ρ') ≃ₗ[LL] (ι → ↥(Dst P ρ)) :=
    subEquiv (tensCoord E (Bst P)) ((Dst P ρ').restrictScalars LL) _ fun x => by
      simp only [Submodule.restrictScalars_mem, mem_Dst]
      rw [forall_comm]
      refine forall_congr' fun g => ?_
      rw [← (tensCoord E (Bst P)).injective.eq_iff, funext_iff]
      simp only [GlobalTheory.PstExt.tensCoord_stRep P hE]
  have h1 := e.finrank_eq
  have h2 := E.finrank_eq
  rw [finrank_fun', ← Module.finrank_mul_finrank LL LL', hι] at h1 h2
  have hp : 0 < Fintype.card ι := Fintype.card_pos
  rw [Nat.eq_of_mul_eq_mul_left hp h1, Nat.eq_of_mul_eq_mul_left hp h2, h]

theorem isSstAt_conj {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O)
    {a : ℕ} {r r' : ↥Gw →* GL (Fin a) (Om l)} (A : GL (Fin a) (Om l)) (hc : ∀ g, r' g = A * r g * A⁻¹)
    (h : IsSstAt P Bw r) : IsSstAt P Bw r' := by
  obtain ⟨L₁, r₁, h₁, hs⟩ := h
  obtain ⟨L₂, hL, r₂, hm, e, he⟩ := GlobalTheory.ConjLocal.exists_conj_model A hc h₁
  refine ⟨L₂, r₂, hm, ?_⟩
  let _ : Algebra ↥L₁.1 ↥L₂.1 := (IntermediateField.inclusion hL).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] ↥L₁.1 ↥L₂.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := L₂.2
  have : FiniteDimensional ↥L₁.1 ↥L₂.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  have hρ : ∀ g, ∃ M : Matrix (Fin a) (Fin a) ↥L₁.1, (∀ x, Bw.repE L₁ r₁ g x = M.mulVec x) ∧
      ∀ x, Bw.repE L₂ (Formalism.MainNotions.N.mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x =
        (M.map (algebraMap ↥L₁.1 ↥L₂.1)).mulVec x :=
    fun g => ⟨r₁ (Bw.e.symm g), fun _ => rfl, fun _ => rfl⟩
  have : Nonempty (Fin (finrank ↥L₁.1 ↥L₂.1)) := ⟨⟨0, finrank_pos⟩⟩
  refine isSst_of_coord P (E := (e.symm.restrictScalars ↥L₁.1).trans (vecCoord ↥L₁.1 ↥L₂.1 a)) (fun g x i => ?_)
    (Fintype.card_fin _).symm hs
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [← he]
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, LinearEquiv.symm_apply_apply]
  exact vecCoord_rep hρ g y i

theorem sat_ae_of_smooth (hS : SatLoc) {F : Type} [Field F] [NumberField F] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    [Nontrivial V] (ρ : Representation ℂ (GL (Fin n) (Af F)) V) (hρ : GlobalTheory.PRep.IsSmooth ρ)
    (hi : ∀ w, ∃ σ, LocIsotypic ρ w σ) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, GlobalTheory.LFun.HasSatGL w (ρ.comp (locGL F n w)) B := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨S, hS'⟩ := GlobalFixedVectors.exists_KAway_subset (M := 1) ((hρ v).mem_nhds (by simp))
  filter_upwards [S.finite_toSet.eventually_cofinite_notMem] with w hw
  obtain ⟨σ, hσ⟩ := hi w
  obtain ⟨h1, h2⟩ := hS F n w σ
  have hK : IsCompact (GlobalTheory.LFun.KGL w (n := n) : Set (GL (Fin n) (w.adicCompletion F))) :=
    GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F w)
  obtain ⟨B, hB⟩ := h1 (hasFixed_of_sum σ.ρ σ.smooth (ρ.comp (locGL F n w)) _ hK hσ.2
    ⟨v, hv, fun u hu => hS' (GlobalFixedVectors.mem_KAway.2 ⟨locGL_mem_KLev n w
      (by rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top) hu,
      fun x hx => pLoc_locGL_of_ne (fun e : x = w => hw (e ▸ hx)) u⟩)⟩)
  exact ⟨B, (h2 _ _ hσ B).2 hB⟩

end UpperTheory.V.Af

end
end

