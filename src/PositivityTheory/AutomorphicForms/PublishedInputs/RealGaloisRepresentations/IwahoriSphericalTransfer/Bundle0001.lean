module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0139
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.AttachedRepConjugateInvariant
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GaloisLiftFixedPoints

open scoped Pointwise

section

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

theorem exists_of_fixed (y : Ω) (hy : ∀ s : Formalism.ConjugateSelfDual.G K Ω, s y = y) : ∃ x : K, algebraMap K Ω x = y :=
  IntermediateField.mem_bot.1 ((InfiniteGalois.mem_bot_iff_fixed y).2 hy)

end

section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

noncomputable def liftEquiv (φ : Ω ≃+* Ω) (h1 : ∀ x : K, ∃ y : K, algebraMap K Ω y = φ (algebraMap K Ω x))
    (h2 : ∀ x : K, ∃ y : K, algebraMap K Ω y = φ.symm (algebraMap K Ω x)) : K ≃+* K where
  toFun x := (h1 x).choose
  invFun x := (h2 x).choose
  left_inv x := (algebraMap K Ω).injective (by
    rw [(h2 _).choose_spec, (h1 x).choose_spec, φ.symm_apply_apply])
  right_inv x := (algebraMap K Ω).injective (by
    rw [(h1 _).choose_spec, (h2 x).choose_spec, φ.apply_symm_apply])
  map_mul' x y := (algebraMap K Ω).injective (by
    rw [(h1 _).choose_spec, map_mul, map_mul, map_mul, (h1 x).choose_spec, (h1 y).choose_spec])
  map_add' x y := (algebraMap K Ω).injective (by
    rw [(h1 _).choose_spec, map_add (f := _), map_add (f := _), map_add (f := _), (h1 x).choose_spec, (h1 y).choose_spec])

theorem liftEquiv_spec (φ : Ω ≃+* Ω) (h1 : ∀ x : K, ∃ y : K, algebraMap K Ω y = φ (algebraMap K Ω x))
    (h2 : ∀ x : K, ∃ y : K, algebraMap K Ω y = φ.symm (algebraMap K Ω x)) (x : K) :
    algebraMap K Ω (liftEquiv φ h1 h2 x) = φ (algebraMap K Ω x) :=
  (h1 x).choose_spec

end

end GlobalTheory.GaloisLiftFixedPoints

open scoped Pointwise
open GlobalTheory.GaloisLiftFixedPoints in
theorem _root_.GlobalTheory.T.attached_rep_conjugate_invariant : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (r : G K Ω →* GL (Fin a) (Qbar l)) (g : G F Ω) (c : G K Ω →* G K Ω), (∀ s, res F Ω K (c s) = g * res F Ω K s * g⁻¹) → Function.Surjective c → AttRes π ι K r → AttRes π ι K (r.comp c) := by
  intro F Ω _ _ _ _ _ _ K _ _ _ _ _ _ l _ ι a π r g c hc hsurj hr
  have ginv : ∀ z : Ω, g⁻¹ (g z) = z := fun z => by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have gg : ∀ z : Ω, g (g⁻¹ z) = z := fun z => by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have hcx : ∀ (s : G K Ω) (x : Ω), c s x = g (s (g⁻¹ x)) := fun s x => by
    have := congrArg (fun φ : G F Ω => φ x) (hc s)
    exact this
  set σ' : Ω ≃+* Ω := (g⁻¹ : G F Ω).toRingEquiv with hσ'
  have hsymm : ∀ z : Ω, σ'.symm z = g z := fun z => by
    rw [RingEquiv.symm_apply_eq]
    exact (ginv z).symm
  have h1 : ∀ x : K, ∃ y : K, algebraMap K Ω y = σ' (algebraMap K Ω x) := fun x => by
    refine exists_of_fixed _ fun s => ?_
    have e := hcx s (algebraMap K Ω x)
    rw [AlgEquiv.commutes] at e
    show s (g⁻¹ (algebraMap K Ω x)) = g⁻¹ (algebraMap K Ω x)
    have e2 := congrArg (fun z => g⁻¹ z) e
    simp only [ginv] at e2
    exact e2.symm
  have h2 : ∀ x : K, ∃ y : K, algebraMap K Ω y = σ'.symm (algebraMap K Ω x) := fun x => by
    rw [hsymm]
    refine exists_of_fixed _ fun s => ?_
    obtain ⟨t, rfl⟩ := hsurj s
    rw [hcx, ginv, AlgEquiv.commutes]
  set τ : K ≃+* K := liftEquiv σ' h1 h2 with hτ
  have hL : IsLift τ σ' := fun x => (liftEquiv_spec σ' h1 h2 x).symm
  have hτF : ∀ y : F, τ (algebraMap F K y) = algebraMap F K y := fun y => (algebraMap K Ω).injective (by
    rw [← hL, ← IsScalarTower.algebraMap_apply]
    exact AlgEquiv.commutes _ _)
  have hconj : ∀ s : G K Ω, c s = conjGal hL s := fun s => AlgEquiv.ext fun x => by
    rw [conjGal_apply, hsymm, hcx]
    rfl
  have hσA : ∀ A : ValuationSubring Ω, ∀ x, σ' x ∈ A ↔ x ∈ g • A := fun A x => by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    rfl
  have hfrob : ∀ (A : ValuationSubring Ω) (q : ℕ) (s : G K Ω), IsFrob A q s → IsFrob (g • A) q (c s) :=
    fun A q s hs => by
      rw [hconj]
      refine ⟨conjGal_mem_Dec hL (hσA A) hs.1, fun x hx => ?_⟩
      rw [← val_lt_one (hσA A), map_sub, map_pow, apply_conjGal]
      exact hs.2 _ ((A.valuation_le_one_iff _).2 ((hσA A x).2 (((g • A).valuation_le_one_iff _).1 hx)))
  have hine : ∀ (A : ValuationSubring Ω) (s : G K Ω), s ∈ Ine (F := K) A → c s ∈ Ine (F := K) (g • A) :=
    fun A s hs => by
      rw [hconj]
      exact conjGal_mem_Ine hL (hσA A) hs
  set e : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv τ with he
  have hunder : ∀ w : HeightOneSpectrum (𝓞 K), (preplace τ w).under (𝓞 F) = w.under (𝓞 F) := fun w => by
    apply HeightOneSpectrum.ext
    ext x
    have hx : e (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 K) x := RingOfIntegers.ext (hτF (x : F))
    show algebraMap (𝓞 F) (𝓞 K) x ∈ (preplace τ w).asIdeal ↔ algebraMap (𝓞 F) (𝓞 K) x ∈ w.asIdeal
    rw [mem_preplace, ← he, hx]
  have hnorm : ∀ w : HeightOneSpectrum (𝓞 K), normV (preplace τ w) = normV w := fun w => by
    show Nat.card (𝓞 K ⧸ (w.asIdeal.comap (e : 𝓞 K →+* 𝓞 K))) = Nat.card (𝓞 K ⧸ w.asIdeal)
    exact Nat.card_congr (Ideal.quotientEquiv _ _ e
      (Ideal.map_comap_of_surjective (e : 𝓞 K →+* 𝓞 K) e.surjective _).symm).toEquiv
  have hinj : Function.Injective (preplace τ) := fun u v huv =>
    (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv τ)).symm.injective huv
  unfold AttRes at hr ⊢
  filter_upwards [hinj.tendsto_cofinite.eventually hr] with w hw f hf
  have hf' : normV (preplace τ w) = normV ((preplace τ w).under (𝓞 F)) ^ f := by
    rw [hnorm, hunder]
    exact hf
  obtain ⟨B, hB, hE⟩ := hw f hf'
  rw [hunder] at hB hE
  refine ⟨B, hB, fun A hA => ?_⟩
  obtain ⟨k1, k2⟩ := hE (g • A) (isPlaceOver_preplace hL (hσA A) hA)
  refine ⟨fun s hs => k1 _ (hine A s hs), fun s hs => ?_⟩
  have := k2 (c s) (by rw [hnorm]; exact hfrob A _ s hs)
  rw [MonoidHom.comp_apply, map_inv]
  exact this
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.BridgeJMemKwOfDecLe
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RealGal

theorem bridge_j_mem_Kw_of_dec_le : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), Dec (F := F) A ≤ (res F Ω K).range → ∀ x : K, Bw.j (algebraMap K Ω x) ∈ Bw.Kw.1 := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ A O _ _ _ Bw hD x
  have hfix : ∀ σ ∈ (Bw.Kw.1).fixingSubgroup, σ (Bw.j (algebraMap K Ω x)) = Bw.j (algebraMap K Ω x) := by
    intro σ hσ
    obtain ⟨g, hg⟩ := Bw.e.surjective ⟨σ, hσ⟩
    have h1 := Bw.e_comm g (algebraMap K Ω x)
    rw [hg] at h1
    obtain ⟨h, hh⟩ := hD g.2
    have h2 : (g : Ω ≃ₐ[F] Ω) (algebraMap K Ω x) = algebraMap K Ω x := by
      rw [← hh]
      exact h.commutes x
    simpa [h2] using h1
  haveI : IsGalois ℚ_[l] (Om l) := inferInstance
  rw [← InfiniteGalois.fixedField_fixingSubgroup Bw.Kw.1]
  exact fun σ => hfix σ.1 σ.2

end GlobalTheory.RealGal
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ComplexConjAlgebraMap
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RealGal

theorem exists_hodgeTate {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ} (π : TR.CuspSub F a)
    (hπ : π.IsRegAlg) (v : InfinitePlace F) :
    ∃ H : Multiset ℤ, ∃ m, π.HasInfChar v m ∧
      H.map (fun n : ℤ => (n : ℂ)) = m.map fun z => ((a : ℂ) - 1) / 2 - z := by
  obtain ⟨m, hm, -, hz⟩ := hπ v
  refine ⟨m.attach.map fun z => -(hz z.1 z.2).choose, m, hm, ?_⟩
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.attach_map_val m, Multiset.map_map]
  refine Multiset.map_congr rfl fun z _ => ?_
  have h := (hz z.1 z.2).choose_spec
  simp only [Function.comp_apply, Int.cast_neg]
  linear_combination h

theorem complexConj_algebraMap {F K : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K]
    [IsCMField K] [Algebra F K] (x : F) :
    IsCMField.complexConj K (algebraMap F K x) = algebraMap F K x := by
  rw [IsCMField.complexConj_eq_self_iff, mem_maximalRealSubfield_iff]
  intro φ
  have h := ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_mk_iff.mp
    (IsTotallyReal.isReal (InfinitePlace.mk (φ.comp (algebraMap F K)))))
  rw [RCLike.star_def, ← ComplexEmbedding.conjugate_coe_eq]
  exact RingHom.congr_fun h x

end GlobalTheory.RealGal

end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.DRSstCrysPstJumpsDescend
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.RealGal.dRSstCrysPstJumps_descend : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (P : LocPrime l) (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O), Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → Bw'.LL = Bw.LL → ∀ (a : ℕ) (r : G F Ω →* GL (Fin a) (Qbar l)), (IsdRAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) → IsdRAt P Bw (r.comp (Dec (F := F) A).subtype)) ∧ (IsSstAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) → IsSstAt P Bw (r.comp (Dec (F := F) A).subtype)) ∧ (IsCrysAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) → IsCrysAt P Bw (r.comp (Dec (F := F) A).subtype)) ∧ (IsPstAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) → IsPstAt P Bw (r.comp (Dec (F := F) A).subtype)) ∧ ∀ (τ : K →+* Qbar l) (J : Multiset ℤ), IsJumpsAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) τ J → IsJumpsAt P Bw (r.comp (Dec (F := F) A).subtype) (τ.comp (algebraMap F K)) J := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ P A O _ _ _ Bw Bw' hK hj hL a r
  obtain ⟨Kw', j', jE', jd', e', ec', esc', ecomm', LL0', hs', eO', h1', h2', h3'⟩ := Bw'
  dsimp only at hK hj hL
  subst hK hj hL
  set Bw' : LocBridge l K Ω (Dec (F := K) A) O :=
    ⟨Bw.Kw, Bw.j, jE', jd', e', ec', esc', ecomm', Bw.LL, hs', eO', h1', h2', h3'⟩ with hBw'
  have key : ∀ (LL' : FinExt l) (r'' : ↥(Dec (F := K) A) →* GL (Fin a) ↥LL'.1),
      IsModel Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) LL' r'' →
      IsModel Bw (r.comp (Dec (F := F) A).subtype) LL' (r''.comp (Bw.e.trans e'.symm).toMonoidHom) ∧
      Bw.repE LL' (r''.comp (Bw.e.trans e'.symm).toMonoidHom) = Bw'.repE LL' r'' := by
    intro LL' r'' ⟨hle, hmap⟩
    refine ⟨⟨hle, ?_⟩, ?_⟩
    · refine MonoidHom.ext fun g => ?_
      have h1 := DFunLike.congr_fun hmap (e'.symm (Bw.e g))
      have h2 : AlgEquiv.restrictScalarsHom F ((e'.symm (Bw.e g) : ↥(Dec (F := K) A)) : Ω ≃ₐ[K] Ω) =
          ((g : ↥(Dec (F := F) A)) : Ω ≃ₐ[F] Ω) := by
        refine AlgEquiv.ext fun x => Bw.j.injective ?_
        change Bw.j (((e'.symm (Bw.e g) : ↥(Dec (F := K) A)) : Ω ≃ₐ[K] Ω) x) = _
        rw [← ecomm', MulEquiv.apply_symm_apply, Bw.e_comm]
      exact h1.trans (congrArg r h2)
    · refine MonoidHom.ext fun g => ?_
      simp only [LocBridge.repE, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨LL', r'', hm, hd⟩
    obtain ⟨hm2, he⟩ := key LL' r'' hm
    refine ⟨LL', _, hm2, ?_⟩
    unfold LocBridge.IsdRE at hd ⊢
    rw [he]; exact hd
  · rintro ⟨LL', r'', hm, hd⟩
    obtain ⟨hm2, he⟩ := key LL' r'' hm
    refine ⟨LL', _, hm2, ?_⟩
    rw [he]; exact hd
  · rintro ⟨LL', r'', hm, hd⟩
    obtain ⟨hm2, he⟩ := key LL' r'' hm
    refine ⟨LL', _, hm2, ?_⟩
    unfold LocBridge.IsCrysE at hd ⊢
    rw [he]; exact hd
  · rintro ⟨LL', r'', hm, hd⟩
    obtain ⟨hm2, he⟩ := key LL' r'' hm
    refine ⟨LL', _, hm2, ?_⟩
    rw [he]; exact hd
  · rintro τ J ⟨LL', r'', hm, hd, τ', hind, hc⟩
    obtain ⟨hm2, he⟩ := key LL' r'' hm
    refine ⟨LL', _, hm2, ?_, τ', ?_, ?_⟩
    · unfold LocBridge.IsdRE at hd ⊢
      rw [he]; exact hd
    · intro x
      have := hind (algebraMap F K x)
      simp only [RingHom.comp_apply]
      rw [this]
      congr 3
      exact congrArg Bw.j (IsScalarTower.algebraMap_apply F K Ω x).symm
    · intro n
      rw [hc n]
      unfold LocBridge.multE
      rw [he]
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Imports
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IsoOfFrobFree

private theorem contCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem main : IsoOfFrob := by
  intro F Ω _ _ _ _ _ l _ ι n r r' hr hr' hs hs' hw
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw)
  have hc : ∀ g : G F Ω, (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
    intro g
    ext i
    have h1 : Continuous fun g : G F Ω => (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr.comp continuous_inv))
    have h2 : Continuous fun g : G F Ω => (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr'.comp continuous_inv))
    refine congrFun (Continuous.ext_on hD h1 h2 ?_) g
    rintro σ ⟨v, hv, -, A, hA, hσ⟩
    obtain ⟨B, hB, hB'⟩ := not_not.1 hv
    have h := ((hB A hA).2 σ hσ).trans ((hB' A hA).2 σ hσ).symm
    have h' := Polynomial.map_injective ι.toRingHom ι.injective h
    simp only [h']
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' (fun g => by simpa using hc g⁻¹)
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩

end GlobalTheory.IsoOfFrobFree
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ImportsAlt
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LFun GlobalTheory.PRep

namespace GlobalTheory.RealGal.SatLocProof

theorem main : SatLoc := by
  intro F _ _ n w σ
  have hex : GlobalTheory.LGrp.IsSpherical σ.ρ (KGL w (n := n)) → ∃ B, HasSatGL w σ.ρ B :=
    GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred
  refine ⟨fun ⟨v, h0, hv⟩ => hex ((Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, h0⟩), ?_⟩
  intro V _ _ ρ ⟨hV, htop⟩ B
  have up : ∀ B, HasSatGL w σ.ρ B → HasSatGL w (ρ.comp (locGL F n w)) B := by
    intro B h
    constructor
    · obtain ⟨f, h0⟩ : ∃ f : {f : σ.V →ₗ[ℂ] V // ∀ g v, f (σ.ρ g v) = ρ (locGL F n w g) (f v)}, f.1 ≠ 0 := by
        by_contra hc
        push Not at hc
        refine top_ne_bot (htop.symm.trans (eq_bot_iff.2 (iSup_le fun f => ?_)))
        rw [hc f, LinearMap.range_zero]
      obtain ⟨x, hx⟩ := h.exists_vec
      have hi : LinearMap.ker f.1 = ⊥ := ((isIrreducible_iff σ.ρ).1 σ.irred).2 _ (fun g v hv => by
        rw [LinearMap.mem_ker] at hv ⊢
        rw [f.2, hv, map_zero]) |>.resolve_right fun e => h0 (LinearMap.ker_eq_top.1 e)
      have h1 := hx.map (ρ' := ρ.comp (locGL F n w)) f.1 f.2
        ((map_ne_zero_iff f.1 (LinearMap.ker_eq_bot.1 hi)).2 hx.1)
      exact (Submodule.ne_bot_iff _).2 ⟨_, h1.2.1, h1.1⟩
    · intro x hx h0
      exact GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup (ρ := ρ.comp (locGL F n w)) σ.irred h
        (fun f : {f : σ.V →ₗ[ℂ] V // ∀ g v, f (σ.ρ g v) = ρ (locGL F n w g) (f v)} => f.1) (fun f => f.2)
        (htop ▸ Submodule.mem_top) hx h0
  refine ⟨fun h => ?_, up B⟩
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 h.1
  obtain ⟨y, hy0, hy⟩ := LocSph.exists_fixed_of_mem_iSup (ρ.comp (locGL F n w)) σ.ρ σ.irred
    (fun f : {f : σ.V →ₗ[ℂ] V // ∀ g v, f (σ.ρ g v) = ρ (locGL F n w g) (f v)} => f.1) (fun f => f.2)
    (KGL w (n := n) : Set _) x hx0 (fun k hk => GlobalTheory.LGrp.mem_fixed.1 hx k hk) (htop ▸ Submodule.mem_top)
  obtain ⟨B', hB'⟩ := hex ((Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.LGrp.mem_fixed.2 hy, hy0⟩)
  exact (up B' hB').unique h ▸ hB'

end GlobalTheory.RealGal.SatLocProof
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ImportsFurther
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeMultOne

theorem main : ∀ (F : Type) [Field F] [NumberField F] (η η' : HChar F), (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, η.UnrAt v ∧ η'.UnrAt v ∧ η.val v = η'.val v) → η = η' := by
  intro F _ _ η η' h
  set S : Finset (HeightOneSpectrum (𝓞 F)) := (Filter.eventually_cofinite.mp h).toFinset with hS
  have key : η * η'⁻¹ = 1 := by
    refine Subtype.ext (GlobalTheory.FrobDense.eq_one_of_away (η * η'⁻¹).1 (η * η'⁻¹).2.1 (η * η'⁻¹).2.2 S fun v hv => ?_)
    have hv' : η.UnrAt v ∧ η'.UnrAt v ∧ η.val v = η'.val v := by
      by_contra hc
      exact hv (by rw [hS, Set.Finite.mem_toFinset]; exact hc)
    obtain ⟨h1, h2, h3⟩ := hv'
    intro x
    refine GlobalTheory.FrobDense.eq_one_of_unif ((η * η'⁻¹).loc v) (fun y hy => ?_) x
    change η.loc v y * (η'.loc v y)⁻¹ = 1
    rw [η.val_eq h1 y hy, η'.val_eq h2 y hy, h3, mul_inv_cancel]
  exact mul_inv_eq_one.mp key

end GlobalTheory.HeckeMultOne
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ImportsTer
section

end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.InducedEmbeddingExtends
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem induced_embedding_extends : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O), Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → ∀ (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' → ∃ (τK : K →+* Qbar l) (τ'' : ↥Bw'.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), τK.comp (algebraMap F K) = τ ∧ IsInduced Bw' τK τ'' := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ A O _ _ _ Bw Bw' hK hj τ LL' τ' hτ
  obtain ⟨Kw', j', j_E', _, _, _, _, _, _, _, _, _, _, _⟩ := Bw'
  dsimp only at hK hj ⊢
  subst hK
  subst hj
  let ι : K →+* ↥Bw.Kw.1 :=
    { toFun := fun x => ⟨Bw.j (algebraMap K Ω x), j_E' x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  refine ⟨(LL'.1.val.toRingHom.comp (τ'.toRingHom.comp ι)), τ', ?_, ?_⟩
  · ext x
    have := hτ x
    simp only [RingHom.coe_comp, Function.comp_apply] at this ⊢
    rw [this]
    have e : (ι (algebraMap F K x)) = ⟨Bw.j (algebraMap F Ω x), Bw.j_E x⟩ := by
      apply Subtype.ext
      simp [ι, ← IsScalarTower.algebraMap_apply]
    simp [e]
  · intro x
    rfl

end GlobalTheory
end

