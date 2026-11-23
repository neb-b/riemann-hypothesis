module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOneAlt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0003
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0001
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeaklyAttachedGaloisRepresentationBaseChangeRest
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0235
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResInjective

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.DownCrys
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core

theorem UpperTheory.Gal.Int.Core.downCrys_holds :
    SphDown .crys := by
  intro E Ω _ _ _ _ _ _ l _ ι a π Q P hPc r w B hB hQ1 hyp
  have hAF := GlobalTheory.automorphicFormsFiniteGL
  intro Pr AI hT A hA O _ _ _ Bw hj σ hσ hsph
  have hdec := hQ1 A hA
  have hjK := GlobalTheory.RealGal.bridge_j_mem_Kw_of_dec_le E Ω Q.K l A O Bw hdec
  obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge E Q.K Ω l A O Bw hjK
  have hj' : Induces Bw' := fun x => by rw [e2]; exact hj x
  obtain ⟨w', h', i, hi⟩ := GlobalTheory.PlaceIsoDec.exists_placeIso_of_dec_le_range E Ω Q.K w A hA hdec
  have hund : w'.under (𝓞 E) = w := by
    have := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver hA h'
    ext1
    exact this.over.symm
  obtain ⟨c, -, -, hq, -⟩ := GlobalTheory.WeilTransport.weil_equiv E Ω A w hA Q.K Ω A w' h' (RingEquiv.refl Ω) (algebraMap E Q.K) i hi
  have hB' : (CG.mk P).HasSat w' B := by
    have := hPc.sat w' 1 B (by rw [pow_one, hund, hq]) (by rw [hund]; exact hB)
    simpa using this
  obtain ⟨σ', hσ', -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp hAF Q.K a P w'
  obtain ⟨e, he⟩ := hPc.loc w w' i hi.cont hi.loc σ σ' hσ hσ'
  have hsph' := (GlobalTheory.CompletionIso.iwahori_spherical_transfer E Q.K w w' i hi.cont a σ σ' e he).2 hsph
  have hcr : ClauseAt .crys P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)) w' := hyp w' hund hB'
  exact (GlobalTheory.RealGal.dRSstCrysPstJumps_descend E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r).2.2.1
    (hcr Pr AI hT A h' O Bw' hj' σ' hσ' hsph')
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.DownDR
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core

set_option maxHeartbeats 1000000 in
theorem UpperTheory.Gal.Int.Core.downDR_holds :
    SphDown .dR := by
  intro E Ω _ _ _ _ _ _ l _ ι a π Q P hP r w B hB hdec hS
  show ClauseAt .dR π ι r w
  intro Pr AI hT A hA O _ _ _ Bw hj
  have hdA := hdec A hA
  have hjK := GlobalTheory.RealGal.bridge_j_mem_Kw_of_dec_le E Ω Q.K l A O Bw hdA
  obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge E Q.K Ω l A O Bw hjK
  have hj' : Induces Bw' := fun x => by rw [e2]; exact hj x
  obtain ⟨w', hu, hw', hn⟩ := GlobalTheory.PlaceNormDec.exists_place_normV_eq E Ω Q w A hA hdA
  have hBP : (CG.mk P).HasSat w' (B.map (· ^ 1)) :=
    hP.sat w' 1 B (by rw [hu, pow_one]; exact hn) (by rw [hu]; exact hB)
  have hc : ClauseAt .dR P ι _ w' := hS w' hu (by simpa using hBP)
  have hc' := hc Pr AI hT A hw' O Bw' hj'
  have D := GlobalTheory.RealGal.dRSstCrysPstJumps_descend E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r
  refine ⟨D.1 hc'.1, fun τ LL' τ' hτ J hJ => ?_⟩
  obtain ⟨τK, τ'', hτK, hind⟩ := GlobalTheory.induced_embedding_extends E Ω Q.K l A O Bw Bw' e1 e2 τ LL' τ' hτ
  have hJK : J.map (fun n : ℤ => (n : ℂ)) =
      ((CG.mk P).infChar (ι.toRingHom.comp τK)).map (fun z => ((a : ℂ) - 1) / 2 - z) := by
    rw [hP.inf, RingHom.comp_assoc, hτK]
    exact hJ
  have hres := D.2.2.2.2 τK J (hc'.2 τK LL' τ'' hind J hJK)
  rwa [hτK] at hres
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.DownUnr
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core

theorem UpperTheory.Gal.Int.Core.downUnr_holds :
    SphDown .unr := by
  intro E Ω _ _ _ _ _ _ l _ ι a π Q P hP ρ w B hB hQdec hyp hl A h
  obtain ⟨w', hunder, h', hN⟩ := GlobalTheory.PlaceNormDec.exists_place_normV_eq E Ω Q w A h (hQdec A h)
  have hB' : (CG.mk P).HasSat w' B := by
    have e := hP.sat w' 1 B (by rw [pow_one, hunder, hN]) (hunder ▸ hB)
    simpa using e
  have hlw : ((l : ℕ) : 𝓞 Q.K) ∉ w'.asIdeal := by
    intro hw
    apply hl
    have e1 := (h ((l : ℕ) : 𝓞 E))
    have e2 := (h' ((l : ℕ) : 𝓞 Q.K))
    simp only [map_natCast] at e1 e2
    exact e1.1 (e2.2 hw)
  have hcl := hyp w' hunder hB' hlw A h'
  rw [hN] at hcl
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · obtain ⟨s', rfl⟩ := hQdec A h (Ine_le_Dec A hs)
    exact hcl.1 s' hs
  · obtain ⟨σ', rfl⟩ := hQdec A h hσ.1
    have e := hcl.2 σ' hσ
    rw [← map_inv]
    exact e
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.OneConj
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc
open UpperTheory.Gal.Int.Core
open scoped Pointwise


open GlobalTheory.RealGal.AttConj in
theorem UpperTheory.Gal.Int.Core.oneConj_holds :
    OneConj := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ ι a sat r g c hc hsurj h
  have hcs : ∀ s y, c s y = g (s ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y)) := fun s y => DFunLike.congr_fun (hc s) y
  have hfwd : ∀ x : K, ∃ y : K, algebraMap K Ω y = g (algebraMap K Ω x) := fun x => by
    apply exists_of_fixed
    intro t
    obtain ⟨s, rfl⟩ := hsurj t
    rw [hcs, inv_apply_apply, s.commutes]
  have hbwd : ∀ x : K, ∃ y : K, algebraMap K Ω y = (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x) := fun x => by
    apply exists_of_fixed
    intro t
    have h1 := hcs t (algebraMap K Ω x)
    rw [(c t).commutes] at h1
    calc t ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x))
        = (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (g (t ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x)))) := (inv_apply_apply _ _).symm
      _ = (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x) := by rw [← h1]
  obtain ⟨γ, hγ⟩ := exists_ringEquiv g hfwd hbwd
  have hγinv : ∀ x : K, algebraMap K Ω (γ.symm x) = (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x) := fun x => by
    have h1 := hγ (γ.symm x)
    rw [RingEquiv.apply_symm_apply] at h1
    rw [h1, inv_apply_apply]
  have hγF : ∀ x : F, γ.symm (algebraMap F K x) = algebraMap F K x := fun x => by
    apply (algebraMap K Ω).injective
    rw [hγinv, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]
  set e : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv γ with he
  have heγ : ∀ y : 𝓞 K, ((e.symm y : 𝓞 K) : K) = γ.symm (y : K) := fun y => rfl
  let P : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K) :=
    fun w => w.comap (e.symm : 𝓞 K →+* 𝓞 K) e.symm.surjective
  have hPmem : ∀ w y, y ∈ (P w).asIdeal ↔ e.symm y ∈ w.asIdeal := fun _ _ => Iff.rfl
  have hPinj : Function.Injective P := by
    intro w1 w2 h12
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    have h3 := congrArg (fun w : HeightOneSpectrum (𝓞 K) => e x ∈ w.asIdeal) h12
    simp only [hPmem, RingEquiv.symm_apply_apply] at h3
    exact Iff.of_eq h3
  have hPunder : ∀ w, (P w).under (𝓞 F) = w.under (𝓞 F) := by
    intro w
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    show algebraMap (𝓞 F) (𝓞 K) x ∈ (P w).asIdeal ↔ algebraMap (𝓞 F) (𝓞 K) x ∈ w.asIdeal
    rw [hPmem]
    have h4 : e.symm (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 K) x :=
      RingOfIntegers.ext (by rw [heγ]; exact hγF x)
    rw [h4]
  have hPnorm : ∀ w, normV (P w) = normV w := by
    intro w
    unfold normV
    refine Nat.card_congr (Ideal.quotientEquiv (P w).asIdeal w.asIdeal e.symm ?_).toEquiv
    exact (Ideal.map_comap_of_surjective _ e.symm.surjective w.asIdeal).symm
  have hPplace : ∀ w (A : ValuationSubring Ω), IsPlaceOver A w → IsPlaceOver (g • A) (P w) := by
    intro w A hA y
    rw [val_lt_one_smul, hPmem, ← hA (e.symm y), heγ, hγinv]
  unfold AttOne at h ⊢
  filter_upwards [hPinj.tendsto_cofinite.eventually h] with w hw hp
  obtain ⟨B, hB, hE⟩ := hw (by rw [hPnorm]; exact hp)
  rw [hPunder] at hB
  rw [hPnorm] at hE
  refine ⟨B, hB, fun A hA => ?_⟩
  obtain ⟨hI, hF⟩ := hE (g • A) (hPplace w A hA)
  refine ⟨fun s hs => hI (c s) (ine_conj g c hc A s hs), fun σ hσ => ?_⟩
  have h5 := hF (c σ) (by rw [hPnorm]; exact frob_conj g c hc A _ σ hσ)
  rw [MonoidHom.comp_apply, map_inv]
  exact h5
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.OneTower
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core

private theorem normV_under_eq_of_normV_prime {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (w : HeightOneSpectrum (𝓞 M)) (hp : (normV w).Prime) : normV (w.under (𝓞 K)) = normV w := by
  let f : 𝓞 K ⧸ (w.under (𝓞 K)).asIdeal →+* 𝓞 M ⧸ w.asIdeal :=
    Ideal.quotientMap w.asIdeal (algebraMap (𝓞 K) (𝓞 M)) le_rfl
  have hf : Function.Injective f := Ideal.quotientMap_injective' le_rfl
  have hd : normV (w.under (𝓞 K)) ∣ normV w := by
    have h1 := AddSubgroup.card_addSubgroup_dvd_card f.toAddMonoidHom.range
    rwa [← Nat.card_congr (AddMonoidHom.ofInjective (f := f.toAddMonoidHom) hf).toEquiv] at h1
  rcases (Nat.dvd_prime hp).1 hd with h | h
  · exfalso
    haveI : (w.under (𝓞 K)).asIdeal.IsPrime := (w.under (𝓞 K)).isPrime
    have h2 := (Nat.card_eq_one_iff_unique.1 h).1
    exact not_subsingleton (𝓞 K ⧸ (w.under (𝓞 K)).asIdeal) h2
  · exact h

theorem UpperTheory.Gal.Int.Core.oneTower_holds :
    OneTower := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ M _ _ _ _ _ _ _ _ _ l _ ι a sat r hK
  unfold AttOne at hK ⊢
  have hT : Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K))
      Filter.cofinite Filter.cofinite := by
    refine ((Filter.tendstoCofinite_iff_finite_preimage_singleton _).2 ?_).tendsto_cofinite
    intro v
    refine (Ideal.finite_factors (I := v.asIdeal.map (algebraMap (𝓞 K) (𝓞 M))) ?_).subset ?_
    · exact Ideal.map_ne_bot_of_ne_bot v.ne_bot
    · intro w hw
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw
      show w.asIdeal ∣ _
      rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← hw]
      exact le_rfl
  filter_upwards [hT.eventually hK] with w hw hp
  have hn := normV_under_eq_of_normV_prime (K := K) w hp
  obtain ⟨B, hB, hF⟩ := hw (hn ▸ hp)
  refine ⟨B, ?_, ?_⟩
  · convert hB using 2
    ext x
    show algebraMap (𝓞 F) (𝓞 M) x ∈ w.asIdeal ↔ algebraMap (𝓞 K) (𝓞 M) (algebraMap (𝓞 F) (𝓞 K) x) ∈ w.asIdeal
    rw [show algebraMap (𝓞 K) (𝓞 M) (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 M) x from
      Subtype.ext (IsScalarTower.algebraMap_apply F K M (x : F)).symm]
  · rw [hn] at hF
    intro A hA
    have hA' : IsPlaceOver A (w.under (𝓞 K)) := by
      intro x
      rw [show algebraMap K Ω (x : K) = algebraMap M Ω ((algebraMap (𝓞 K) (𝓞 M) x : 𝓞 M) : M) from
        IsScalarTower.algebraMap_apply K M Ω (x : K)]
      exact hA _
    obtain ⟨hI, hFr⟩ := hF A hA'
    refine ⟨fun s hs => hI _ ?_, fun σ hσ => ?_⟩
    · obtain ⟨hs1, hs2⟩ := hs
      exact ⟨hs1, fun x hx => hs2 x hx⟩
    · have h3 := hFr (res K Ω M σ) ⟨hσ.1, fun x hx => by rw [hn]; exact hσ.2 x hx⟩
      rw [MonoidHom.comp_apply, map_inv]
      exact h3
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOne
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut

namespace UpperTheory.Gal.Int.Core

open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
open scoped Pointwise

private theorem uniq (hI : IsoOne) (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (hu : ∀ v B B', sat v B → sat v B' → B = B') (r r' : G K Ω →* GL (Fin a) (Qbar l)) (hc : Continuous r) (hc' : Continuous r') (hs : IsSSRep r) (hs' : IsSSRep r') (h : AttOne sat ι K r) (h' : AttOne sat ι K r') : RepIso r r' := by
  refine hI K Ω l ι a r r' hc hc' hs hs' ?_
  filter_upwards [h, h'] with w hw hw' hp
  obtain ⟨B, hB, hr⟩ := hw hp
  obtain ⟨B', hB', hr'⟩ := hw' hp
  obtain rfl := hu _ _ _ hB hB'
  exact ⟨_, hr, hr'⟩


open GlobalTheory.RealGal.TrInv in
private theorem trace_conj (hI : IsoOne) (hC : OneConj) (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (h2 : Module.finrank F K = 2) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (hu : ∀ v B B', sat v B → sat v B' → B = B') (r : G K Ω →* GL (Fin a) (Qbar l)) (hr : Continuous r) (hss : IsSSRep r) (hatt : AttOne sat ι K r) (g : G F Ω) (s s' : G K Ω) (hs : res F Ω K s' = g * res F Ω K s * g⁻¹) : ((r s' : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace = ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace := by
  haveI : Algebra.IsQuadraticExtension F K := ⟨h2⟩
  haveI : Normal F K := Algebra.IsQuadraticExtension.normal F K
  have hsur := conj_surjective (F := F) (Ω := Ω) K g
  have hatt' : AttOne sat ι K (r.comp (conj K g)) :=
    hC F Ω K l ι a sat r g (conj K g) (res_conj K g) hsur hatt
  obtain ⟨h, hh⟩ := uniq hI F Ω K l ι a sat hu r (r.comp (conj K g)) hr (hr.comp (continuous_conj K g)) hss
    (isSSRep_comp r _ hsur hss) hatt hatt'
  have hs' : s' = conj K g s := GlobalTheory.SatSysPatch.res_injective (F := F) (Ω := Ω) K (by rw [hs, res_conj])
  subst hs'
  rw [← MonoidHom.comp_apply, hh s]
  simp only [Units.val_mul]
  rw [Matrix.trace_mul_cycle]
  simp


open GlobalTheory.RealGalCompat in
private theorem trace_eq (hI : IsoOne) (hT : OneTower) (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (Q Q' : QCM F Ω) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (hu : ∀ v B B', sat v B → sat v B' → B = B') (r : G ↥Q.K Ω →* GL (Fin a) (Qbar l)) (r' : G ↥Q'.K Ω →* GL (Fin a) (Qbar l)) (hr : Continuous r) (hr' : Continuous r') (hs : IsSSRep r) (hs' : IsSSRep r') (ha : AttOne sat ι ↥Q.K r) (ha' : AttOne sat ι ↥Q'.K r') (s : G ↥Q.K Ω) (s' : G ↥Q'.K Ω) (hss : res F Ω ↥Q.K s = res F Ω ↥Q'.K s') : ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace = ((r' s' : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace := by
  let M : IntermediateField F Ω := Q.K ⊔ Q'.K
  haveI : FiniteDimensional F Q.K := Module.finite_of_finrank_pos (by rw [Q.two]; norm_num)
  haveI : FiniteDimensional F Q'.K := Module.finite_of_finrank_pos (by rw [Q'.two]; norm_num)
  haveI : NumberField M := NumberField.of_module_finite F M
  haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed F,
    haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic; Algebra.IsAlgebraic.tower_top (K := F) _⟩
  haveI : Algebra.IsQuadraticExtension F Q.K := { finrank_eq_two' := Q.two }
  haveI : Algebra.IsQuadraticExtension F Q'.K := { finrank_eq_two' := Q'.two }
  haveI : Normal F M := IntermediateField.normal_sup F Ω Q.K Q'.K
  letI : Algebra Q.K M := (IntermediateField.inclusion (le_sup_left : Q.K ≤ M)).toRingHom.toAlgebra
  letI : Algebra Q'.K M := (IntermediateField.inclusion (le_sup_right : Q'.K ≤ M)).toRingHom.toAlgebra
  haveI : IsScalarTower F Q.K M := IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion _).commutes x).symm
  haveI : IsScalarTower F Q'.K M := IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion _).commutes x).symm
  haveI : IsScalarTower Q.K M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : IsScalarTower Q'.K M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  have hA := hT F Ω Q.K M l ι a sat r ha
  have hA' := hT F Ω Q'.K M l ι a sat r' ha'
  have hS := UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a r (res Q.K Ω M) (range_res_normal (F := F)) hs
  have hS' := UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a r' (res Q'.K Ω M) (range_res_normal (F := F)) hs'
  have hC := hr.comp (UpperTheory.V.Af.continuous_restrictScalarsHom Q.K M Ω)
  have hC' := hr'.comp (UpperTheory.V.Af.continuous_restrictScalarsHom Q'.K M Ω)
  obtain ⟨g, hg⟩ := uniq hI F Ω M l ι a sat hu _ _ hC hC' hS hS' hA hA'
  set σ : G F Ω := res F Ω Q.K s with hσ
  have hfix : σ ∈ M.fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf]
    refine ⟨fun x => ?_, fun x => ?_⟩
    · exact s.commutes x
    · rw [hss]; exact s'.commutes x
  let t : G M Ω := IntermediateField.fixingSubgroupEquiv M ⟨σ, hfix⟩
  have ht : res Q.K Ω M t = s := by ext z; rfl
  have ht' : res Q'.K Ω M t = s' := by
    ext z
    exact congrArg (fun u : G F Ω => u z) hss
  have e := hg t
  simp only [MonoidHom.comp_apply, ht, ht'] at e
  rw [e, Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul]

theorem patchOne_holds : IsoOne → OneTower → OneConj → PatchOne := by
  intro hI hT hC F Ω _ _ _ _ _ l _ ι a sat hu S hS r hr
  classical
  haveI : Infinite ↥S := hS.to_subtype
  haveI : Algebra.IsIntegral F Ω := (IsAlgClosure.isAlgebraic (R := F) (K := Ω)).isIntegral
  obtain ⟨η, hηinj, hη⟩ := GlobalTheory.RealGal.SignChar.main F Ω
  let e : ∀ Q : ↥S, G ↥Q.1.K Ω ≃* (η Q.1).ker := fun Q =>
    (MonoidHom.ofInjective (GlobalTheory.SatSysPatch.res_injective F Ω ↥Q.1.K)).trans (MulEquiv.subgroupCongr (hη Q.1).1.symm)
  have he : ∀ Q : ↥S, ∀ (s : G ↥Q.1.K Ω), ((e Q s : (η Q.1).ker) : G F Ω) = res F Ω ↥Q.1.K s := fun Q s => rfl
  have hes : ∀ Q : ↥S, ∀ (h : (η Q.1).ker), res F Ω ↥Q.1.K ((e Q).symm h) = h := by
    intro Q h; rw [← he, MulEquiv.apply_symm_apply]
  let r' : ∀ Q : ↥S, (η Q.1).ker →* GL (Fin a) (Qbar l) := fun Q => (r Q).comp (e Q).symm.toMonoidHom
  have hr' : ∀ Q : ↥S, ∀ (h : (η Q.1).ker), r' Q h = r Q ((e Q).symm h) := fun Q h => rfl
  have hcont : ∀ Q : ↥S, Continuous (r' Q) := by
    intro Q
    haveI : CompactSpace (G ↥Q.1.K Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[↥Q.1.K] Ω))
    have hc : Continuous (e Q) := (UpperTheory.V.Af.continuous_restrictScalarsHom F ↥Q.1.K Ω).subtype_mk _
    let hm := hc.homeoOfEquivCompactToT2 (f := (e Q).toEquiv)
    exact (hr Q).1.comp hm.symm.continuous
  have hss : ∀ Q : ↥S, IsSSRep (r' Q) := by
    intro Q
    refine UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a (r Q) (e Q).symm.toMonoidHom ?_ (hr Q).2.1
    rw [MonoidHom.range_eq_top.mpr (e Q).symm.surjective]
    infer_instance
  obtain ⟨ρ, hρc, hρs, hev⟩ := GlobalTheory.IndexTwoPatch.main (G F Ω) (Qbar l) a ↥S (fun Q => η Q.1)
    (hηinj.comp Subtype.val_injective) (fun Q => (hη Q.1).2) r' (fun Q => ⟨hcont Q, hss Q⟩)
    (by
      intro Q g h h' hh
      rw [hr', hr']
      exact trace_conj hI hC F Ω ↥Q.1.K Q.1.two l ι a sat hu (r Q) (hr Q).1 (hr Q).2.1 (hr Q).2.2 g
        ((e Q).symm h) ((e Q).symm h') (by rw [hes, hes]; exact hh))
    (by
      intro Q Q' h h' hh
      rw [hr', hr']
      exact trace_eq hI hT F Ω Q.1 Q'.1 l ι a sat hu (r Q) (r Q') (hr Q).1 (hr Q').1 (hr Q).2.1 (hr Q').2.1
        (hr Q).2.2 (hr Q').2.2 _ _ (by rw [hes, hes]; exact hh))
  refine ⟨ρ, hρc, hρs, hev.mono fun Q hQ => ?_⟩
  have hres : IsSSRep (ρ.comp (res F Ω ↥Q.1.K)) := by
    refine UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a ρ (res F Ω ↥Q.1.K) ?_ hρs
    rw [← (hη Q.1).1]
    infer_instance
  refine GlobalTheory.TraceConj.main (G ↥Q.1.K Ω) (Qbar l) a (r Q) (ρ.comp (res F Ω ↥Q.1.K)) (hr Q).2.1 hres fun s => ?_
  have h1 := hQ (e Q s)
  rw [hr', MulEquiv.symm_apply_apply, he] at h1
  exact h1.symm

end UpperTheory.Gal.Int.Core

end
end

