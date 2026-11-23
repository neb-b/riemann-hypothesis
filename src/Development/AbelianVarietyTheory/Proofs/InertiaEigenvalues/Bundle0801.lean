module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0297
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0790
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompChainSpaceDefiniteAddNormalFrame
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0791
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharUnramifiedOutsideOfLPowerGaloisChar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnramPull

set_option maxHeartbeats 800000 in
theorem unramOutside_of_corr : ∀ (D : D7) (N : NData D.R D.host D.what₂) (art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E N.Om), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ (r : G D.host.E N.Om →* ℂˣ) (l n : ℕ), l.Prime → (∀ σ, r σ ^ (l ^ n) = 1) → ∀ (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → GlobalTheory.ToricDistribution.Corr art r χ → ∀ Q : Finset (Pl D.host.E), SplitSet Q → (∀ P ∈ Q, ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → (∀ v : Pl D.host.E, v ∉ Q → (∀ P ∈ Q, ¬ Formalism.BasicNotions.IsConjPl D.host P v) → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, r σ = 1) → GlobalTheory.ExportSeries.UnramOutside c Q := by
  intro D N art hart r l n hl hp c χ hc hcorr Q hQ hlQ hine
  intro x hx1 hx2 hx3 hxQ
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have hidem := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨M, hM, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 hidem c χ hc
  choose e he hinf he1 he0 using hidem
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E M hM
    (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  set f := idem Q + cA D (idem Q) with hf
  have hcf : cA D f = f := by rw [hf, map_add (f := _), GlobalTheory.DualPairCheck.cA_cA, add_comm]
  have hfe : ∀ P ∈ Q, idemAt P * f = idemAt P := by
    intro P hP
    have k1 : idemAt P * idem Q = idemAt P :=
      GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (hQ.isIdemAt ha).1) (fun a ha b hb hab => hQ.mul_eq_zero ha hb hab) hP
    have k2 : idemAt P * cA D (idem Q) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [idem, map_sum, Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj => hQ.mul_conj hP hj
    rw [hf, mul_add, k1, k2, add_zero]
  have hdelta : ∀ P e', GlobalTheory.IdemSupport.IsDelta Φ P e' → e P = e' := fun P e' h' =>
    GlobalTheory.IdemSupport.delta_unique hΦ ((GlobalTheory.IdemSupport.tie_iff hΦ (he P).1 (hinf P) P).1 (he P).2.2) h'
  have hcomp : ∀ P, (∃ a, e P = a ∧ a * f = a) → ι (finPart D (x : AE D)) P = 1 := by
    rintro P ⟨a, hea, haf⟩
    have k : e P * (x : AE D) = e P := by rw [hea, ← haf, mul_assoc, hxQ]
    have k' : ι (finPart D (e P * (x : AE D))) P = ι (finPart D (e P)) P := by rw [k]
    have e5 : ι (finPart D (e P * (x : AE D))) = ι (finPart D (e P)) * ι (finPart D (x : AE D)) := by
      rw [map_mul (finPart D) (e P) (x : AE D), map_mul ι]
    rw [e5] at k'
    change ι (finPart D (e P)) P * ι (finPart D (x : AE D)) P = ι (finPart D (e P)) P at k'
    rwa [he1 P, one_mul] at k'
  have hstar : ∀ z : D.host.E, star z = D.host.conj z := bridge_star_holds D.R D.host
  have hconj : ∀ P' v : Pl D.host.E, Formalism.BasicNotions.IsConjPl D.host P' v → v = GlobalTheory.IdemSupport.cP P' := by
    intro P' v h
    refine (GlobalTheory.IdemSupport.eq_of_le fun y hy => ?_).symm
    refine (h (GlobalTheory.IdemSupport.cO D y) y ?_).1 hy
    rw [GlobalTheory.IdemSupport.cO_coe, ← hstar, star_star]
  have hlconj : ∀ P' v : Pl D.host.E, Formalism.BasicNotions.IsConjPl D.host P' v →
      (((l : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal ↔ ((l : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal) := by
    intro P' v h
    refine h _ _ ?_
    push_cast
    exact (map_natCast _ l).symm
  have hv : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    intro P
    have a := (h2 _).1 hx2 P
    have b := (h2 _).1 hx3 P
    have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := by
      rw [← map_mul]
      have : ι (finPart D (x : AE D)) P * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P = 1 := by
        change (ι (finPart D (x : AE D)) * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D))) P = 1
        rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
        rfl
      rw [this, map_one]
    refine le_antisymm a ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := e'.symm
      _ ≤ Valued.v (ι (finPart D (x : AE D)) P) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _
  have key := hprod x hx1 S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  apply Subtype.ext
  refine key.trans (Finset.prod_eq_one fun P hP => ?_)
  obtain ⟨a, -, b⟩ := hS P hP
  have a' : Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) := a
  have b' : Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) ≤
      WithZero.exp (-1 : ℤ) * P.valuation D.host.E (k P : D.host.E) := b
  rw [hv P] at a'
  rw [← a', mul_one] at b'
  have hun : Formalism.L2.Host.IsUnitAt P (Formalism.L2.Host.atFin P (k P)) := by
    show Valued.v (((k P : D.host.E)) : P.adicCompletion D.host.E) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← a']
  have : χ.locK P (k P) = 1 := by
    show χ.loc P (Formalism.L2.Host.atFin P (k P)) = 1
    by_cases hPQ : P ∈ Q ∨ ∃ P' ∈ Q, Formalism.BasicNotions.IsConjPl D.host P' P
    · have hlP : ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
        rcases hPQ with hPQ | ⟨P', hP', hc'⟩
        · exact hlQ P hPQ
        · exact fun hm => hlQ P' hP' ((hlconj P' P hc').2 hm)
      have h1P : ι (finPart D (x : AE D)) P = 1 := by
        refine hcomp P ?_
        rcases hPQ with hPQ | ⟨P', hP', hc'⟩
        · exact ⟨idemAt P, hdelta P _ (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (hQ.isIdemAt hPQ)), hfe P hPQ⟩
        · refine ⟨cA D (idemAt P'), ?_, ?_⟩
          · rw [hconj P' P hc']
            exact hdelta _ _ (GlobalTheory.IdemSupport.delta_conj hΦ (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (hQ.isIdemAt hP')))
          · rw [← hcf, ← map_mul, hfe P' hP']
      have ht := GlobalTheory.ToricDistribution.levelLe_one_of_pow hl (hcorr.pow hp) hlP
      refine ht _ hun ?_
      rw [h1P] at b'
      have e4 : ((Formalism.L2.Host.atFin P (k P) : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) - 1 =
          -(1 - algebraMap D.host.E _ (k P : D.host.E)) := by
        show algebraMap D.host.E _ (k P : D.host.E) - 1 = _
        ring
      rw [e4, Valuation.map_neg]
      simpa using b'
    · push_neg at hPQ
      obtain ⟨B, hB⟩ := ReciprocityTheory.Gal.exists_isPlaceOver N.Om P
      exact GlobalTheory.ToricDistribution.Corr.unr hart hcorr hB (hine P hPQ.1 hPQ.2 B hB) _ hun
  show ((χ.locK P (k P) : ℂˣ) : ℂ) = 1
  rw [this, Units.val_one]

end GlobalTheory.UnramPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharUnramifiedOutsideSplitSetOfTame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnramTame

set_option maxHeartbeats 800000 in
theorem unramOutside_of_corr_of_tame : ∀ (D : D7) (N : NData D.R D.host D.what₂) (art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E N.Om), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ (r : G D.host.E N.Om →* ℂˣ) (M : ℕ), M ≠ 0 → (∀ σ, r σ ^ M = 1) → ∀ (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → GlobalTheory.ToricDistribution.Corr art r χ → ∀ Q : Finset (Pl D.host.E), SplitSet Q → (∀ P ∈ Q, ∀ P' : Pl D.host.E, (P' = P ∨ Formalism.BasicNotions.IsConjPl D.host P P') → χ.TameAt P') → (∀ v : Pl D.host.E, v ∉ Q → (∀ P ∈ Q, ¬ Formalism.BasicNotions.IsConjPl D.host P v) → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, r σ = 1) → GlobalTheory.ExportSeries.UnramOutside c Q := by
  intro D N art hart r Mo hMo hMr c χ hc hcorr Q hQ htame hine
  intro x hx1 hx2 hx3 hxQ
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have hidem := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨M, hM, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 hidem c χ hc
  choose e he hinf he1 he0 using hidem
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E M hM
    (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  set f := idem Q + cA D (idem Q) with hf
  have hcf : cA D f = f := by rw [hf, map_add (f := _), GlobalTheory.DualPairCheck.cA_cA, add_comm]
  have hfe : ∀ P ∈ Q, idemAt P * f = idemAt P := by
    intro P hP
    have k1 : idemAt P * idem Q = idemAt P :=
      GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (hQ.isIdemAt ha).1) (fun a ha b hb hab => hQ.mul_eq_zero ha hb hab) hP
    have k2 : idemAt P * cA D (idem Q) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [idem, map_sum, Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj => hQ.mul_conj hP hj
    rw [hf, mul_add, k1, k2, add_zero]
  have hdelta : ∀ P e', GlobalTheory.IdemSupport.IsDelta Φ P e' → e P = e' := fun P e' h' =>
    GlobalTheory.IdemSupport.delta_unique hΦ ((GlobalTheory.IdemSupport.tie_iff hΦ (he P).1 (hinf P) P).1 (he P).2.2) h'
  have hcomp : ∀ P, (∃ a, e P = a ∧ a * f = a) → ι (finPart D (x : AE D)) P = 1 := by
    rintro P ⟨a, hea, haf⟩
    have k : e P * (x : AE D) = e P := by rw [hea, ← haf, mul_assoc, hxQ]
    have k' : ι (finPart D (e P * (x : AE D))) P = ι (finPart D (e P)) P := by rw [k]
    have e5 : ι (finPart D (e P * (x : AE D))) = ι (finPart D (e P)) * ι (finPart D (x : AE D)) := by
      rw [map_mul (finPart D) (e P) (x : AE D), map_mul ι]
    rw [e5] at k'
    change ι (finPart D (e P)) P * ι (finPart D (x : AE D)) P = ι (finPart D (e P)) P at k'
    rwa [he1 P, one_mul] at k'
  have hstar : ∀ z : D.host.E, star z = D.host.conj z := bridge_star_holds D.R D.host
  have hconj : ∀ P' v : Pl D.host.E, Formalism.BasicNotions.IsConjPl D.host P' v → v = GlobalTheory.IdemSupport.cP P' := by
    intro P' v h
    refine (GlobalTheory.IdemSupport.eq_of_le fun y hy => ?_).symm
    refine (h (GlobalTheory.IdemSupport.cO D y) y ?_).1 hy
    rw [GlobalTheory.IdemSupport.cO_coe, ← hstar, star_star]
  have hv : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    intro P
    have a := (h2 _).1 hx2 P
    have b := (h2 _).1 hx3 P
    have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := by
      rw [← map_mul]
      have : ι (finPart D (x : AE D)) P * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P = 1 := by
        change (ι (finPart D (x : AE D)) * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D))) P = 1
        rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
        rfl
      rw [this, map_one]
    refine le_antisymm a ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := e'.symm
      _ ≤ Valued.v (ι (finPart D (x : AE D)) P) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _
  have key := hprod x hx1 S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  apply Subtype.ext
  refine key.trans (Finset.prod_eq_one fun P hP => ?_)
  obtain ⟨a, -, b⟩ := hS P hP
  have a' : Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) := a
  have b' : Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) ≤
      WithZero.exp (-1 : ℤ) * P.valuation D.host.E (k P : D.host.E) := b
  rw [hv P] at a'
  rw [← a', mul_one] at b'
  have hun : Formalism.L2.Host.IsUnitAt P (Formalism.L2.Host.atFin P (k P)) := by
    show Valued.v (((k P : D.host.E)) : P.adicCompletion D.host.E) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← a']
  have : χ.locK P (k P) = 1 := by
    show χ.loc P (Formalism.L2.Host.atFin P (k P)) = 1
    by_cases hPQ : P ∈ Q ∨ ∃ P' ∈ Q, Formalism.BasicNotions.IsConjPl D.host P' P
    · have h1P : ι (finPart D (x : AE D)) P = 1 := by
        refine hcomp P ?_
        rcases hPQ with hPQ | ⟨P', hP', hc'⟩
        · exact ⟨idemAt P, hdelta P _ (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (hQ.isIdemAt hPQ)), hfe P hPQ⟩
        · refine ⟨cA D (idemAt P'), ?_, ?_⟩
          · rw [hconj P' P hc']
            exact hdelta _ _ (GlobalTheory.IdemSupport.delta_conj hΦ (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (hQ.isIdemAt hP')))
          · rw [← hcf, ← map_mul, hfe P' hP']
      have ht : χ.TameAt P := by
        rcases hPQ with hPQ | ⟨P', hP', hc'⟩
        · exact htame P hPQ P (Or.inl rfl)
        · exact htame P' hP' P (Or.inr hc')
      refine ht _ hun ?_
      rw [h1P] at b'
      have e4 : ((Formalism.L2.Host.atFin P (k P) : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) - 1 =
          -(1 - algebraMap D.host.E _ (k P : D.host.E)) := by
        show algebraMap D.host.E _ (k P : D.host.E) - 1 = _
        ring
      rw [e4, Valuation.map_neg]
      simpa using b'
    · push_neg at hPQ
      obtain ⟨B, hB⟩ := ReciprocityTheory.Gal.exists_isPlaceOver N.Om P
      exact GlobalTheory.ToricDistribution.Corr.unr hart hcorr hB (hine P hPQ.1 hPQ.2 B hB) _ hun
  show ((χ.locK P (k P) : ℂˣ) : ℂ) = 1
  rw [this, Units.val_one]

end GlobalTheory.UnramTame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterValueAtConjugatePlacePow
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjLocVal

theorem value_at_conj_place : ∀ (D : D7) (PP : Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (n : ℕ) (y : (AE D)ˣ), Formalism.L2.NTheta.IsIdemAt e PP → ϖ ∈ PP.asIdeal → ϖ ∉ PP.asIdeal ^ 2 → ChrEq c χ → χ.UnrAt (Formalism.L2.DIV.conjPl PP) → (y : AE D) = 1 + cA D e * (incA D (star (ϖ : D.host.E)) ^ n - 1) → ((c y : Circle) : ℂ) = ((χ.val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) ^ n := by
  intro D PP e ϖ c χ n y he h1 h2 hc hU hy
  obtain ⟨⟨e1, e2, v, ε, hε, e3⟩, e4⟩ := Formalism.IndefR.Fin.LevelGroupLemmas.isIdemAt_conj he
  have hpl : Formalism.L2.JoinChr.IsPlIdem D (cA D e) (Formalism.L2.DIV.conjPl PP) := ⟨e1, ⟨v, ε, hε, Or.inl ⟨e2, e3⟩⟩, e4⟩
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact h2 (zero_mem _)
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  have hs0 : star (ϖ : D.host.E) ≠ 0 := star_ne_zero.2 hϖE
  set k : D.host.Eˣ := Units.mk0 (star (ϖ : D.host.E)) hs0 with hk
  have hy' : (y : AE D) = Formalism.L2.JoinChr.locE D (cA D e) ((k ^ n : D.host.Eˣ) : D.host.E) := by
    rw [hy, Formalism.L2.JoinChr.locE, Units.val_pow_eq_pow_val, map_pow]
    rfl
  rw [hc.2 _ _ hpl (k ^ n) y hy', map_pow, Units.val_pow_eq_pow_val]
  congr 1
  have hmem : Formalism.L2.DIV.starO ϖ ∈ (Formalism.L2.DIV.conjPl PP).asIdeal := by
    show Formalism.L2.DIV.starO (Formalism.L2.DIV.starO ϖ) ∈ PP.asIdeal
    rw [Formalism.L2.DIV.starO_starO]; exact h1
  have hnsq : Formalism.L2.DIV.starO ϖ ∉ (Formalism.L2.DIV.conjPl PP).asIdeal ^ 2 := by
    intro hm
    have hm' := Ideal.le_comap_pow (f := Formalism.L2.DIV.starOHom) (K := PP.asIdeal) 2 hm
    rw [Ideal.mem_comap] at hm'
    apply h2
    have : Formalism.L2.DIV.starOHom (Formalism.L2.DIV.starO ϖ) = ϖ := Formalism.L2.DIV.starO_starO ϖ
    rwa [this] at hm'
  have hunif : Formalism.L2.Host.IsUnifAt (Formalism.L2.DIV.conjPl PP) (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) k) := by
    show Valued.v (((star (ϖ : D.host.E) : D.host.E)) : (Formalism.L2.DIV.conjPl PP).adicCompletion D.host.E) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← Formalism.L2.DIV.starO_coe,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact GlobalTheory.LatIntFacts.intValuation_uniformiser _ hmem hnsq
  have hval : χ.loc (Formalism.L2.DIV.conjPl PP) (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) k) = χ.val (Formalism.L2.DIV.conjPl PP) := by
    have hu : Formalism.L2.Host.IsUnitAt (Formalism.L2.DIV.conjPl PP)
        (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) k * (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) (Formalism.L2.Host.unif (Formalism.L2.DIV.conjPl PP)))⁻¹) := by
      have h2' := Formalism.L2.Host.unif_spec (Formalism.L2.DIV.conjPl PP)
      unfold Formalism.L2.Host.IsUnitAt
      unfold Formalism.L2.Host.IsUnifAt at hunif h2'
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hunif, h2']
      exact mul_inv_cancel₀ (by simp)
    have h3 := hU _ hu
    rw [map_mul, map_inv, mul_inv_eq_one] at h3
    exact h3
  show ((χ.loc (Formalism.L2.DIV.conjPl PP) (Formalism.L2.Host.atFin (Formalism.L2.DIV.conjPl PP) k) : ℂˣ) : ℂ) = _
  rw [hval]

end GlobalTheory.ConjLocVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelHalfLeConjPlaceOfNotLe
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem mb_le_conjPl_of_not_le : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (l₂ : Geo.Tor.Level H) (Q : Formalism.L2.DIV.Pl D.host.E), ((l₂.M : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ¬ l₂.Mb ≤ Q.asIdeal → l₂.Mb ≤ (Formalism.L2.DIV.conjPl Q).asIdeal := by
  intro D H l₂ Q hM hnot
  have hprod : l₂.Mb * l₂.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ Q.asIdeal := by
    rw [l₂.prod, Ideal.span_le, Set.singleton_subset_iff]; exact hM
  rcases Ideal.IsPrime.mul_le Q.isPrime |>.1 hprod with h | h
  · exact absurd h hnot
  · rw [Ideal.map_le_iff_le_comap] at h
    intro x hx
    have hx' := h hx
    show Formalism.L2.DIV.starOHom x ∈ Q.asIdeal
    have e : Formalism.L2.DIV.starOHom x = (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) x := by
      apply RingOfIntegers.ext
      have hb := H.bar_eq x
      simp only [RingEquiv.coe_toRingHom] at hb ⊢
      rw [hb]
      exact Formalism.L2.DIV.starO_coe x
    rw [e]; exact hx'

end GlobalTheory.LevelSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

theorem linearIndependent_rows_map {K L : Type*} [Field K] [Field L] (e : K →+* L) {n m : ℕ}
    (a : Fin n → Fin m → K) (ha : LinearIndependent K a) :
    LinearIndependent L fun c k => e (a c k) := by
  classical
  obtain ⟨g, hg⟩ := (Fintype.linearCombination K a).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 ha.fintypeLinearCombination_injective)
  have hj : ∀ c j, g (a c) j = if c = j then 1 else 0 := fun c j => by
    have := congrFun (LinearMap.congr_fun hg (Pi.single c 1)) j
    simpa [Pi.single_apply, eq_comm] using this
  have hg' : ∀ (x : Fin m → K) j, g x j = ∑ k, x k * g (fun j' => if k = j' then 1 else 0) j := fun x j => by
    conv_lhs => rw [pi_eq_sum_univ x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply]
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.linearIndependent_iff]
  intro μ hμ j
  have h0 : ∀ k, ∑ c, μ c * e (a c k) = 0 := fun k => by
    have := congrFun hμ k
    simpa [Finset.sum_apply] using this
  calc μ j = ∑ c, μ c * e (g (a c) j) := by simp [hj]
    _ = ∑ c, ∑ k, μ c * e (a c k * g (fun j' => if k = j' then 1 else 0) j) :=
        Finset.sum_congr rfl fun c _ => by rw [hg' (a c) j, map_sum, Finset.mul_sum]
    _ = ∑ k, e (g (fun j' => if k = j' then 1 else 0) j) * ∑ c, μ c * e (a c k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [map_mul]
        ring
    _ = 0 := by simp [h0]

theorem realRd_faithful : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ), ν ≠ 0 → Rl.toRealDat.LUnif → Rl.toRealDat.models_HW → FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _) → (S.A ((j : ℕ) + 1)).IsKsForm → Faithful (realRd YS v₀ hρ i j b ν) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG S YS v₀ ρ hρ i j b ν hν hU hW hv hK
  classical
  let L : (Rl.HW j (sg0 D A3.A)).H →ₗ[ℂ] (GA D (Wc D j) → ℂ) :=
    { toFun := fun x => (Rl.HW j (sg0 D A3.A)).e x (v₀ j _)
      map_add' := fun x y => by rw [map_add (f := _)]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hL : LinearMap.ker L = ⊥ :=
    LinearMap.ker_eq_bot.2 fun x y h => GlobalTheory.LiftScalarCompare.eval_inj hW hv h
  obtain ⟨m, bb, -, hKs, hspan, hLL, -⟩ := hK
  let bK : Module.Basis (Fin m) S.Ks ↥(S.A ((j : ℕ) + 1)).WK :=
    (Module.Basis.span hKs).map (LinearEquiv.ofEq _ _ hspan)
  have hbK : ∀ k, ((bK k : ↥(S.A ((j : ℕ) + 1)).WK) : S.WL ((j : ℕ) + 1)) = bb k := fun k => by
    simp [bK, Module.Basis.span_apply]
  let φ : Fin m → (GA D (Wc D j) → ℂ) := fun k => evW YS v₀ j (bb k)
  have hφ : LinearIndependent ℂ φ := by
    have h1 : LinearIndependent D.what₂.LL fun k => (YS.fi j).e (bb k) :=
      hLL.map' (YS.fi j).e.toLinearMap (YS.fi j).e.ker
    exact ((hU j (sg0 D A3.A)).1 m _ h1).map' L hL
  let B : Module.Basis (Fin m) (NX.KB S i b) (NX.Fm S i ((j : ℕ) + 1) b) :=
    Algebra.TensorProduct.basis (NX.KB S i b) bK
  intro n v hvi
  let w : Fin n → NX.Fm S i ((j : ℕ) + 1) b := fun c => YS.eF i _ b (Nat.le_add_left _ _) j.2 (v c)
  have hw0 : LinearIndependent (FractionRing (D.ntw.O i)) w :=
    hvi.map' (YS.eF i _ b (Nat.le_add_left _ _) j.2).toLinearMap (YS.eF i _ b (Nat.le_add_left _ _) j.2).ker
  have hw1 : LinearIndependent (NX.KB S i b) w := hw0
  have hw : LinearIndependent (NX.KB S i b) fun c => B.equivFun (w c) :=
    hw1.map' B.equivFun.toLinearMap B.equivFun.ker
  have hr := linearIndependent_rows_map (ρ.e i b) (fun c => B.equivFun (w c)) hw
  let Ψ : (Fin m → ℂ) →ₗ[ℂ] (GA D (Wc D j) → ℂ) := ν⁻¹ • Fintype.linearCombination ℂ φ
  have hΨ : LinearMap.ker Ψ = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun z hz => ?_
    have h0 : Fintype.linearCombination ℂ φ z = 0 := by
      have := hz
      simp only [Ψ, LinearMap.smul_apply, smul_eq_zero, inv_eq_zero, hν, false_or] at this
      exact this
    exact hφ.fintypeLinearCombination_injective (h0.trans (map_zero _).symm)
  suffices key : (fun c => realRd YS v₀ hρ i j b ν (v c)) = Ψ ∘ fun c k => ρ.e i b (B.equivFun (w c) k) by
    rw [key]; exact hr.map' Ψ hΨ
  funext c
  change ν⁻¹ • evK YS v₀ hρ i j b (w c) = ν⁻¹ • Fintype.linearCombination ℂ φ _
  congr 1
  rw [Fintype.linearCombination_apply]
  conv_lhs => rw [← B.sum_equivFun (w c)]
  refine (map_sum (evK YS v₀ hρ i j b) _ _).trans ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show B k = ((1 : NX.KB S i b) ⊗ₜ[S.Ks] bK k : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) from
    Algebra.TensorProduct.basis_apply _ _]
  change evK YS v₀ hρ i j b ((B.equivFun (w c) k • (1 : NX.KB S i b)) ⊗ₜ[S.Ks] (bK k : NX.FmK S ((j : ℕ) + 1))) = _
  rw [smul_eq_mul, mul_one]
  refine (evK_tmul YS v₀ hρ i j b _ _).trans ?_
  exact congrArg _ (congrArg (evW YS v₀ j) (hbK k))

end GlobalTheory.SeriesTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanTranslatesConjugateHalfTwistPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_translates_conjugateHalf_twistPlace : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)), T.rank ≤ S.rank → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), ∀ N : ℕ, IsBaseFrame S βS ΛS N → Submodule.IsFullLattice D.host.E ΛS → Submodule.IsFullLattice D.host.E ΛT → ∀ (e : AE D) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP → ∀ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ, ξ PP ≠ 1 → ∀ Φ : WO S T → ℂ, IsSBHalf (cA D e) (latH S T ΛS ΛT) Φ → (∀ κ : GA D S, SuppAt e S κ → κ ∈ GfC S → finE S κ ∈ St βS → redFn βS PP (finE S κ) ∈ blockTri (blk2 T.rank) → (∀ PP', PP' ≠ PP → ¬ Formalism.IndefR.Lev.IsConjPl PP PP' → redFn βS PP' (finE S κ) = 1) → ∀ x x' : WO S T, IsHalf (cA D e) x → IsHalf (cA D e) x' → Φ (actO S T κ 1 x) * adjDat S T βS βT e (omegaQ {PP} T.rank ξ (-1)) x' = Φ x * adjDat S T βS βT e (omegaQ {PP} T.rank ξ (-1)) (actO S T κ 1 x')) → Φ ∈ Submodule.span ℂ (translT S T (cA D e) (adjDat S T βS βT e (omegaQ {PP} T.rank ξ (-1)))) := by
  intro D S T βS βT hr ΛS ΛT N hB hS hT e PP he ξ hξ Φ hΦ hlaw
  exact GlobalTheory.DownLift.ConjHalfGen.mem_span_translT D S T βS βT hr ΛS ΛT N hB
    (by first | exact hS | exact hS.toIsLattice) (by first | exact hT | exact hT.toIsLattice)
    e PP he ξ hξ Φ hΦ hlaw
end

