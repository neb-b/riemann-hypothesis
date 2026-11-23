module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SphConj
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SmoEq
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.CbcSph
section
open NumberField IsDedekindDomain

private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

theorem UpperTheory.ConvolutionTheory.Sph.cbcSph :
    UpperTheory.ConvolutionTheory.Sph.CBCsph := by
  intro K M _ _ _ _ _ _ hp hK n hn π P hW v hv
  haveI := hK
  haveI hM : IsTotallyComplex M := isTotallyComplex_of_algebra K M
  haveI : Fact (Module.finrank K M).Prime := ⟨hp⟩
  haveI : FiniteDimensional K M := Module.finite_of_finrank_pos hp.pos
  haveI : IsCyclic (M ≃ₐ[K] M) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank K M)
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := M ≃ₐ[K] M)
  rcases π with @⟨_, π⟩ | @⟨hR, π⟩
  swap
  · exact (not_both K hR hK).elim
  rcases P with @⟨_, P⟩ | @⟨hR, P⟩
  swap
  · exact (not_both M hR hM).elim
  have hu : UpperTheory.ConvolutionTheory.GM.Unr M v := fun w =>
    hv w.1 (HeightOneSpectrum.ext (Ideal.LiesOver.over (P := w.1.asIdeal) (p := v.asIdeal)).symm)
  have hn' : 0 < n := hn
  exact ⟨fun B hB w hw f hf => UpperTheory.ConvolutionTheory.Sph.up K M σ hσ hp n hn' π P hW v hu B hB w hw f hf,
    fun h => UpperTheory.ConvolutionTheory.Sph.down K M σ hσ hp n hn' π P hW v hu h⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.RamSphOf
section
noncomputable section

open NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.LocGL Formalism.BasicNotions UpperTheory.CBC PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.ConvolutionTheory.Sph

private theorem not_split_of_ramified {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (v : Pl K) (u : PlacesOver M v) (hram : ¬ Algebra.IsUnramifiedAt (𝓞 K) u.1.asIdeal) : ¬ GM.Split M v := by
  intro hs
  haveI := u.2
  have hb : Function.Bijective (Algebra.linearMap (v.adicCompletion K) (u.1.adicCompletion M)) :=
    ⟨(completionMap v u.1).injective, hs u⟩
  have h : u.1.asIdeal.ramificationIdx (𝓞 K) * u.1.asIdeal.inertiaDeg (𝓞 K) = 1 := by
    rw [← finrank_eq_ramificationIdx_mul_inertiaDeg M v u.1, ← (LinearEquiv.ofBijective _ hb).finrank_eq,
      Module.finrank_self]
  exact hram (Ideal.ramificationIdx_eq_one_iff.1 (Nat.eq_one_of_mul_eq_one_right h))

private theorem unlinked_of {q : ℂ} {n : ℕ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (α : Fin n → ℂˣ)
    (h : ∀ a ∈ (Finset.univ.val.map fun i => α i ^ ε), ∀ b ∈ (Finset.univ.val.map fun i => α i ^ ε), (a : ℂ) ≠ q * b)
    (i j : Fin n) : (α i : ℂ) ≠ q * α j := by
  have hm : ∀ k, α k ^ ε ∈ (Finset.univ.val.map fun i => α i ^ ε) := fun k =>
    Multiset.mem_map_of_mem _ (Finset.mem_univ k)
  rcases hε with rfl | rfl
  · simpa using h _ (hm i) _ (hm j)
  · intro e
    apply h _ (hm j) _ (hm i)
    have hi : (α i : ℂ) ≠ 0 := (α i).ne_zero
    have hj : (α j : ℂ) ≠ 0 := (α j).ne_zero
    simp only [zpow_neg, zpow_one, Units.val_inv_eq_inv_val]
    rw [e]
    have hq : q ≠ 0 := fun h0 => hi (by rw [e, h0, zero_mul])
    field_simp

end UpperTheory.ConvolutionTheory.Sph

open UpperTheory.ConvolutionTheory.Sph in
theorem UpperTheory.ConvolutionTheory.Sph.ramSphOf :
    UpperTheory.Gal.Join.LocGal → UpperTheory.Gal.Join.LiftGood → UpperTheory.ConvolutionTheory.Sph.RamSph := by
  intro hLG hLift K M _ _ _ _ _ _ _ _ hp n hn π P hW w hram B hB
  let v : Pl K := w.under (𝓞 K)
  have hlies : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  let u : PlacesOver M v := ⟨w, hlies⟩
  have hns : ¬ GM.Split M v := not_split_of_ramified v u hram
  obtain ⟨hN, -, -⟩ := UpperTheory.ConvolutionTheory.Sph.normRam K M hp w hram
  have habs : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal := by
    simpa [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply, v] using hN
  haveI : Fact (Module.finrank K M).Prime := ⟨hp⟩
  haveI : IsCyclic (M ≃ₐ[K] M) := isCyclic_of_prime_card (p := Module.finrank K M) (IsGalois.card_aut_eq_finrank K M)
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := M ≃ₐ[K] M)
  obtain ⟨σw, N, hloc, hNorm, -⟩ := hLG K M σ hσ hp v u hns
  obtain ⟨ε, hε, hsd⟩ : SatDict := UpperTheory.ConvolutionTheory.Sph.satDict
  obtain ⟨hconj, hex, hex'⟩ := UpperTheory.ConvolutionTheory.Sph.weakStable K M hp n hn π P hW
  obtain ⟨τ, hτ⟩ := hex v
  obtain ⟨τ', hτ'⟩ := hex' w
  obtain ⟨d1, d2, d3⟩ := hsd K n π v τ hτ
  have hsph : IsSpherical τ.ρ := d1 ⟨B, hB⟩
  obtain ⟨α, hα⟩ := d2 hsph
  have hsat := d3 α hsph hα
  obtain rfl := SSatUniq_holds K n (.cx π) v _ _ hB hsat
  have hsub := hLift K M σ hσ hp n hn v u hns σw N (hloc n) hNorm π P hconj hW τ τ' hτ hτ'
    (fun i => unrChar (v.adicCompletion K) (α i)) (fun i => isSmoothChar_of_isUnram (isUnram_unrChar _ _)) hα
  have hcomp : ∀ i, (unrChar (v.adicCompletion K) (α i)).comp N = unrChar (w.adicCompletion M) (α i) := fun i =>
    UpperTheory.ConvolutionTheory.Sph.unrNorm K M v u σw _ N hNorm habs (α i)
  beta_reduce at hsub
  rw [funext hcomp] at hsub
  have hun := unlinked_of (q := (Ideal.absNorm w.asIdeal : ℂ)) hε α (by
    rw [habs]
    exact UpperTheory.ConvolutionTheory.Sph.unlinked K n hn π v _ hsat)
  have hsph' : IsSpherical τ'.ρ := UpperTheory.ConvolutionTheory.Sph.unlSph M n w τ' α hun hsub
  exact (hsd M n P w τ' hτ').2.2 α hsph' hsub
end
end

