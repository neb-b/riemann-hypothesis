module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.NormSpan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.CentChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CharEq
section
attribute [local instance] UpperTheory.V.QbarInst.charZero UpperTheory.V.QbarInst.torsionFree UpperTheory.V.QbarInst.algClosure

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd

noncomputable section

namespace UpperTheory.V.Br.CharacterEquality

private theorem normV_inj : Function.Injective fun w : Pl ℚ => normV w := fun v w h =>
  HeightOneSpectrum.ext (by rw [(places v).2.1, (places w).2.1, show normV v = normV w from h])

private theorem normV_surj {p : ℕ} (hp : p.Prime) : ∃ w : Pl ℚ, normV w = p := by
  have h0 : Prime ((p : ℕ) : 𝓞 ℚ) := by
    have h : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
    have e : ((p : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((p : ℕ) : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h
  let w : Pl ℚ := ⟨Ideal.span {((p : ℕ) : 𝓞 ℚ)}, (Ideal.span_singleton_prime h0.ne_zero).mpr h0,
    by rw [Ne, Ideal.span_singleton_eq_bot]; exact h0.ne_zero⟩
  refine ⟨w, (places w).2.2.1.symm.trans ?_⟩
  change Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  simp

private theorem tr_det {K : Type} [Field K] (ι : K ≃+* ℂ) {A : Matrix (Fin 2) (Fin 2) K} {a d : ℂ}
    (h : A.charpoly.map ι.toRingHom = X ^ 2 - C a * X + C d) : ι A.trace = a ∧ ι A.det = d := by
  rw [Matrix.charpoly_fin_two] at h
  have h0 := congrArg (AddMonoidAlgebra.coeff · 0) h
  have h1 := congrArg (AddMonoidAlgebra.coeff · 1) h
  simp at h0 h1
  exact ⟨h1, h0⟩

private theorem two_det {K : Type} [CommRing K] (A : Matrix (Fin 2) (Fin 2) K) :
    2 * A.det = A.trace ^ 2 - (A * A).trace := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem exists_rep (P : HypothesesH) (ι : Qbar 2 ≃+* ℂ) {k N : ℕ} [NeZero N] (hk : 2 ≤ k) {χ : DirichletCharacter ℂ N}
    (g : Eigenform k N χ) : ∃ r : G ℚ (AlgebraicClosure ℚ) →* GL (Fin 2) (Qbar 2), Continuous r ∧
      ∀ᶠ w : Pl ℚ in Filter.cofinite, ∀ A : ValuationSubring (AlgebraicClosure ℚ), IsPlaceOver A w →
        ∀ σ : G ℚ (AlgebraicClosure ℚ), IsFrob A (normV w) σ →
          ι (r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar 2)).trace = g.a (normV w) ∧
          ι (r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar 2)).det = χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1) := by
  obtain ⟨ω, φ, hω, hval, hφ, hcu⟩ := adelise k N hk χ g
  obtain ⟨π, hreg, ⟨χ', hpol⟩, -, -, hsat⟩ := holRep P ℚ k hk _ ω hω φ _ hφ hcu
  obtain ⟨r, wt, HT, hG, hatt, -⟩ := exR P ℚ (AlgebraicClosure ℚ) 2 ι 2 one_le_two π χ' hreg hpol
  refine ⟨r, hG.cont, ?_⟩
  filter_upwards [hatt.2, normV_inj.tendsto_cofinite.eventually (Set.finite_le_nat N).eventually_cofinite_notMem]
    with w ⟨B₁, hB₁, hF⟩ hw A hA σ hσ
  have hq : ¬ normV w ∣ N := fun h => hw (Nat.le_of_dvd (NeZero.pos N) h)
  obtain ⟨B₂, hB₂, e⟩ := hsat w (Nat.factorization_eq_zero_of_not_dvd hq)
  obtain rfl := hB₁.unique hB₂
  rw [← (hval w hq).2]
  exact tr_det ι (((hF A hA).2 σ hσ).trans e)

end UpperTheory.V.Br.CharacterEquality
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RepEig
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd
  UpperTheory.V.Br CongruenceSubgroup

private theorem untwist (k N : ℕ) [NeZero N] (hk : 1 ≤ k) (χ ψ : DirichletCharacter ℂ N) (g : Eigenform k N χ) :
    ∃ (χ' : DirichletCharacter ℂ (N * N)) (g' : Eigenform k (N * N) χ'), ∀ p : ℕ, p.Prime → ¬ p ∣ N →
      g'.a p * ψ (p : ZMod N) = g.a p ∧ χ' (p : ZMod (N * N)) * ψ (p : ZMod N) ^ 2 = χ (p : ZMod N) := by
  haveI : NeZero (N * N) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne N)⟩
  obtain ⟨h, hc, hn⟩ := clTwist N k χ ψ⁻¹ g.f g.char
  have h0 : h ≠ 0 := by
    rintro rfl
    have := hn 1
    rw [g.one, Nat.cast_one, map_one, mul_one] at this
    simp [coef, UpperHalfPlane.qExpansion_zero] at this
  obtain ⟨g', hg'⟩ := eigEx (N * N) k hk _ h hc h0 fun p => ψ⁻¹ (p : ZMod N) * g.a p
  refine ⟨_, g', fun p hp hd => ?_⟩
  have hu : IsUnit (p : ZMod (N * N)) :=
    (ZMod.isUnit_prime_iff_not_dvd hp).2 fun e => hd ((hp.dvd_mul.1 e).elim id id)
  have hu' : IsUnit (p : ZMod N) := (ZMod.isUnit_prime_iff_not_dvd hp).2 hd
  have e : DirichletCharacter.changeLevel (dvd_mul_right N N) (χ * ψ⁻¹ ^ 2) (p : ZMod (N * N)) =
      χ (p : ZMod N) * ψ⁻¹ (p : ZMod N) ^ 2 := by
    have := DirichletCharacter.changeLevel_eq_cast_of_dvd (χ * ψ⁻¹ ^ 2) (dvd_mul_right N N) hu.unit
    rw [IsUnit.unit_spec, ZMod.cast_natCast (dvd_mul_right N N)] at this
    rw [this, MulChar.mul_apply, MulChar.pow_apply' _ two_ne_zero]
  have e1 : ψ⁻¹ (p : ZMod N) * ψ (p : ZMod N) = 1 := by
    rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply hu']
  constructor
  · rw [hg' p hp fun n h1 => ?_]
    · linear_combination g.a p * e1
    have := g.eig p hp n h1
    rw [e, hn, hn n, Nat.cast_mul, map_mul, Eigenform.a]
    by_cases hpn : p ∣ n
    · obtain ⟨m, rfl⟩ := hpn
      rw [if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hp.pos] at this ⊢
      rw [hn, Nat.cast_mul, map_mul]
      linear_combination ψ⁻¹ (p : ZMod N) * (ψ⁻¹ (p : ZMod N) * ψ⁻¹ (m : ZMod N)) * this
    · rw [if_neg hpn] at this ⊢
      linear_combination ψ⁻¹ (p : ZMod N) * ψ⁻¹ (n : ZMod N) * this
  · rw [e]
    linear_combination χ (p : ZMod N) * (ψ⁻¹ (p : ZMod N) * ψ (p : ZMod N) + 1) * e1

private theorem eig_unique {k N p : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {f : CuspForm (Gamma1 N) (k : ℤ)} (hf : f ≠ 0)
    {a b : ℂ} (ha : IsEigAt k χ f p a) (hb : IsEigAt k χ f p b) : a = b := by
  by_contra h
  exact hf ((finDim N k).2 f fun n hn =>
    (mul_eq_zero.1 (show (a - b) * coef f n = 0 by linear_combination hb n hn - ha n hn)).resolve_left (sub_ne_zero.2 h))

private theorem level_zero_eq_maximal_compact {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) :
    K1 w 0 = GlobalTheory.LFun.KGL w (n := 2) := by
  ext g
  refine ⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩
  haveI : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact Subsingleton.elim _ _

private theorem lie_one (φ : TR.Sm ℚ 2) (h : ∀ v, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = 0) : TR.lie ℚ 2 (TR.oneL ℚ 2) φ = 0 := by
  classical
  have hX : TR.lie ℚ 2 (TR.oneL ℚ 2) = ∑ i, TR.lieS ℚ 2 i i 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [TR.lieS_apply, ← map_sum]
    exact congrArg _ (Matrix.sum_single_one (m := Fin 2) (α := TR.Rinf ℚ)).symm
  have h1 : ∀ i, TR.lieS ℚ 2 i i 1 = TR.Eop Rat.infinitePlace i i := fun i => by
    rw [TR.Eop_eq]
    congr 1
    funext v
    rw [Subsingleton.elim v Rat.infinitePlace]
    simp
  rw [hX, Fin.sum_univ_two, h1, h1]
  exact h _

private theorem ev_not_dvd {a : ℕ} (h : a ≠ 0) : ∀ᶠ w : Pl ℚ in Filter.cofinite, ¬ normV w ∣ a := by
  have h0 : Ideal.span {(a : 𝓞 ℚ)} ≠ 0 := by simpa using h
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  obtain ⟨c, rfl⟩ := not_not.1 hw
  refine Ideal.dvd_span_singleton.2 ?_
  rw [Nat.cast_mul, (places w).2.1]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
end

