module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0032
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Ad0IrrMulVec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.CentChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RDual2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.ArthurClozelDescent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalTwists.Reduce
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.CentChar
public import GroundTheory.AutomorphicForms.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.AdAutQ
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Sd

private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

private theorem charEig_cyc_inv {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F)) (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) :
    CharEig ι (cycBar F Ω l)⁻¹ w (normV w : ℂ) := by
  intro A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h1 : cycZ F Ω l s = 1 := Units.ext (PadicInt.ext_of_toZModPow.mp fun n => by
      rw [cycZ_toZModPow_eq hw hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
      simp)
    rw [MonoidHom.inv_apply, cycBar, MonoidHom.comp_apply, h1, map_one, inv_one]
  · have h2 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
      change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
      rw [cycZ_of_isFrob hw hA hσ, map_natCast, map_natCast]
    rw [MonoidHom.inv_apply, map_inv, inv_inv, h2, map_natCast]

private theorem fin_scalar {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    finGL F 2 (locGL F 2 w (Matrix.GeneralLinearGroup.scalar (Fin 2) x)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (localIdele F w x) := by
  have h := GlobalTheory.CuspRep.finId_det_locGL w (Matrix.GeneralLinearGroup.scalar (Fin 1) x)
  rw [locGL, GlobalTheory.CuspRep.cornerGL_scalar] at h ⊢
  rw [finGL, GlobalTheory.CuspRep.cornerGL_scalar]
  congr 1
  exact (congrArg (finId F) (GlobalTheory.CuspRep.CG.det_oneByOne _)).symm.trans
    (h.trans (congrArg (localIdele F w) (GlobalTheory.CuspRep.CG.det_oneByOne _)))

private theorem cent (hP : UpperTheory.V.Af.Hypotheses₂) {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2)
    (hreg : π.IsRegAlg) (hs : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, π.HasSat w B) :
    ∃ ω : HChar F, (∀ w (α β : ℂˣ), π.HasSat w {α, β} → α * β = ω.val w) ∧ ∀ v, ∃ n : ℤ, TR.expo ω v = n := by
  obtain ⟨ω, hω, -⟩ := UpperTheory.V.Sd.Wc.centChar hP F π
  have hv : ∀ w (α β : ℂˣ), π.HasSat w {α, β} → α * β = ω.val w := fun w α β h => by
    obtain ⟨x, hx⟩ := GlobalTheory.LFun.HasSatGL.exists_vec h
    have hZ := (UpperTheory.V.Br.uOfSat F w _ _ x α β hx).2
    have h2 : π.locRep w (Matrix.GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) x = ((ω.val w : ℂˣ) : ℂ) • x := by
      refine Subtype.ext (Subtype.ext (funext fun g => ?_))
      change x.1.1 (g * finGL F 2 (locGL F 2 w _)) = _
      rw [fin_scalar, ← GlobalTheory.CuspRep.scalar_comm, hω _ _ x.2]
      rfl
    exact Units.ext (smul_left_injective ℂ hx.1 (hZ.symm.trans h2))
  refine ⟨ω, hv, fun v => ?_⟩
  have hiso : π.Iso (π.dual.twist ω) := by
    refine hP.smoR F 2 one_le_two _ _ ?_
    filter_upwards [hs, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified ω)] with w ⟨B, hB⟩ hu
    obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 hB.card
    have e : (({α, β} : Multiset ℂˣ).map (·⁻¹)).map (· * ω.val w) = {α, β} := by
      rw [← hv w α β hB, Multiset.pair_comm α β]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, inv_mul_cancel_left]
      rw [mul_comm α β, inv_mul_cancel_left]
      exact Multiset.pair_comm α β
    exact ⟨_, hB, e ▸ hB.dual.twist hu⟩
  obtain ⟨m, hm, -, hz⟩ := hreg v
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hm.1
  obtain ⟨i, hi⟩ := hz x (by simp)
  obtain ⟨j, hj⟩ := hz y (by simp)
  have h := congrArg Multiset.sum ((hiso.hasInfChar hm).unique (hm.dual.twist ω))
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
    Multiset.sum_singleton] at h
  refine ⟨i + j + 1, ?_⟩
  push_cast at hi hj ⊢
  linear_combination hi + hj - h / 2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.QuadOf
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Lit

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem norm_deg (w : HeightOneSpectrum (𝓞 E)) :
    normV w = normV (w.under (𝓞 F)) ^ w.asIdeal.inertiaDeg (𝓞 F) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 F)).isMaximal
  have hnorm : ∀ {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)),
      normV v = Ideal.absNorm v.asIdeal := by
    intro L _ _ v
    rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hnorm, hnorm]
  exact (Ideal.absNorm_pow_inertiaDeg (w.under (𝓞 F)).asIdeal w.asIdeal).symm

private theorem deg_sum (h2 : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F))
    (T : Finset (v.asIdeal.primesOver (𝓞 E))) : ∑ q ∈ T, q.1.inertiaDeg (𝓞 F) ≤ 2 := by
  have := v.isMaximal
  have : Fintype (v.asIdeal.primesOver (𝓞 E)) := (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).fintype
  rw [← h2, Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E,
    ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)]
  refine (Finset.sum_le_sum_of_subset T.subset_univ).trans (Finset.sum_le_sum fun q _ => ?_)
  have := q.2.1
  exact Nat.le_mul_of_pos_left _ (Ideal.ramificationIdx_pos _ _)

private theorem norm_split (h2 : Module.finrank F E = 2) {w w' : HeightOneSpectrum (𝓞 E)} (hne : w' ≠ w)
    (hu : w'.under (𝓞 F) = w.under (𝓞 F)) : normV w = normV (w.under (𝓞 F)) := by
  classical
  have := w.isPrime
  have := w'.isPrime
  have hu' : (w.under (𝓞 F)).asIdeal = w'.asIdeal.under (𝓞 F) := (congrArg HeightOneSpectrum.asIdeal hu).symm
  have hs := deg_sum h2 (w.under (𝓞 F)) {⟨w'.asIdeal, w'.isPrime, ⟨hu'⟩⟩, ⟨w.asIdeal, w.isPrime, ⟨rfl⟩⟩}
  rw [Finset.sum_pair fun h => hne (HeightOneSpectrum.ext (congrArg Subtype.val h))] at hs
  have h3 := w.asIdeal.inertiaDeg_pos (𝓞 F)
  have h4 := w'.asIdeal.inertiaDeg_pos (𝓞 F)
  rw [norm_deg (F := F) w, show w.asIdeal.inertiaDeg (𝓞 F) = 1 by dsimp only at hs; omega, pow_one]

private theorem gal_two (h2 : Module.finrank F E = 2) : ∃ σ : E ≃ₐ[F] E, σ ≠ 1 ∧ ∀ τ : E ≃ₐ[F] E, τ = 1 ∨ τ = σ := by
  have : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, hy, hy'⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  exact ⟨y, hy, fun τ => (em (τ = 1)).imp_right (hy' τ)⟩

end Places

section Main

variable {F E : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsTotallyReal E] [Algebra F E] {a : ℕ}

variable (F) in
private def Concl (π : TR.CuspSub E a) : Prop :=
  ((∀ (v v' : InfinitePlace E) (m : Multiset ℂ), v.comap (algebraMap F E) = v'.comap (algebraMap F E) →
      π.HasInfChar v m → π.HasInfChar v' m) ∧
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) →
      ∃ B, π.HasSat w B ∧ π.HasSat w' B) ∨
  ∃ P : TR.CuspSub F (2 * a),
    (∀ (v v' : InfinitePlace E) (m m' : Multiset ℂ), v ≠ v' → v.comap (algebraMap F E) = v'.comap (algebraMap F E) →
      π.HasInfChar v m → π.HasInfChar v' m' → P.HasInfChar (v.comap (algebraMap F E)) (m + m')) ∧
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      (∀ w' : HeightOneSpectrum (𝓞 E), w' ≠ w → w'.under (𝓞 F) = w.under (𝓞 F) →
        ∃ B B', π.HasSat w B ∧ π.HasSat w' B' ∧ P.HasSat (w.under (𝓞 F)) (B + B')) ∧
      (normV w = normV (w.under (𝓞 F)) ^ 2 → ∃ B B' : Multiset ℂˣ, π.HasSat w (B'.map (· ^ 2)) ∧
        B = B' + B'.map (fun b => -b) ∧ P.HasSat (w.under (𝓞 F)) B)

end Main
end

