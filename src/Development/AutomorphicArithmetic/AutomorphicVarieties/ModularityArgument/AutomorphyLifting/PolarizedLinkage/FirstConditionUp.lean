module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.CompatCsdOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.QuadraticCharpolySplitting.QuadFamSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.Bundle0001

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter UpperTheory.V.Af.Bc

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win

private theorem unlocked_of_potentially {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {r : G F Ω →* GL (Fin n) (Qbar l)} {v : HeightOneSpectrum (𝓞 F)} (h : PotUnl r v) : Unl1 r v := fun A hA =>
  (h A hA).imp fun _ k => ⟨k.1, fun i j e => k.2 i j 1 le_rfl (by simpa only [pow_one] using e)⟩

private theorem keeps_of_pot (hFL : FlagLaws) {K M Ω : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [CharZero Ω]
    [IsAlgClosure ℚ Ω] [Algebra K Ω] [Algebra K M] [Algebra M Ω] [IsScalarTower K M Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    (r : G ℚ Ω →* GL (Fin n) (Qbar l))
    (hp : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → PotUnl r v) :
    Keeps (r.comp (resG ℚ K Ω)) M := by
  intro w hw _
  have hv : ((l : ℕ) : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal := by
    simpa [HeightOneSpectrum.under, Ideal.mem_comap] using hw
  have h := (((hFL ℚ Ω l n r).2.2.2 M).2.2 w hw).1 (hp _ hv)
  exact unlocked_of_potentially h

private theorem step (hFL : FlagLaws) (hUD : AUpDown) (hP : HypothesesH) (hR : RowT) (K K' Ω : Type) [Field K] [NumberField K] [IsCMField K]
    [Field K'] [NumberField K'] [IsCMField K'] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω] [Algebra K' Ω]
    (hK : Module.finrank ℚ K = 2) (hK' : Module.finrank ℚ K' = 2) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (hn : 1 ≤ n)
    (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (hp : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → PotUnl r v)
    (hc : Continuous r) (hA : IsAutomorphicOverImagQuad ι r)
    (θ : G ℚ Ω →* (Qbar l)ˣ) (hθ : IsAlgChar ι θ) (hd : DualTw r θ) (hI : IneAb r) (hF : Flagged r)
    (hi : IsIrr (r.comp ((resG ℚ K Ω).range ⊓ (resG ℚ K' Ω).range).subtype))
    (hW : WitA ι (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω))) :
    WitA ι (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K' Ω →* G ℚ Ω)) := by
  obtain ⟨M, _, _, _, iK, iK', iM, tK, tK', gK, gK', hs, hs', hM, hM'⟩ := UpperTheory.V.Z.Bc.biQuad K K' Ω hK hK'
  have closure_over (L : Type) [Field L] [CharZero L] [Algebra L Ω] : IsAlgClosure L Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
  have := closure_over K
  have := closure_over K'
  have := closure_over M
  have exists_conj : ∃ c : G ℚ Ω, IsConjEl c := by
    let j : Ω →ₐ[ℚ] ℂ := _root_.IsAlgClosed.lift
    let : Algebra Ω ℂ := j.toRingHom.toAlgebra
    have : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
    let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
    exact ⟨τ.restrictNormal Ω, algebraMap Ω ℂ, τ.restrictNormal_commutes Ω⟩
  obtain ⟨c, hcc⟩ := exists_conj
  have he : (r.comp (resG ℚ K Ω)).comp (resG K M Ω) = (r.comp (resG ℚ K' Ω)).comp (resG K' M Ω) :=
    MonoidHom.ext fun s => rfl
  have irr_of_range {Δ Δ' : Type} [Group Δ] [Group Δ']
      (f : Δ →* G ℚ Ω) (f' : Δ' →* G ℚ Ω) (h : ∀ s, ∃ t, f' t = f s)
      (H : IsIrr (r.comp f)) : IsIrr (r.comp f') := by
    refine ⟨H.1, fun _ _ _ => trivial, fun W hW hI => H.2.2 W hW fun s v hv => ?_⟩
    obtain ⟨t, ht⟩ := h s
    simpa only [MonoidHom.comp_apply, ht] using hI t v hv
  have hiM : IsIrr ((r.comp (resG ℚ K Ω)).comp (resG K M Ω)) := by
    refine irr_of_range _ ((resG ℚ K Ω).comp (resG K M Ω)) ?_ hi
    rintro ⟨s, ⟨t, rfl⟩, h2⟩
    obtain ⟨u, rfl⟩ := (hM t).2 h2
    exact ⟨u, rfl⟩
  have hiM' : IsIrr ((r.comp (resG ℚ K' Ω)).comp (resG K' M Ω)) := he ▸ hiM
  have hiK : IsIrr (r.comp (resG ℚ K Ω)) :=
    irr_of_range ((resG ℚ K Ω).comp (resG K M Ω)) (resG ℚ K Ω) (fun s => ⟨resG K M Ω s, rfl⟩) hiM
  have hiK' : IsIrr (r.comp (resG ℚ K' Ω)) :=
    irr_of_range ((resG ℚ K' Ω).comp (resG K' M Ω)) (resG ℚ K' Ω) (fun s => ⟨resG K' M Ω s, rfl⟩) hiM'
  have exists_pairing (F : Type) [Field F] [CharZero F] [Algebra F Ω] :
      ∃ P, IsPairing c (r.comp (resG ℚ F Ω)) (θ.comp (resG ℚ F Ω)) P := by
    obtain ⟨J, hJ⟩ := hd
    refine ⟨J * r c⁻¹, fun s s' h => ?_⟩
    have h' : resG ℚ F Ω s' = c * resG ℚ F Ω s * c⁻¹ := h
    have e : r c⁻¹ * r (resG ℚ F Ω s') = r (resG ℚ F Ω s) * r c⁻¹ := by
      rw [h', ← map_mul, ← map_mul]
      congr 1
      group
    have e' : (r c⁻¹).val * (r (resG ℚ F Ω s')).val = (r (resG ℚ F Ω s)).val * (r c⁻¹).val :=
      congrArg Units.val e
    have hp := hJ (resG ℚ F Ω s)
    simp only [MonoidHom.comp_apply]
    rw [Units.val_mul, ← Matrix.smul_mul, ← hp]
    simp only [Matrix.mul_assoc, e']
  obtain ⟨P, hPa⟩ := exists_pairing K
  obtain ⟨P', hPa'⟩ := exists_pairing K'
  have pol : Sol.Pol ι (r.comp (resG ℚ K Ω)) :=
    ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      θ, c, P, hθ, UpperTheory.V.Ws.auSign θ, hcc, hPa⟩
  have pol' : Sol.Pol ι (r.comp (resG ℚ K' Ω)) :=
    ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      θ, c, P', hθ, UpperTheory.V.Ws.auSign θ, hcc, hPa'⟩
  have up := (hUD hP hR K M Ω hs l ι n hn (r.comp (resG ℚ K Ω)) (hc.comp (continuous_restrictScalarsHom ℚ K Ω)) hiM pol
    (hA hc K hK hiK) (((hFL ℚ Ω l n r).2.2.2 K).2.1 hF)).1 hW
  rw [he] at up
  exact (hUD hP hR K' M Ω hs' l ι n hn (r.comp (resG ℚ K' Ω)) (hc.comp (continuous_restrictScalarsHom ℚ K' Ω)) hiM' pol'
    (hA hc K' hK' hiK') (((hFL ℚ Ω l n r).2.2.2 K').2.1 hF)).2 (((hFL ℚ Ω l n r).2.2.2 K').1 hI)
    (keeps_of_pot hFL r hp) up

end UpperTheory.V.Z.Win
