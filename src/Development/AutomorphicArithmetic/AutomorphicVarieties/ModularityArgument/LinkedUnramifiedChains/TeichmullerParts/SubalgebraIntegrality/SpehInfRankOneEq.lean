module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0054
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0058
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0057
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0053
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0059
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0052
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0051
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0056
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1323
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0653
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DualIsConjOfIsCsd
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open UpperTheory.V.Af.Gu UpperTheory.V.Z.J.D GlobalTheory.DefiniteBC GlobalTheory.SmGL
open UpperTheory.V.Z.Mult (Cp At)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace SpehDualProof

open Matrix GlobalTheory.ContraPair

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

private def phiOp (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) : Module.End ℂ (Sm L a) :=
  act (.fin (PhiU a (Af L))) * act (.cpt (PhiK L a))

private theorem barK_barK (k : Kinf L a) : barK (barK k) = k := Subtype.ext (by
  ext i j : 1
  exact star_star _)

private theorem fin_cpt (k : GL (Fin a) (Af L)) (u : Kinf L a) :
    act (.cpt u) * act (.fin k) = act (.fin k) * act (Op.cpt u : Op L a) := by
  change rt L a _ * rt L a _ = rt L a _ * rt L a _
  rw [← map_mul, ← map_mul]
  exact congrArg _ (infGL_comm _ _)

private theorem phiOp_mul (o : Op L a) : phiOp L a * act (invTOp (conjOp o)) = act (thetaOp o) * phiOp L a := by
  cases o with
  | fin k =>
    simp only [phiOp, conjOp, invTOp, thetaOp]
    rw [mul_assoc, fin_cpt, ← mul_assoc, ← mul_assoc]
    congr 1
    change finRep L a _ * finRep L a _ = finRep L a _ * finRep L a _
    rw [← map_mul, ← map_mul]
    congr 1
    change _ = PhiU a (Af L) * _ * (PhiU a (Af L))⁻¹ * _
    rw [inv_mul_cancel_right]
    rfl
  | cpt k =>
    simp only [phiOp, conjOp, invTOp, thetaOp, barK_barK]
    rw [← mul_assoc, fin_cpt, mul_assoc, mul_assoc]
    congr 1
    change cptRep L a _ * cptRep L a _ = cptRep L a _ * cptRep L a _
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  | lie X =>
    simp only [phiOp, conjOp, invTOp, thetaOp]
    have h1 := GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits (PhiK L a)) (-(Matrix.of X)ᴴ)
    have h2 := lie_rt_fin (E := L) (toL (-(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ)))
      (PhiU a (Af L))
    have e : Unitary.toUnits (PhiK L a) = PhiU a (Cinf L) := Units.ext rfl
    have e2 : (Unitary.toUnits (PhiK L a)).val * (-(Matrix.of X)ᴴ) * ((Unitary.toUnits (PhiK L a))⁻¹).val =
        -(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ) := by
      rw [e, mul_neg, neg_mul]; rfl
    rw [e2] at h1
    rw [mul_assoc, ← mul_assoc (act (Op.lie _))]
    exact (congrArg (act (.fin (PhiU a (Af L))) * ·) h1).trans ((mul_assoc _ _ _).symm.trans
      (congrArg (· * _) h2.symm))

private theorem dualIsConj_of_isCsd {π : CuspSub L a} (h : Paired π π invTOp) (hc : π.IsCsd) : DualIsConj π := by
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨T, hT⟩ := hc
  let P : Module.End ℂ π.V := π.op (.fin (PhiU a (Af L))) * π.op (.cpt (PhiK L a))
  let Q : Module.End ℂ π.V := π.op (.cpt (PhiK L a)⁻¹) * π.op (.fin (PhiU a (Af L))⁻¹)
  have f1 : ∀ k k' : GL (Fin a) (Af L), k * k' = 1 → ∀ φ, π.op (.fin k) (π.op (.fin k') φ) = φ := fun k k' e φ =>
    Subtype.ext (by
      change (finRep L a k * finRep L a k') φ.1 = φ.1
      rw [← map_mul, e, map_one]; rfl)
  have f2 : ∀ k k' : Kinf L a, k * k' = 1 → ∀ φ, π.op (.cpt k) (π.op (.cpt k') φ) = φ := fun k k' e φ =>
    Subtype.ext (by
      change (cptRep L a k * cptRep L a k') φ.1 = φ.1
      rw [← map_mul, e, map_one]; rfl)
  let Pe : π.V ≃ₗ[ℂ] π.V := LinearEquiv.ofLinear P Q
    (LinearMap.ext fun φ => by simp [P, Q, f1, f2]) (LinearMap.ext fun φ => by simp [P, Q, f1, f2])
  let S := Pe.trans T
  have hS : ∀ o φ, S (π.op (invTOp (conjOp o)) φ) = π.op o (S φ) := fun o φ => by
    change T _ = π.op o (T _)
    rw [← hT]
    exact congrArg T (Subtype.ext (LinearMap.congr_fun (phiOp_mul o) φ.1))
  have hS' : ∀ o φ, S.symm (π.op o φ) = π.op (invTOp (conjOp o)) (S.symm φ) := fun o φ => by
    rw [LinearEquiv.symm_apply_eq, hS, LinearEquiv.apply_symm_apply]
  refine ⟨B.flip ∘ₗ S.symm.toLinearMap, fun φ h => ?_, fun ψ h => h1 ψ fun x => ?_, fun k φ ψ => ?_, fun k φ ψ => ?_,
    fun X φ ψ => ?_⟩
  · exact (map_eq_zero_iff _ S.symm.injective).1 (h2 _ h)
  · simpa using h (S x)
  · change B _ (S.symm _) = B _ (S.symm _)
    rw [hS']; exact h3 _ _ _
  · change B _ (S.symm _) = B _ (S.symm _)
    rw [hS']; exact h4 _ _ _
  · change B _ (S.symm _) + B _ (S.symm _) = 0
    rw [hS', add_comm]; exact h5 _ _ _

end SpehDualProof

private theorem ss_irr {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k} (h : IsIrr r) : IsSSRep r := fun M hM => by
  rcases h.2.2 M le_top hM with rfl | rfl
  · exact ⟨⊤, h.2.1, isCompl_bot_top⟩
  · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
    rw [(Submodule.mem_bot k).1 hv]
    simp

private theorem irr_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (e : RepIso r r') (h : IsIrr r) :
    IsIrr r' := by
  obtain ⟨P, hP⟩ := e
  refine ⟨h.1, fun _ _ _ => Submodule.mem_top, fun M _ hM => ?_⟩
  let T : (Fin n → k) ≃ₗ[k] (Fin n → k) := (Matrix.GeneralLinearGroup.toLin P).toLinearEquiv
  have hT : ∀ v, T v = (P : Matrix (Fin n) (Fin n) k).mulVec v := fun v => rfl
  have hi : Formalism.MainNotions.N.IsInv r (M.comap (T : (Fin n → k) →ₗ[k] (Fin n → k))) := fun g v hv => by
    have h1 := hM g _ hv
    have h2 : T ((r g : Matrix (Fin n) (Fin n) k).mulVec v) = (r' g : Matrix (Fin n) (Fin n) k).mulVec (T v) := by
      rw [hT, hT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP g]
      simp [Matrix.mul_assoc]
    show T _ ∈ M
    rw [h2]
    exact h1
  rcases h.2.2 _ le_top hi with h0 | h0
  · left
    refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
    have h1 : T.symm v ∈ M.comap (T : (Fin n → k) →ₗ[k] (Fin n → k)) := by simpa using hv
    rw [h0] at h1
    simpa using (Submodule.mem_bot k).1 h1
  · right
    refine (Submodule.eq_top_iff').2 fun v => ?_
    have h1 : T.symm v ∈ M.comap (T : (Fin n → k) →ₗ[k] (Fin n → k)) := by rw [h0]; trivial
    simpa using h1

private theorem iso_split {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (hE : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal)
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (r r' : G E Ω →* GL (Fin n) (Qbar l)) (hr : Continuous r) (hr' : Continuous r')
    (hs : IsSSRep r) (hs' : IsSSRep r')
    (hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ∃ B, FrobEig ι r w B ∧ FrobEig ι r' w B) : RepIso r r' := by
  have hc : ∀ g : G E Ω, (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
    intro g
    ext i
    have h1 : Continuous fun g : G E Ω => (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (GlobalTheory.LocBound.continuous_coeff_charpoly n i).comp (Units.continuous_val.comp (hr.comp continuous_inv))
    have h2 : Continuous fun g : G E Ω => (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (GlobalTheory.LocBound.continuous_coeff_charpoly n i).comp (Units.continuous_val.comp (hr'.comp continuous_inv))
    refine congrFun (GlobalTheory.Published.chebotarevDegreeOne'.eq_of_frob (Filter.eventually_cofinite.1 hw) h1 h2 ?_) g
    intro v hv hd A hA σ hσ
    obtain ⟨B, hB, hB'⟩ := (not_not.1 hv) (UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one E v (hE v) hd)
    have h := ((hB A hA).2 σ hσ).trans ((hB' A hA).2 σ hσ).symm
    have h' := Polynomial.map_injective ι.toRingHom ι.injective h
    simp only [h']
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' (fun g => by simpa using hc g⁻¹)
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩

private theorem speh_inf_rank_one_eq (m : Multiset ℂ) : GlobalTheory.DefiniteBC.spehInf 1 m = m := by
  simp [GlobalTheory.DefiniteBC.spehInf]

private theorem ev_away {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)

private theorem onePart (H : HypothesesH) (hLink : SatLink) {E : Type} [Field E] [NumberField E] [IsCMField E]
    (hE : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal)
    {n : ℕ} (hn : 1 ≤ n) (σ : Submodule ℂ (UA E n → ℂ)) (hσ : IsAutRepU σ) (hsum : ∑ _i : Fin 1, 1 * n = n)
    (P : Fin 1 → CuspSub E n) (ρ : Fin 1 → ∀ w : HeightOneSpectrum (𝓞 E), LocIrr w n)
    (m : Fin 1 → (E →+* ℂ) → Multiset ℂ) (τs : Fin 1 → ∀ w : HeightOneSpectrum (𝓞 E), LocIrr w (1 * n))
    (hP : GlobalTheory.BcSpeh.Parts σ (fun _ => n) (fun _ => 1) hsum P ρ m)
    (hS : ∀ i w, GlobalTheory.SmGL.IsUnitarisable (ρ i w).ρ ∧ GlobalTheory.SmGL.IsUnitarisable (τs i w).ρ ∧
      GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) 1 (τs i w).ρ)
    (hsplit : ∀ w, IsSplitAt w → IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd hsum w (τs · w))) :
    ∃ π : CuspSub E n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ At π σ ∧
      (∀ φ lam, HasWeightAt σ φ lam → π.HasInfChar φ (infOfWeight lam)) ∧ ∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B := by
  have hw : ∀ φ lam, HasWeightAt σ φ lam → (P 0).HasInfChar φ (infOfWeight lam) := fun φ lam h => by
    have e := hP.weight φ lam h
    rw [Fin.sum_univ_one, speh_inf_rank_one_eq] at e
    exact e ▸ hP.inf 0 φ
  refine ⟨P 0, (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, SpehDualProof.dualIsConj_of_isCsd (H.toClassicalTheorems.litN.aut.gk E _ (P 0)) (hP.csd 0), ?_, hw, fun w hu => ?_⟩
  · obtain ⟨lam, hl⟩ := _root_.GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU E _ hn σ hσ τ
    rw [CG.HasInfChar.infChar_eq (π := CG.mk (P 0)) (hw τ lam hl)]
    refine ⟨nodup_infOfWeight lam, fun z hz => ?_⟩
    rw [infOfWeight, Multiset.mem_map] at hz
    obtain ⟨j, -, rfl⟩ := hz
    exact ⟨lam.w j - (j : ℕ), by push_cast; ring⟩
  · filter_upwards [(hLink E _ (P 0)).2] with w ⟨B, hB⟩ hs
    have e : (fun i => τs i w) = fun _ => τs 0 w := funext fun i => by rw [Subsingleton.elim i 0]
    have key : ∀ f : Fin 1 → LocIrr w (1 * n), f = (fun _ => τs 0 w) →
        IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd hsum w f) →
        IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd hsum w fun _ => τs 0 w) := by
      rintro f rfl h
      exact h
    have hc := key _ e (hsplit w hs)
    exact ⟨ρ 0 w, B, UpperTheory.V.Z.Desc.irrComp E n σ hsum (P 0) w (ρ 0 w) (τs 0 w) (hP.loc 0 w) (hS 0 w).2.2 hc (ρ 0 w) (hP.loc 0 w),
      ((hLink E _ (P 0)).1 w _ (hP.loc 0 w) _).1 hB, hB⟩
  · obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1
      (GlobalTheory.SphBC.isSpherical_of_isUnramU E hE n σ hσ 1 _ _ hsum P ρ m τs hP hS hsplit w hu 0 (ρ 0 w) (hP.loc 0 w))
    obtain ⟨B, hB⟩ := (satLoc H.toClassicalTheorems E n w (ρ 0 w)).1 ⟨x, h0, GlobalTheory.LGrp.mem_fixed.1 hx⟩
    exact ⟨B, ((hLink E _ (P 0)).1 w _ (hP.loc 0 w) _).2 hB⟩

private theorem assemble (H : HypothesesH) (hB : GlobalTheory.BcSpeh.BcSpeh) (hFam : SumFam) (hHalf : Half) (hStr : Strings) (hUni : CompUnique)
    (hRec : RecTot) (hFrob : FrobTot) (hLink : SatLink) : BcOf := by
  intro _ E Ω _ _ _ _ _ _ hE l _ _ ι n hn π hπ R hRc hRi hR
  obtain ⟨c, a, d, hsum, P, ρ, m, σ, hP, hS, hsplit⟩ := hB E hE n hn π hπ
  have hc : 1 ≤ c := by
    rcases c with _ | c
    · simp at hsum; omega
    · omega
  have hint : ∀ i (k : Fin (d i)) τ, (m i τ).Nodup ∧ ∀ z ∈ m i τ, ∃ j : ℤ, z + (ex n (d i) k : ℂ) / 2 = j := fun i k τ => by
    obtain ⟨lam, hl⟩ := _root_.GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU E n hn π hπ τ
    exact (hStr n c d (m · τ) lam (hP.weight τ lam hl)).1 i k
  choose r₀ HT₀ h₀ hw₀ using fun i (k : Fin (d i)) =>
    hHalf E Ω l ι (a i) (hP.pos i).1 (P i) (hP.csd i) (ρ i) (hP.loc i) (m i) (hP.inf i) (ex n (d i) k) (hint i k)
  choose r₁ h₁ hi₁ using fun i => hFam E Ω l ι (d i) (hP.pos i).2 (fun _ => a i) (fun _ => (hP.pos i).1) (d i * a i) (by simp)
    (r₀ i) _ (HT₀ i) (h₀ i)
  obtain ⟨r, hr, hi⟩ := hFam E Ω l ι c hc (fun i => d i * a i) (fun i => Nat.mul_pos (hP.pos i).2 (hP.pos i).1) n hsum r₁ _ _ h₁
  have hpar : ∀ w, ParAt ι r w (totPar n d (ρ · w)) := hr.par
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧
      ∃ S : Fin c → Multiset ℂˣ, ∀ i, (CG.mk (P i)).HasSat w (S i) := by
    filter_upwards [ev_away (K := E) l, Filter.eventually_all.2 fun i => (hLink E _ (P i)).2] with w h1 h2
    exact ⟨h1, Classical.skolem.1 h2⟩
  have hRp : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ParAt ι R w (totPar n d (ρ · w)) := by
    filter_upwards [hR] with w hw hs
    let T : SmIrr (GL (Fin n) (w.adicCompletion E)) :=
      { V := _, ρ := locProd hsum w (σ · w), smooth := GlobalTheory.SmGL.isSmooth_parInd _ _, irred := (hsplit w hs).1 }
    exact ((locGlob_iff ι R w T).1 (hw hs T (hsplit w hs))).congr fun A h rc hrc =>
      (hRec E Ω n c a d hsum P w (ρ · w) (σ · w) hP.pos (hP.loc · w) (hS · w) T
        (hUni E n π hπ w hs _ _ _ _ (hsplit w hs) (hsplit w hs)) A h rc hrc).symm
  have hiso : RepIso R r := iso_split hE ι R r hRc hr.cont (ss_irr hRi) hr.ss (by
    filter_upwards [hev, hRp] with w ⟨hw, S, hS'⟩ hp hs
    have hSat : ∀ i, GlobalTheory.LFun.HasSatGL w (ρ i w).ρ (S i) := fun i => ((hLink E _ (P i)).1 w _ (hP.loc i w) _).1 (hS' i)
    exact ⟨_, hFrob E Ω l ι n c a d R hRc w hw (ρ · w) S hSat (hp hs), hFrob E Ω l ι n c a d r hr.cont w hw (ρ · w) S hSat (hpar w)⟩)
  have hirr : IsIrr r := irr_conj hiso hRi
  obtain ⟨hc1, hr1⟩ := hi hirr
  have hd1 : ∀ i, d i = 1 := fun i => (hi₁ i (hr1 i)).1
  clear hi hi₁ h₁ hr hpar hint hev hRp hiso hirr hr1 h₀ hw₀
  subst hc1
  obtain rfl : d = fun _ => 1 := funext hd1
  have ha : a = fun _ => n := funext fun i => by
    rw [Subsingleton.elim i 0]
    simpa using hsum
  subst ha
  exact onePart H hLink hE hn π hπ hsum P ρ m σ hP hS hsplit
