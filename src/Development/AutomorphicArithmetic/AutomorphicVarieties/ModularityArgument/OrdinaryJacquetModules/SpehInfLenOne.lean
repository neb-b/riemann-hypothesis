module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrdAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0051
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CharpolyEqProd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1475
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0233
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DualIsConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
open UpperTheory.V.Af.Gu GlobalTheory.DefiniteBC

noncomputable section

namespace SpehInfLenOneDualProof

open Matrix GlobalTheory.ContraPair

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

private def phiOp (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) : Module.End ℂ (Sm L a) :=
  act (.fin (PhiU a (Af L))) * act (.cpt (PhiK L a))

omit [NumberField L] [IsCMField L] in
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
  let Pe : π.V ≃ₗ[ℂ] π.V := LinearEquiv.ofLinearMap P Q
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

end SpehInfLenOneDualProof

private theorem ev_offL {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)

private theorem unram_ev {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {σ : Submodule ℂ (UA E n → ℂ)}
    (hσ : IsAutRepU σ) : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsUnramU σ w := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ.ne_bot
  let L : Subgroup (finU (E := E) (n := n)) :=
    { carrier := {k | RU E n k φ = φ}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at *
        rw [Subgroup.coe_mul, map_mul, mul_apply_eq_comp, hb, ha]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq] at *
        conv_lhs => rw [← ha]
        rw [← mul_apply_eq_comp, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, one_apply_eq_self] }
  have hLo : IsOpen (L : Set (finU (E := E) (n := n))) := (hσ.aut φ hφ).level
  filter_upwards [GlobalTheory.T.eventually_localIntegralPoints_mem_openSubgroup_definiteUnitary E n L hLo] with w hw
  exact ⟨φ, hφ, hφ0, fun x hx hxK => hw x hx hxK hx.1⟩

private theorem ss_irr {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k} (h : Af.IsIrr r) : IsSSRep r := fun M hM => by
  rcases h.2.2 M le_top hM with rfl | rfl
  · exact ⟨⊤, h.2.1, isCompl_bot_top⟩
  · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
    rw [(Submodule.mem_bot k).1 hv]
    simp

private theorem irr_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (e : Af.RepIso r r')
    (h : Af.IsIrr r) : Af.IsIrr r' := by
  obtain ⟨P, hP⟩ := e
  refine ⟨h.1, fun _ _ _ => Submodule.mem_top, fun M _ hM => ?_⟩
  let T : (Fin n → k) ≃ₗ[k] (Fin n → k) := (Matrix.GeneralLinearGroup.toLin P).toLinearEquiv
  have hT : ∀ v, T v = (P : Matrix (Fin n) (Fin n) k).mulVec v := fun v => rfl
  have hi : IsInv r (M.comap (T : (Fin n → k) →ₗ[k] (Fin n → k))) := fun g v hv => by
    have h1 := hM g _ hv
    change (r' g : Matrix (Fin n) (Fin n) k).mulVec (T v) ∈ M at h1
    change T _ ∈ M
    have e1 : (P : Matrix (Fin n) (Fin n) k) * (r g : Matrix (Fin n) (Fin n) k) =
        (r' g : Matrix (Fin n) (Fin n) k) * (P : Matrix (Fin n) (Fin n) k) := by
      have e2 : P * r g = r' g * P := by rw [hP g, inv_mul_cancel_right]
      exact congrArg Units.val e2
    rw [hT, Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec, ← hT]
    exact h1
  have hm : M = (M.comap (T : (Fin n → k) →ₗ[k] (Fin n → k))).map (T : (Fin n → k) →ₗ[k] (Fin n → k)) :=
    (Submodule.map_comap_eq_of_surjective T.surjective M).symm
  rcases h.2.2 _ le_top hi with h0 | h1
  · left
    rw [hm, h0, Submodule.map_bot]
  · right
    rw [hm, h1, Submodule.map_top, LinearMap.range_eq_top.2 T.surjective]

private theorem iso_deg_one {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) {n : ℕ} (r r' : G E Ω →* GL (Fin n) (Qbar l)) (hr : Continuous r) (hr' : Continuous r')
    (hs : IsSSRep r) (hs' : IsSSRep r')
    (hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, w.asIdeal.inertiaDeg ℤ = 1 →
      ∃ B, Af.FrobEig ι r w B ∧ Af.FrobEig ι r' w B) : Af.RepIso r r' := by
  have hc := UpperTheory.V.Af.Es.charpoly_eq_prod ι (I := Unit) (a := fun _ => n) r (fun _ => r') hr (fun _ => hr')
    (hw.mono fun w h hd => by
      obtain ⟨B, h1, h2⟩ := h hd
      exact ⟨fun _ => B, by simpa using h1, fun _ => h2⟩)
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' (fun g => by simpa using hc g)
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩

private theorem spehInf_len_one (m : Multiset ℂ) : GlobalTheory.DefiniteBC.spehInf 1 m = m := by
  simp [GlobalTheory.DefiniteBC.spehInf]

private theorem satTot_len_one {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (S : Fin 1 → Multiset ℂˣ) :
    satTot w (fun _ => 1) S = S 0 := by
  simp [satTot, GlobalTheory.WeilDeligne.qPow_zero]

private theorem one_part (PH : Af.HypothesesH) (hUni : CompUnique) {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (hn1 : 1 ≤ n)
    {π : Submodule ℂ (UA E n → ℂ)} (hπ : IsAutRepU π) {c : ℕ} {a d : Fin c → ℕ} (hn : ∑ i, d i * a i = n)
    {P : ∀ i, CuspSub E (a i)} {ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (a i)) (w.adicCompletion E))}
    {m : Fin c → (E →+* ℂ) → Multiset ℂ} (H : GlobalTheory.BcSpeh.Parts π a d hn P ρ m)
    {σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (d i * a i)) (w.adicCompletion E))}
    (hS : ∀ i w, IsSpeh (cl (ρ i w)) (d i) (σ i w).ρ)
    (hsplit : ∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd hn w (σ · w)))
    (hc : c = 1) (hd : ∀ i, d i = 1) {r : G E Ω →* GL (Fin n) (Qbar l)} (hr : IsSSRep r)
    (hF : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ S : Fin c → Multiset ℂˣ, (∀ i, (CG.mk (P i)).HasSat w (S i)) ∧
      Af.FrobEig ι r w (Af.algSat n (normV w) (satTot w d S))) :
    ∃ Q : CuspSub E n, (CG.mk Q).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj Q ∧ Af.AttC ι r Q ∧
      ∀ w, IsSplitAt w → ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion E)),
        IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → Q.IsLocComp w τ := by
  subst hc
  obtain rfl : d = fun _ => 1 := funext hd
  have hn' : a 0 = n := by simpa using hn
  obtain rfl : a = fun _ => n := funext fun i => by rw [Subsingleton.elim i 0, hn']
  have hw : ∀ φ lam, HasWeightAt π φ lam → (P 0).HasInfChar φ (infOfWeight lam) := fun φ lam h => by
    have e := H.weight φ lam h
    rw [Fin.sum_univ_one, spehInf_len_one] at e
    exact e ▸ H.inf 0 φ
  refine ⟨P 0, (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, SpehInfLenOneDualProof.dualIsConj_of_isCsd (PH.toClassicalTheorems.litN.aut.gk E _ (P 0)) (H.csd 0),
    ⟨hr, hF.mono fun w ⟨S, h1, h2⟩ => ⟨S 0, h1 0, satTot_len_one w S ▸ h2⟩⟩, fun w hsp τ hτ => ?_⟩
  · obtain ⟨lam, hl⟩ := _root_.GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU E _ hn1 π hπ τ
    rw [CG.HasInfChar.infChar_eq (π := CG.mk (P 0)) (hw τ lam hl)]
    refine ⟨nodup_infOfWeight lam, fun z hz => ?_⟩
    rw [infOfWeight, Multiset.mem_map] at hz
    obtain ⟨j, -, rfl⟩ := hz
    exact ⟨lam.w j - (j : ℕ), by push_cast; ring⟩
  · have e : (σ · w) = fun _ => σ 0 w := funext fun i => by rw [Subsingleton.elim i 0]
    have hcg : ∀ x y : (∀ _i : Fin 1, SmIrr (GL (Fin (1 * n)) (w.adicCompletion E))), x = y →
        IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd (N := fun _ : Fin 1 => 1 * n) hn w x) →
        IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd (N := fun _ : Fin 1 => 1 * n) hn w y) := by
      rintro x _ rfl h
      exact h
    have h0 := hcg _ _ e (hsplit w hsp)
    have hρ : IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (ρ 0 w).ρ :=
      UpperTheory.V.Z.Desc.irrComp E n π hn (P 0) w (ρ 0 w) (σ 0 w) (H.loc 0 w) (hS 0 w) h0 (ρ 0 w) (H.loc 0 w)
    exact (GlobalTheory.BCT.isLocComp_iff_equiv (H.loc 0 w) τ).2 (hUni E n π hπ w hsp _ _ _ _ hτ hρ)

private theorem assemble_link (H : Af.HypothesesH) (hFam : SumFam) (hHalf : Half) (hStr : Strings) (hUni : CompUnique) (hRec : RecTot)
    (hFrob : FrobTot) (hSat : Af.SatFrob) (hLoc : Af.SatLoc) (hLink : SatLink) : LinkU := by
  intro E Ω _ _ _ _ _ _ hE l _ _ ι n hn π hπ ρ' hρc hρi hρF
  obtain ⟨c, a, d, hsum, P, ρ, m, σ, hP, hS, hsplit⟩ :=
    GlobalTheory.BcSpeh.bcSpeh_of_baseChange (GlobalTheory.BaseChangeBridge.main H.litN.aut.bc H.litN.loc.bern)
      (GlobalTheory.SpehInfChar.discreteSpectrumGL_of_residual H.litN.aut.mw) E hE n hn π hπ
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
  have hss' : IsSSRep ρ' := ss_irr hρi
  have hagree : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, w.asIdeal.inertiaDeg ℤ = 1 →
      ∃ B, Af.FrobEig ι r w B ∧ Af.FrobEig ι ρ' w B := by
    filter_upwards [ev_offL (K := E) l, unram_ev hπ, hρF] with w hl hu hw hd
    have hsp := UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one E w (hE w) hd
    obtain ⟨τ, hτ⟩ := (GlobalTheory.SplitComp.exists_comp_and_unique E n π hπ w hsp).1
    obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.SphBC.isSpherical_of_isCompAlong_split hπ hsp τ.ρ hτ hu)
    obtain ⟨B, hB⟩ := (hLoc E n w τ).1 ⟨x, h0, GlobalTheory.LGrp.mem_fixed.1 hx⟩
    refine ⟨_, hSat E Ω l ι n r hr.cont w hl τ B hB fun A h rc hrc => ?_, hw hsp τ hτ B hB⟩
    exact (((Af.Gu.locGlob_iff ι r w τ).2 ((hpar w).congr (hRec E Ω n c a d hsum P w (ρ · w) (σ · w) hP.pos (hP.loc · w) (hS · w) τ
      (hUni E n π hπ w hsp _ _ _ _ hτ (hsplit w hsp))))) A h rc hrc).1 hl
  have hiso : Af.RepIso r ρ' := iso_deg_one ι r ρ' hr.cont hρc hr.ss hss' hagree
  have hir : Af.IsIrr r := irr_conj (Af.RepIso.symm' hiso) hρi
  refine one_part H hUni ι hn hπ hsum hP (fun i w => (hS i w).2.2) hsplit (hi hir).1 (fun i => (hi₁ i ((hi hir).2 i)).1) hss' ?_
  filter_upwards [ev_offL (K := E) l, Filter.eventually_all.2 fun i => (hLink E _ (P i)).2] with w h1 h2
  obtain ⟨S, hSs⟩ := Classical.skolem.1 h2
  exact ⟨S, hSs, Af.FrobEig.of_iso (hFrob E Ω l ι n c a d r hr.cont w h1 (ρ · w) S
    (fun i => ((hLink E _ (P i)).1 w _ (hP.loc i w) _).1 (hSs i)) (hpar w)) hiso⟩

theorem UpperTheory.V.Z.Ord.linkU :
    Af.HypothesesH → LinkU := fun H =>
  assemble_link H (UpperTheory.sum_family_of_reductions (UpperTheory.sum_two_of_hodge_tate H UpperTheory.galoisRep_direct_sum_away_from_places UpperTheory.sum_hodge_tate) UpperTheory.finiteSum_reduction)
    (UpperTheory.half_of_compatible_polarization H UpperTheory.eta_condition UpperTheory.twist_local_components_compatible (UpperTheory.compatible_polarization_of_link H (UpperTheory.V.Af.compatCsd H) (UpperTheory.satake_galois_compatibility_of_hecke_eigensystem H)))
    UpperTheory.speh_parameter_strings UpperTheory.building_component_uniqueness (UpperTheory.total_reciprocity H) (UpperTheory.total_frobenius_compatibility H) (UpperTheory.V.Af.satFrob H.toClassicalTheorems) (UpperTheory.V.Af.satLoc H.toClassicalTheorems)
    (UpperTheory.satake_galois_compatibility_of_hecke_eigensystem H)
