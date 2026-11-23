module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DualIsConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinrankInvFunBranch
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0653
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HalfOfCompatiblePolarization
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open UpperTheory.V.Af UpperTheory.V.Af.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace HalfDualProof

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

end HalfDualProof

theorem UpperTheory.half_of_compatible_polarization :
    HypothesesH → Eta → TwistLoc → CompatPol → Half := by
  intro H hEta hTw hC E Ω _ _ _ _ _ _ l _ ι a ha P hP ρ hρ m hm e he
  obtain ⟨ξ, mξ, hξ, hN⟩ := hEta E (e + a - 1)
  set s : ℝ := ((e + a - 1 : ℤ) : ℝ) / 2 with hs
  have hsC : (s : ℂ) = (e : ℂ) / 2 + ((a : ℂ) - 1) / 2 := by
    rw [hs]; push_cast; ring
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s
  have hinf : ∀ τ, (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).infChar τ = (m τ).map (· + (s : ℂ)) := fun τ => by
    have h1 := (hm τ).twist (GlobalTheory.HeckeGal.Model.absPow E s)
    rw [(InfType.expo_of_infType E _).2.1 s hν τ] at h1
    exact CG.HasInfChar.infChar_eq (π := CG.mk _) h1
  have hreg : (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [hinf]
    refine ⟨(he τ).1.map (add_left_injective _), fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨j, hj⟩ := (he τ).2 y hy
    exact ⟨j, by rw [hsC, ← hj]; ring⟩
  have hd : GlobalTheory.ContraPair.DualIsConj ((P.twist (GlobalTheory.HeckeGal.Model.absPow E s)).twist ξ) := by
    rw [← CuspSub.twist_mul]
    exact Cq.csdTwist E a P 1 _ ((GlobalTheory.ContraPair.dualIsConjBy_one P).2
      (HalfDualProof.dualIsConj_of_isCsd (H.litN.aut.gk E a P) hP)) (by rw [hN, inv_one])
  choose σ hσ hcl using fun w => hTw E a P s w (ρ w) (hρ w)
  obtain ⟨r, HT, hr, hHT⟩ := hC E Ω l ι a ha _ _ ξ mξ hreg (GlobalTheory.HeightCounting.Blocks.isPolarized_twist_absPow hP s) hξ hd σ hσ
  refine ⟨r, HT, ⟨hr.cont, hr.ss, hr.ht, fun w => (hr.par w).congr fun A h rc hrc => ?_⟩, fun τ => ?_⟩
  · obtain ⟨_, _, _, -, L⟩ := hrc
    rw [← L.nu_eq]
    refine congrArg rc ?_
    change (cl (σ w)).nu _ = _
    rw [hcl, IrrGL.nu_nu]
    congr 1
    rw [hsC]; push_cast; ring
  · rw [hHT, hinf, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply, hsC]; ring

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HasWeightAtOfTensorDualIntertwiner
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.hasWeightAt_of_tensor_dual_intertwiner :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (I : Type) [Finite I] (φ : I → E →+* ℂ), (Function.Injective fun i => InfinitePlace.mk (φ i)) → ∀ (lam : I → DomWeight n) (σ : Submodule ℂ (UA E n → ℂ)) (Φ : Module.Dual ℂ (⨂[ℂ] i, nablaSq ℂ n (lam i)) →ₗ[ℂ] (UA E n → ℂ)), Φ ≠ 0 → (∀ ℓ, Φ ℓ ∈ σ) → (∀ ℓ, ∀ x ∈ infU E n, RU E n x (Φ ℓ) = Φ (ℓ ∘ₗ PiTensorProduct.map fun i => GlobalTheory.Branching.sqRep ℂ n (lam i) (cEmb (φ i) x⁻¹))) → ∀ i, HasWeightAt σ (φ i) (lam i).dual := by
  intro E _ _ _ n hn I _ φ hφ lam σ Φ hΦ hσ heq y
  obtain ⟨F, hF0, hF⟩ := UpperTheory.exists_factor_dual_embedding_of_ne_zero_tensor I (fun i => nablaSq ℂ n (lam i)) _ Φ hΦ y
  obtain ⟨e, he⟩ := (_root_.GlobalTheory.OneFunctional.iso_irr_comp_conjU n hn (lam y)).symm.trans (_root_.GlobalTheory.ConjDual.iso_conj_dual n (lam y))
  obtain ⟨u, hu⟩ := GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n (φ y)
  refine ⟨GlobalTheory.DefU.isIrreducible_sqRep n _, (Φ ∘ₗ F) ∘ₗ e.toLinearMap, fun h0 => hF0 ?_, fun v => hσ _, fun x v => ?_⟩
  · apply LinearMap.ext
    intro m
    obtain ⟨v, rfl⟩ := e.surjective m
    exact LinearMap.congr_fun h0 v
  · have hx : x.1 ∈ infU E n := GlobalTheory.DefU.embU_le_infU _ x.2
    have hT : ∀ i, i ≠ y → GlobalTheory.Branching.sqRep ℂ n (lam i) (cEmb (φ i) x.1⁻¹) = LinearMap.id := by
      intro i hi
      have h1 := (Subgroup.mem_inf.1 x.2).2
      rw [Subgroup.mem_iInf] at h1
      have h2 := h1 (φ i)
      rw [Subgroup.mem_iInf] at h2
      have h3 : cEmb (φ i) x.1 = 1 := h2 fun h => hi (hφ h)
      rw [map_inv, h3, inv_one, map_one]
      rfl
    change Φ (F (e (GlobalTheory.Branching.sqRep ℂ n (lam y).dual (cEmb (φ y) x.1) v))) = RU E n x.1 (Φ (F (e v)))
    rw [heq _ _ hx, hF _ hT, map_inv, ← hu x]
    congr 2
    rw [← map_inv]
    exact he (u x) v
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeEigenvalueBasicProperties
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem algSat_injective (n q : ℕ) (hq : q ≠ 0) (B B' : Multiset ℂˣ)
    (h : UpperTheory.V.Af.algSat n q B = UpperTheory.V.Af.algSat n q B') : B = B' := by
  unfold UpperTheory.V.Af.algSat at h
  have hc : ((((q : ℝ) ^ (((n : ℝ) - 1) / 2)) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (q : ℝ) ^ (((n : ℝ) - 1) / 2) :=
      Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hq) _
    exact_mod_cast this.ne'
  have h1 := Multiset.map_injective (mul_right_injective₀ hc) h
  have h2 : ∀ s : Multiset ℂˣ, (do let a ← s; pure (a : ℂ)) =
      Multiset.map (fun a : ℂˣ => (a : ℂ)) s := fun s => Multiset.bind_singleton _ _
  rw [h2, h2] at h1
  exact Multiset.map_injective Units.val_injective h1

theorem UpperTheory.hecke_eigenvalue_basic_properties :
    UpperTheory.V.Af.Sol.EigBasic := by
  intro F Ω _ _ _ _ _ l _ ι v
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  refine ⟨?_, ?_, ?_⟩
  · intro δ δ' z z' hz hz' A' hA'
    obtain ⟨hi, hf⟩ := hz A' hA'
    obtain ⟨hi', hf'⟩ := hz' A' hA'
    refine ⟨fun s hs => ?_, fun τ hτ => ?_⟩
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hi s hs, hi' s hs, inv_one, mul_one]
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_mul, Units.val_inv_eq_inv_val,
        map_inv₀, hf τ hτ, hf' τ hτ]
      push_cast
      rfl
  · intro δ z z' hz hz'
    apply Units.ext
    rw [← (hz A hA).2 σ hσ, ← (hz' A hA).2 σ hσ]
  · intro n r B B' hB hB'
    have e1 := (hB A hA).2 σ hσ
    have e2 := (hB' A hA).2 σ hσ
    rw [e1] at e2
    have e3 := congrArg Polynomial.roots e2
    rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at e3
    have hq : Formalism.ConjugateSelfDual.normV v ≠ 0 := by
      unfold Formalism.ConjugateSelfDual.normV
      exact Nat.card_pos.ne'
    exact algSat_injective n _ hq B B' e3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HodgeTateWeightsOfLocalGlobal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem norm_hom {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : ‖σ x‖ = ‖(x : PadicAlgCl l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq K.val K.val.injective]
  rfl


open Formalism.BasicNotions.Loc in
private theorem ex_emb {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (hj : GlobalTheory.Pst.Induces Bw) (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1)
    (hτ : GlobalTheory.Pst.IsInduced Bw τ τ') :
    ∃ j : W.Emb l w, j.1.comp (algebraMap F (w.adicCompletion F)) = τ := by
  have e : w = GlobalTheory.EvExtend.placeOf τ := by
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    rw [GlobalTheory.EvExtend.mem_placeOf, hτ]
    have h1 := norm_hom (LL'.1.val.comp τ') ⟨Bw.j (algebraMap F Ω x), Bw.j_E x⟩
    refine ((hj.valuation_lt_one_iff _).symm.trans (h x)).symm.trans ?_
    exact iff_of_eq (congrArg (· < 1) h1.symm)
  subst e
  obtain ⟨j, hc, hx, -⟩ := GlobalTheory.EvExtend.exists_ext τ
  exact ⟨⟨j, hc⟩, RingHom.ext hx⟩

theorem UpperTheory.hodge_tate_weights_of_local_global :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (ι : Qbar l ≃+* ℂ) (n : ℕ) (A : ValuationSubring Ω) (w : Plc L) (h : IsPlaceOver A w) (r : G L Ω →* GL (Fin n) (Qbar l)) (HT : (L →+* Qbar l) → Multiset ℤ) (τ : SmIrr (GLw n w)) (lam : Wt L l n), Af.HasHT r HT → Af.LocGlob ι r w τ → (∀ j : W.Emb l w, (HT (j.1.comp (algebraMap L _))).map (fun k : ℤ => (k : ℂ)) = (infOfWeight (lam (j.1.comp (algebraMap L _))).dual).map fun z => ((n : ℂ) - 1) / 2 - z) → AtL ι h (r.comp (Dec (F := L) A).subtype) lam τ := by
  intro l _ L Ω _ _ _ _ _ ι n A w h r HT τ lam hHT hLG hw _ _ _ _ rc hrc hab O _ _ _ Bw hj
  obtain ⟨h1, h2⟩ := hHT w A h O Bw hj
  refine ⟨h1, fun t LL' τ' hτ => ?_, fun s => ?_⟩
  · obtain ⟨j, rfl⟩ := ex_emb h Bw hj t LL' τ' hτ
    have e : HT (j.1.comp (algebraMap L _)) =
        Finset.univ.val.map fun i => htW lam i (j.1.comp (algebraMap L _)) := by
      refine Multiset.map_injective (f := fun k : ℤ => (k : ℂ)) Int.cast_injective ?_
      rw [hw j]
      simp only [infOfWeight, Multiset.map_map]
      refine Multiset.map_congr rfl fun i _ => ?_
      simp only [htW, lowW, Function.comp_apply, DomWeight.dual]
      push_cast
      ring
    have h3 := h2 _ LL' τ' hτ
    rw [e] at h3
    exact h3
  · exact ((hLG A h rc hrc).2 O Bw hj).2 (Or.inr hab) s
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InjectiveInfinitePlaceOfEmbAtSplitPlaces
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem w_under {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  have h1 := s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)
  have h2 := s.hA v x
  exact h1.symm.trans h2

private theorem mem_iff {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] {w : Plc L} (j : W.Emb l w) (x : 𝓞 L) :
    x ∈ w.asIdeal ↔ ‖j.1 (algebraMap L _ (x : L))‖ < 1 := by
  have h : w.asIdeal ≤ (GlobalTheory.EvExtend.placeOf (j.1.comp (algebraMap L _))).asIdeal := fun y hy => by
    rw [GlobalTheory.EvExtend.mem_placeOf]
    have h1 : Valued.v (algebraMap L (w.adicCompletion L) (y : L)) < 1 := by
      rw [ReciprocityTheory.Aut.adic_valued_algebraMap]
      exact (w.valuation_lt_one_iff_mem (K := L) y).2 hy
    have h2 := (j.2.tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one h1)
    rw [map_zero] at h2
    refine tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 (h2.congr fun n => ?_)
    exact map_pow j.1 _ n
  rw [w.isMaximal.eq_of_le (GlobalTheory.EvExtend.placeOf _).isPrime.ne_top h, GlobalTheory.EvExtend.mem_placeOf]
  rfl

private theorem not_stable {L : Type} [Field L] [NumberField L] [IsCMField L] {w : Plc L} (hw : IsSplitAt w)
    (h : ∀ x, IsCMField.ringOfIntegersComplexConj L x ∈ w.asIdeal → x ∈ w.asIdeal) : False := by
  obtain ⟨u, hu, hu'⟩ := hw
  refine hu (HeightOneSpectrum.ext (u.isMaximal.eq_of_le w.isPrime.ne_top fun x hx => ?_))
  obtain ⟨y, hy⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff L (x * IsCMField.ringOfIntegersComplexConj L x)).1 (by
    rw [map_mul, mul_comm]
    congr 1
    exact RingOfIntegers.ext (IsCMField.complexConj_apply_apply L x))
  have h1 : y ∈ (u.under (𝓞 (Lp L))).asIdeal := by
    change algebraMap _ (𝓞 L) y ∈ u.asIdeal
    rw [hy]
    exact Ideal.mul_mem_right _ _ hx
  rw [hu'] at h1
  change algebraMap _ (𝓞 L) y ∈ w.asIdeal at h1
  rw [hy] at h1
  exact (w.isPrime.mem_or_mem h1).elim id (h x)

theorem UpperTheory.injective_infinitePlace_of_emb_at_split_places :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V : s.Lev) (ι : Qbar l ≃+* ℂ), Function.Injective fun y : Emb l (fun v : V.frame.Vl => s.w v.1) => InfinitePlace.mk (ι.toRingHom.comp y.res) := by
  intro l _ L Ω _ _ _ _ _ _ s V ι
  rintro ⟨v, j⟩ ⟨v', j'⟩ h
  have h' : (∀ x : L, j.1 (algebraMap L _ x) = j'.1 (algebraMap L _ x)) ∨
      ∀ x : L, j.1 (algebraMap L _ (IsCMField.complexConj L x)) = j'.1 (algebraMap L _ x) := by
    refine (InfinitePlace.mk_eq_iff.1 h).imp (fun e x => ι.injective (RingHom.congr_fun e x)) fun e x => ι.injective ?_
    exact (IsCMField.complexEmbedding_complexConj L (ι.toRingHom.comp (j.1.comp (algebraMap L _))) x).trans
      (RingHom.congr_fun e x)
  have hv : v = v' := by
    apply Subtype.ext
    rw [← w_under s v.1, ← w_under s v'.1]
    ext x
    change algebraMap _ (𝓞 L) x ∈ (s.w v.1).asIdeal ↔ algebraMap _ (𝓞 L) x ∈ (s.w v'.1).asIdeal
    rw [mem_iff j, mem_iff j']
    rcases h' with e | e
    · rw [e]
    · rw [← e]
      have : IsCMField.complexConj L ((algebraMap _ (𝓞 L) x : 𝓞 L) : L) = ((algebraMap _ (𝓞 L) x : 𝓞 L) : L) :=
        IsCMField.complexConj_apply_eq_self L (x : Lp L)
      rw [this]
  subst hv
  rcases h' with e | e
  · have : j = j' := Subtype.ext (DFunLike.coe_injective
      ((HeightOneSpectrum.denseRange_algebraMap L (s.w v.1)).equalizer j.2 j'.2 (funext e)))
    rw [this]
  · refine (not_stable (UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω (s.A v.1) v.1 (s.hA _) (s.split _ (Or.inl v.2)) _ (w_under s _)) fun x hx => ?_).elim
    rw [mem_iff j] at hx
    rw [mem_iff j', ← e]
    exact hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IrreducibleCase
section
open UpperTheory.V.Af UpperTheory.V.Af.Gu
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefiniteBC

private theorem spehInf_one' (m : Multiset ℂ) : spehInf 1 m = m := by
  simp [spehInf]

private theorem satTot_one {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (S : Fin 1 → Multiset ℂˣ) :
    satTot w (fun _ => 1) S = S 0 := by
  simp [satTot, GlobalTheory.WeilDeligne.qPow_zero]

theorem UpperTheory.irreducible_case :
    HypothesesH → IrrCase := by
  intro PH E Ω _ _ _ _ _ _ l _ ι n hn1 π hπ c a d hn P ρ m H hc hd r hr hF
  subst hc
  obtain rfl : d = fun _ => 1 := funext hd
  have hn' : a 0 = n := by simpa using hn
  subst hn'
  have hw : ∀ φ lam, HasWeightAt π φ lam → (P 0).HasInfChar φ (infOfWeight lam) := fun φ lam h => by
    have e := H.weight φ lam h
    rw [Fin.sum_univ_one, spehInf_one'] at e
    exact e ▸ H.inf 0 φ
  refine ⟨P 0, (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, (GlobalTheory.ContraPair.dualIsConjBy_one (P 0)).1 (GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E _ (P 0) 1 (by simpa only [inv_one, CuspSub.twist_one] using PH.toClassicalTheorems.litN.aut.gk E _ (P 0)) ((GlobalTheory.GalOfCusp.isConjDualBy_one (P 0)).2 (H.csd 0))),
    ⟨hr, hF.mono fun w ⟨S, h1, h2⟩ => ⟨S 0, h1 0, satTot_one w S ▸ h2⟩⟩, hw⟩
  obtain ⟨lam, hl⟩ := _root_.GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU E _ hn1 π hπ τ
  rw [CG.HasInfChar.infChar_eq (π := CG.mk (P 0)) (hw τ lam hl)]
  refine ⟨nodup_infOfWeight lam, fun z hz => ?_⟩
  rw [infOfWeight, Multiset.mem_map] at hz
  obtain ⟨j, -, rfl⟩ := hz
  exact ⟨lam.w j - (j : ℕ), by push_cast; ring⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsoSumOfInjectiveEquivariantFamily
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.isoSum_of_injective_equivariant_family :
    ∀ (H M N : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (ρ : Representation ℂ H M) (ρ' : Representation ℂ H N) (Y : Submodule ℂ M) (Z : Submodule ℂ N) (τ : SmIrr H) (I : Type) [Finite I] (φ : I → M →ₗ[ℂ] N), IsoSum ρ' Z τ → (∀ g, ∀ y ∈ Y, ρ g y ∈ Y) → (∀ i, ∀ y ∈ Y, φ i y ∈ Z) → (∀ i g, ∀ y ∈ Y, φ i (ρ g y) = ρ' g (φ i y)) → (∀ y ∈ Y, (∀ i, φ i y = 0) → y = 0) → IsoSum ρ Y τ := by
  intro H M N _ _ _ _ _ _ _ ρ ρ' Y Z τ I _ φ hZ hY hφ he hinj
  classical
  let := Fintype.ofFinite I
  let π : Representation ℂ H Y := (⟨Y, fun g v hv => hY g v hv⟩ : Subrepresentation ρ).toRepresentation
  let P : Representation ℂ H (I → N) :=
    { toFun := fun g => (ρ' g).compLeft I
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  let j : Y →ₗ[ℂ] (I → N) := LinearMap.pi fun i => φ i ∘ₗ Y.subtype
  have hj : Function.Injective j := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    exact Subtype.ext (hinj y y.2 fun i => congrFun hy i)
  have hs : ∀ i g x, LinearMap.single ℂ (fun _ : I => N) i (ρ' g x) = P g (LinearMap.single ℂ (fun _ : I => N) i x) := by
    intro i g x
    funext k
    change (Pi.single i (ρ' g x) : I → N) k = ρ' g ((Pi.single i x : I → N) k)
    by_cases h : k = i
    · subst h; simp
    · simp [h]
  have hsing : ∀ i, ∀ z ∈ Z, LinearMap.single ℂ (fun _ : I => N) i z ∈
      ⨆ f : {f : τ.V →ₗ[ℂ] (I → N) // ∀ g v, f (τ.ρ g v) = P g (f v)}, LinearMap.range f.1 := by
    intro i z hz
    refine Submodule.iSup_induction _ (motive := fun z => LinearMap.single ℂ (fun _ : I => N) i z ∈ _) (hZ hz) ?_ ?_ ?_
    · rintro f _ ⟨s, rfl⟩
      exact Submodule.mem_iSup_of_mem ⟨LinearMap.single ℂ (fun _ : I => N) i ∘ₗ f.1, fun g v => by
        rw [LinearMap.comp_apply, f.2.1, hs]; rfl⟩ ⟨s, rfl⟩
    · rw [map_zero]; exact zero_mem _
    · intro a b ha hb
      rw [map_add]; exact add_mem ha hb
  have key := UpperTheory.V.PiLin.iso_sub τ.ρ π P τ.irred j hj (fun g y => funext fun i => he i g y y.2) (fun y => by
    rw [← Finset.univ_sum_single (j y)]
    exact Submodule.sum_mem _ fun i _ => hsing i _ (hφ i y y.2))
  intro y hy
  refine Submodule.iSup_induction _ (motive := fun z : Y => (z : M) ∈ _) (key ⟨y, hy⟩) ?_ ?_ ?_
  · rintro f _ ⟨s, rfl⟩
    refine Submodule.mem_iSup_of_mem ⟨Y.subtype ∘ₗ f.1, fun g v => ?_, ?_⟩ ⟨s, rfl⟩
    · exact congrArg Subtype.val (f.2 g v)
    · rintro _ ⟨v, rfl⟩; exact (f.1 v).2
  · exact zero_mem _
  · intro a b ha hb
    exact add_mem ha hb
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PolarizedOfCyclicConjugates
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem cyc_cont (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  (Continuous.units_map _ (show Continuous (fun x : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) from
    (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ F Ω l)
end

