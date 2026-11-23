module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsNondegenerateRightInvariantFormOfCompactQu
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.SplitComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.ContRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0005
public import GroundTheory.AutomorphicForms.AdelicGLn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.AfFin
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.afFin :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V) (U : Subgroup (UA L n)), IsLevel U → FiniteDimensional ℂ (AF R U) := by
  intro L _ _ _ n V _ _ _ R U hU
  obtain ⟨S, hS⟩ := GlobalTheory.T.definiteUnitary_classSet_finite L n (U.subgroupOf (finU (E := L) (n := n))) hU.2
  let T : AF R U →ₗ[ℂ] (S → V) :=
    { toFun := fun φ s => φ.1 s.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective T ((injective_iff_map_eq_zero T).2 fun φ h0 => ?_)
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hS g
  have hφ : IsAF R U φ.1 := φ.2
  have hz : φ.1 s = 0 := congrFun h0 ⟨s, hs⟩
  rw [hφ.level _ (Subgroup.mem_subgroupOf.1 hk), hφ.inf x hx, hφ.left γ hγ, hz, map_zero]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.AutProj
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

open GlobalTheory.DefU in
theorem UpperTheory.V.Z.Sym.Al.autProj :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (M : Submodule ℂ (GlobalTheory.DefU.autU L n)), FiniteDimensional ℂ M →
        ∃ (κ : Type) (_ : Fintype κ) (σ : κ → Submodule ℂ (UA L n → ℂ)) (P : κ → GlobalTheory.DefU.autU L n →ₗ[ℂ] GlobalTheory.DefU.autU L n),
          (∀ i, IsAutRepU (σ i)) ∧ (∀ i φ, (P i φ).1 ∈ σ i) ∧
          (∀ i x φ, P i (GlobalTheory.DefU.autRep L n x φ) = GlobalTheory.DefU.autRep L n x (P i φ)) ∧ ∀ φ ∈ M, ∑ i, P i φ = φ := by
  intro L _ _ _ n M hM
  obtain ⟨h1, h2, h3, h4⟩ := UpperTheory.unitary_adelic_t2_locallyCompact_secondCountable L n
  obtain ⟨C, hC, hcov⟩ := UpperTheory.exists_compact_fundamental_set_unitary L n
  obtain ⟨B, hdef, hinv⟩ := UpperTheory.exists_nondegenerate_right_invariant_form_of_compact_quotient (UA L n) (ratU L n) C hC hcov
  have hsum := UpperTheory.mem_iSup_automorphicReps_of_invariant_form L n B (fun φ h => hdef φ h.cont h.left)
    (fun x φ ψ h h' => hinv x φ ψ h.cont h.left h'.cont h'.left)
  have hi := Submodule.map_injective_of_injective (autU L n).injective_subtype
  obtain ⟨κ, _, U, P, hU, hP, hPe, hPs⟩ := UpperTheory.exists_equivariant_projections_of_sum_irreducible (UA L n) (autU L n) (autRep L n) (fun x => by
    have key : ∀ (Z : Submodule ℂ (autU L n)), (∀ σ, IsAutRepU σ → σ.comap (autU L n).subtype ≤ Z) → x ∈ Z := by
      intro Z hZ
      have hle : (⨆ σ : {σ : Submodule ℂ (UA L n → ℂ) // IsAutRepU σ}, σ.1) ≤ Z.map (autU L n).subtype :=
        iSup_le fun σ φ hφ => ⟨⟨φ, σ.2.aut φ hφ⟩, hZ σ.1 σ.2 hφ, rfl⟩
      obtain ⟨y, hy, e⟩ := hle (hsum x.1 x.2)
      exact Subtype.ext e ▸ hy
    refine key _ fun σ hσ => ?_
    have hm : (σ.comap (autU L n).subtype).map (autU L n).subtype = σ := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 hσ.aut
    refine le_iSup_of_le ⟨σ.comap (autU L n).subtype, fun h => hσ.ne_bot ?_, fun g u hu => hσ.stable g u.1 hu,
      fun N hN hst => ?_⟩ le_rfl
    · rw [← hm, h, Submodule.map_bot]
    · refine (hσ.irred (N.map (autU L n).subtype) (hm ▸ Submodule.map_mono hN) ?_).imp
        (fun h => hi (h.trans (Submodule.map_bot _).symm)) fun h => hi (h.trans hm.symm)
      rintro g _ ⟨u, hu, rfl⟩
      exact ⟨_, hst g u hu, rfl⟩) M hM
  refine ⟨κ, inferInstance, fun i => (U i).map (autU L n).subtype, P, fun i => ⟨?_, ?_, ?_, fun N hN hst => ?_⟩,
    fun i φ => ⟨_, hP i φ, rfl⟩, hPe, hPs⟩
  · rintro _ ⟨u, -, rfl⟩
    exact u.2
  · rintro g _ ⟨u, hu, rfl⟩
    exact ⟨_, (hU i).2.1 g u hu, rfl⟩
  · exact fun h => (hU i).1 (hi (h.trans (Submodule.map_bot _).symm))
  · have hm : (N.comap (autU L n).subtype).map (autU L n).subtype = N := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 (hN.trans (Submodule.map_subtype_le _ _))
    rcases (hU i).2.2 (N.comap (autU L n).subtype) (fun u hu => by
      obtain ⟨w, hw, e⟩ := hN hu
      exact Subtype.ext e ▸ hw) (fun g u hu => hst g u.1 hu) with h | h
    · left; rw [← hm, h, Submodule.map_bot]
    · right; rw [← hm, h]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.CoefAut
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem exists_finPart {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} :
    ∃ p : UA L n → finU (E := L) (n := n), Continuous p ∧ p 1 = 1 ∧ ∀ x, (p x : UA L n)⁻¹ * x ∈ infU L n := by
  have hfin : Continuous (finGL L n) :=
    Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
      (continuous_const.prodMk continuous_id : Continuous fun x : Af L => ((0, x) : InfiniteAdeleRing L × Af L))))
  refine ⟨fun x => ⟨⟨finGL L n (Matrix.GeneralLinearGroup.map (pFin L) x.1),
    GlobalTheory.SplitPts.finGL_mem_UA _ fun u => GlobalTheory.SplitPts.comp_eq x u⟩, MonoidHom.mem_ker.2 (pInf_finGL _)⟩,
    Continuous.subtype_mk (Continuous.subtype_mk
      (hfin.comp (GlobalTheory.DefU.continuous_map_pFin.comp continuous_subtype_val)) _) _, ?_, fun x => ?_⟩
  · refine Subtype.ext (Subtype.ext ?_)
    change finGL L n (Matrix.GeneralLinearGroup.map (pFin L) 1) = 1
    rw [map_one, map_one]
  · change Matrix.GeneralLinearGroup.map (pFin L)
      ((finGL L n (Matrix.GeneralLinearGroup.map (pFin L) x.1))⁻¹ * x.1) = 1
    rw [map_mul, map_inv, pFin_finGL, inv_mul_cancel]

private theorem continuous_infC {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} :
    Continuous (infC L n) := by
  have hτ : ∀ τ : L →+* ℂ, Continuous (cEmb (E := L) (n := n) τ) := fun τ => by
    have h1 : Continuous (coord (E := L) τ) := by
      unfold coord
      split_ifs
      · exact continuous_apply _
      · exact Complex.continuous_conj.comp (continuous_apply _)
    have h2 : Continuous (pInf L) := continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
        ((continuous_apply w).comp continuous_fst)
    exact (Continuous.units_map _ (continuous_id.matrix_map h1)).comp
      ((Continuous.units_map _ (continuous_id.matrix_map h2)).comp continuous_subtype_val)
  exact continuous_pi fun v => hτ v.embedding

private theorem infC_of_fin {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {k : UA L n}
    (hk : k ∈ finU (E := L) (n := n)) : infC L n k = 1 :=
  funext fun v => by
    change Matrix.GeneralLinearGroup.map (coord v.embedding) (cInf k) = 1
    rw [MonoidHom.mem_ker.1 hk, map_one]

theorem UpperTheory.V.Z.Sym.Al.coefAut :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V), ContCoef R → ∀ U, IsLevel U → ∀ φ : UA L n → V, IsAF R U φ →
        ∀ f : V →ₗ[ℂ] ℂ, IsAutFormU (f ∘ φ) := by
  intro L _ _ _ n V _ _ _ R hR U hU φ hφ f
  obtain ⟨p, hp, hp1, hp2⟩ := exists_finPart (L := L) (n := n)
  have hU1 : {x : finU (E := L) (n := n) | (x : UA L n) ∈ U} ∈ nhds (1 : finU (E := L) (n := n)) := hU.2.mem_nhds U.one_mem

  have hsm : ∀ᶠ z in nhds (1 : UA L n), ∀ g, φ (g * z) = R (infC L n z⁻¹) (φ g) := by
    have hUp : {x : finU (E := L) (n := n) | (x : UA L n) ∈ U} ∈ nhds (p 1) := by rwa [hp1]
    filter_upwards [(hp.tendsto 1).eventually hUp] with z hz g
    have h1 := hφ.inf _ (hp2 z) (g * (p z : UA L n))
    rw [hφ.level _ hz g, mul_assoc, mul_inv_cancel_left] at h1
    have e : infC L n ((p z : UA L n)⁻¹ * z)⁻¹ = infC L n z⁻¹ := by
      rw [mul_inv_rev, inv_inv, map_mul, infC_of_fin (p z).2, mul_one]
    rw [h1, e]
  refine ⟨?_, fun γ hγ g => congrArg f (hφ.left γ hγ g), ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g0 => ?_
    have hc : Continuous fun g : UA L n => f (R (infC L n (g⁻¹ * g0)) (φ g0)) :=
      (hR (φ g0) f).comp (continuous_infC.comp (continuous_inv.mul continuous_const))
    refine hc.continuousAt.congr ?_
    have ht : Filter.Tendsto (fun g : UA L n => g0⁻¹ * g) (nhds g0) (nhds 1) := by
      have : Continuous fun g : UA L n => g0⁻¹ * g := continuous_const.mul continuous_id
      simpa only [inv_mul_cancel] using this.tendsto g0
    filter_upwards [ht.eventually hsm] with g hg
    have e := hg g0
    rw [mul_inv_cancel_left, mul_inv_rev, inv_inv] at e
    rw [Function.comp_apply, e]
  · refine isOpen_stab_of_mem_nhds ((RU L n).comp (finU (E := L) (n := n)).subtype) _ ?_
    filter_upwards [hU1] with k hk
    funext g
    exact congrArg f (hφ.level _ hk g)
  · let C : Module.Dual ℂ V →ₗ[ℂ] (UA L n → ℂ) :=
      { toFun := fun μ g => μ (φ g)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range C) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨f ∘ₗ R (infC L n (k : UA L n)⁻¹), ?_⟩
    funext g
    change f (R (infC L n (k : UA L n)⁻¹) (φ g)) = f (φ (g * k))
    rw [hφ.inf _ k.2 g]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.CompEx
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.compEx :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], Unr L → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA L n → ℂ), IsAutRepU π → ∀ w, IsSplitAt w → ∃ τ, Comp π w τ := by
  intro H L _ _ _ unr n hn π hπ w hw
  obtain ⟨P, hb⟩ := UpperTheory.BaseChangeIdentities.splitComp
    (GlobalTheory.BcSpeh.bcSpeh_of_baseChange (GlobalTheory.BaseChangeBridge.main H.aut.bc H.loc.bern)
      (GlobalTheory.SpehInfChar.discreteSpectrumGL_of_residual H.aut.mw)) L unr n hn π hπ
  exact ⟨P w hw, hb w hw⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.ContE
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.contE :
    ∀ (I : Type) [Fintype I] (j : ℕ), (FiniteDimensional ℂ (Wt.VG I j) ∧ ContCoef (Wt.repG I j)) ∧
        (FiniteDimensional ℂ (Wt.VD I j) ∧ ∀ e : I → ℤ, ContCoef (repE j e)) := by
  intro I _ j
  obtain ⟨hG, hD⟩ := Wt.contRep I
  have hB : ∀ S : I → Bool, FiniteDimensional ℂ (Wt.Bi 3 (Wt.dg j S)) := fun S => Wt.finMH _ 3 _
  refine ⟨⟨Module.Finite.pi, fun x f => hG j x f⟩, ⟨Wt.finMH I 2 (fun _ => j), fun e x f => ?_⟩⟩
  have key : (fun g => f ((repE j e g) x)) = fun g =>
      ((∏ v, Matrix.GeneralLinearGroup.det (g v) ^ e v : ℂˣ) : ℂ) * f ((Wt.repD I j 0 g) x) := by
    funext g
    simp [repE, Wt.repD_apply, Wt.detE]
  rw [key]
  refine Continuous.mul (Units.continuous_val.comp ?_) (hD j 0 x f)
  exact continuous_finsetProd _ fun v _ =>
    ((Matrix.GeneralLinearGroup.continuous_det).comp (continuous_apply v)).zpow (e v)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.EigTS
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.eigTS :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (V : Type) [AddCommGroup V] [Module ℂ V] (φ : UA L 2 → V) (w : Plc L) (W : Sig.Lev (Kw w)) (ψ : Fin 2 → (Kw w)ˣ →* ℂˣ), EigT φ w W ψ → EigS φ w W (ψ 0 / ψ 1) := by
  intro L _ _ _ V _ _ φ w W ψ h t ht
  have hd : Sig.SDom ![t, t⁻¹] := by
    intro i j hij
    have h0 : valuation (Kw w) (t : Kw w) ≠ 0 := by simp
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    exact ht.trans ((one_lt_inv₀ (zero_lt_iff.2 h0)).2 ht)
  have e : Dict.expo ![ψ 0 / ψ 1, 1] ![t, t⁻¹] = Dict.expo ψ ![t, t⁻¹] := by
    simp [Dict.expo, torusChar, Fin.prod_univ_two, div_eq_mul_inv]
  rw [e]; exact h _ hd
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.ExistsOpen
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

namespace UpperTheory.V.Z.Sym.Al.CofinalityAlt

open GroundTheory.Automorphic.AdelicGLn GroundTheory.Automorphic.GLnLocal

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

private noncomputable abbrev fp (x : UA L n) : GL (Fin n) (Af L) :=
  Matrix.GeneralLinearGroup.map (pFin L) (x : GA L n)

private theorem cont_fp : Continuous (fp : UA L n → GL (Fin n) (Af L)) :=
  continuous_mapFin.comp continuous_subtype_val

private theorem e_apply (w : Plc L) (x : UA L n) : finiteRestrictedEquiv L n (fp x) w = cLoc w x := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [finiteRestrictedEquiv_apply]
  rfl

private theorem cont_cLoc (w : Plc L) : Continuous (cLoc w : UA L n → GL (Fin n) (w.adicCompletion L)) := by
  have e : (cLoc w : UA L n → GL (Fin n) (w.adicCompletion L)) =
      fun x => finiteRestrictedEquiv L n (fp x) w := funext fun x => (e_apply w x).symm
  rw [e]
  exact (RestrictedProduct.continuous_eval w).comp ((finiteRestrictedEquiv L n).continuous.comp cont_fp)

private theorem snd_eq (x : UA L n) : (prodEquiv L n (x : GA L n)).2 = fp x :=
  Units.ext (Matrix.ext fun a b => by rw [prodEquiv_apply_snd]; rfl)

private theorem fst_eq (x : finU (E := L) (n := n)) : (prodEquiv L n ((x : UA L n) : GA L n)).1 = 1 := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [prodEquiv_apply_fst]
  have key := congrArg (fun g : GL (Fin n) (Cinf L) => g.1 a b) (MonoidHom.mem_ker.1 x.2)
  refine (infEq L).symm.injective (key.trans ?_)
  by_cases h : a = b
  · subst h
    simp
  · simp [Matrix.one_apply_ne h]

private theorem mem_Kall {x : UA L n} :
    x ∈ Kall L n ↔ x ∈ finU (E := L) (n := n) ∧ ∀ w : Plc L, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n) := by
  simp [Kall, Subgroup.mem_inf, Subgroup.mem_iInf]

private theorem exists_open {U : Subgroup (UA L n)} (hU : IsOpen {x : finU (E := L) (n := n) | (x : UA L n) ∈ U}) :
    ∃ O : Set (GL (Fin n) (Af L)), IsOpen O ∧ 1 ∈ O ∧ ∀ x : finU (E := L) (n := n), fp x.1 ∈ O → (x : UA L n) ∈ U := by
  obtain ⟨A, hA, eA⟩ := isOpen_induced_iff.1 hU
  obtain ⟨B, hB, rfl⟩ := isOpen_induced_iff.1 hA
  let c : GL (Fin n) (Af L) → GA L n := fun k => (prodEquiv L n).symm (1, k)
  have hc : Continuous c := (prodEquiv L n).symm.continuous.comp (continuous_const.prodMk continuous_id)
  have hx : ∀ x : finU (E := L) (n := n), c (fp x.1) = ((x : UA L n) : GA L n) := fun x => by
    change (prodEquiv L n).symm _ = _
    rw [← fst_eq x, ← snd_eq]
    exact (prodEquiv L n).symm_apply_apply _
  have hmem : ∀ x : finU (E := L) (n := n), (x : UA L n) ∈ U ↔ ((x : UA L n) : GA L n) ∈ B := fun x =>
    (Set.ext_iff.1 eA x).symm
  refine ⟨c ⁻¹' B, hB.preimage hc, ?_, fun x hx' => ?_⟩
  · have h := hx 1
    have h1 : fp ((1 : finU (E := L) (n := n)) : UA L n) = 1 := map_one _
    rw [h1] at h
    rw [Set.mem_preimage, h]
    exact (hmem 1).1 (one_mem U)
  · rw [Set.mem_preimage, hx] at hx'
    exact (hmem x).2 hx'

private theorem nbhd {O : Set (GL (Fin n) (Af L))} (hO : IsOpen O) (h1 : 1 ∈ O) :
    ∃ T : Finset (Plc L), ∀ g : GL (Fin n) (Af L), g ∈ integralFiniteGL L n →
      (∀ v ∈ T, finiteRestrictedEquiv L n g v = 1) → g ∈ O := by
  let e := finiteRestrictedEquiv L n
  let s := RestrictedProduct.structureMap (fun v : Plc L => GL (Fin n) (v.adicCompletion L))
    (fun v => (integralGL (v.adicCompletion L) n : Set (GL (Fin n) (v.adicCompletion L)))) Filter.cofinite
  have hs : Continuous fun a => e.symm (s a) :=
    e.symm.continuous.comp RestrictedProduct.isEmbedding_structureMap.continuous
  have hone : e.symm (s fun v => ⟨1, one_mem _⟩) = 1 := by
    have : s (fun v => ⟨1, one_mem _⟩) = 1 := rfl
    rw [this, map_one]
  obtain ⟨T, u, hu, hT⟩ := isOpen_pi_iff.1 (hO.preimage hs) (fun v => ⟨1, one_mem _⟩)
    (by rw [Set.mem_preimage, hone]; exact h1)
  refine ⟨T, fun g hg hgT => ?_⟩
  have hint := (mem_integralFiniteGL_iff_forall L n).1 hg
  have hg' : e.symm (s fun v => ⟨e g v, hint v⟩) = g := by
    have : s (fun v => ⟨e g v, hint v⟩) = e g := by
      ext v
      rfl
    rw [this, e.symm_apply_apply]
  rw [← hg']
  refine hT fun v hv => ?_
  have : (⟨e g v, hint v⟩ : (integralGL (v.adicCompletion L) n : Set (GL (Fin n) (v.adicCompletion L)))) = ⟨1, one_mem _⟩ :=
    Subtype.ext (hgT v hv)
  rw [this]
  exact (hu v hv).2

private theorem fp_mem {x : UA L n} (hx : ∀ w : Plc L, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n)) :
    fp x ∈ integralFiniteGL L n :=
  (mem_integralFiniteGL_iff_forall L n).2 fun v => by
    rw [e_apply]
    exact GlobalTheory.StabInt.mem_integralGL_of_mem_KGL (hx v)

private theorem clause1 (U : Subgroup (UA L n)) (hU : IsOpen {x : finU (E := L) (n := n) | (x : UA L n) ∈ U}) :
    ∃ T : Finset (Plc L), Kall L n ⊓ ⨅ w ∈ T, away n w ≤ U := by
  obtain ⟨O, hO, h1, hOU⟩ := exists_open hU
  obtain ⟨T, hT⟩ := nbhd hO h1
  refine ⟨T, fun x hx => ?_⟩
  obtain ⟨hK, hA⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨hf, hi⟩ := mem_Kall.1 hK
  refine hOU ⟨x, hf⟩ (hT _ (fp_mem hi) fun v hv => ?_)
  rw [e_apply]
  have h := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hA v) hv
  exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h v) rfl)

private theorem clause2 : IsLevel (Kall L n) := by
  refine ⟨le_rfl, ?_⟩
  have e : {x : finU (E := L) (n := n) | (x : UA L n) ∈ Kall L n} =
      (fun x : finU (E := L) (n := n) => fp x.1) ⁻¹' (integralFiniteGL L n : Set (GL (Fin n) (Af L))) := by
    ext x
    refine ⟨fun h => fp_mem (mem_Kall.1 h).2, fun h => mem_Kall.2 ⟨x.2, fun w => ?_⟩⟩
    have h' := (mem_integralFiniteGL_iff_forall L n).1 h w
    rw [e_apply] at h'
    exact GlobalTheory.StabInt.mem_KGL_of_mem_integralGL h'
  rw [e]
  exact (isOpen_integralFiniteGL L n).preimage (cont_fp.comp continuous_subtype_val)

private theorem clause3 (U : Subgroup (UA L n)) (hU : IsLevel U) (S : Finset (Plc L))
    (V : ∀ w : Plc L, Sig.Lev (Kw w)) : IsLevel (lev U S V) := by
  refine ⟨inf_le_left.trans hU.1, ?_⟩
  have e : {x : finU (E := L) (n := n) | (x : UA L n) ∈ lev U S V} = {x : finU (E := L) (n := n) | (x : UA L n) ∈ U} ∩
      ⋂ w ∈ S, (fun x : finU (E := L) (n := n) => cLoc w (x : UA L n)) ⁻¹' ((V w).J n : Set (GL (Fin n) (Kw w))) := by
    ext x
    simp [lev, Subgroup.mem_inf, Subgroup.mem_iInf]
  rw [e]
  exact hU.2.inter (isOpen_biInter_finset fun w _ =>
    ((Sig.finFacts _ (V w)).2.2.2.2.2 n).2.1.preimage ((cont_cLoc w).comp continuous_subtype_val))

private theorem clause4 (U : Subgroup (UA L n)) (hU : IsLevel U) :
    ∀ᶠ w : Plc L in Filter.cofinite, locU n w ⊓ Kall L n ≤ U := by
  obtain ⟨T, hT⟩ := clause1 U hU.2
  have hfin : ∀ t : Plc L, {w : Plc L | w.under (𝓞 (Lp L)) = t.under (𝓞 (Lp L))}.Finite := fun t =>
    ((IsDedekindDomain.primesOver_finite (t.under (𝓞 (Lp L))).asIdeal (𝓞 L)).preimage
      (fun a _ b _ h => HeightOneSpectrum.ext h)).subset
      fun w hw => ⟨w.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hw).symm⟩⟩
  refine Filter.eventually_cofinite.2 ((T.finite_toSet.biUnion fun t _ => hfin t).subset fun w hw => ?_)
  by_contra hn
  refine hw fun x hx => hT ?_
  obtain ⟨hl, hK⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨hK, Subgroup.mem_iInf.2 fun t => Subgroup.mem_iInf.2 fun ht =>
    Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_⟩
  refine Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hl).2 u) fun huw => hn ?_
  exact Set.mem_biUnion (Finset.mem_coe.2 ht) (huw.symm.trans hu)

end UpperTheory.V.Z.Sym.Al.CofinalityAlt

open UpperTheory.V.Z.Sym.Al.CofinalityAlt in
theorem UpperTheory.V.Z.Sym.Al.cof :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ),
        (∀ U : Subgroup (UA L n), IsOpen {x : finU (E := L) (n := n) | (x : UA L n) ∈ U} → ∃ T : Finset (Plc L), Kall L n ⊓ ⨅ w ∈ T, away n w ≤ U) ∧
        IsLevel (Kall L n) ∧ (∀ U : Subgroup (UA L n), IsLevel U → ∀ S V, IsLevel (lev U S V)) ∧
        ∀ U : Subgroup (UA L n), IsLevel U → ∀ᶠ w : Plc L in Filter.cofinite, locU n w ⊓ Kall L n ≤ U := by
  intro L _ _ _ n
  exact ⟨clause1, clause2, clause3, clause4⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.LocSph
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem det_mem_Uo (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {g : Matrix.GeneralLinearGroup Unit k} (hg : g ∈ KO k Unit) :
    Matrix.GeneralLinearGroup.det g ∈ UpperTheory.V.Hi.Uo k := by
  obtain ⟨h, rfl⟩ := hg
  show valuation k ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) h) : kˣ) : k) = 1
  rw [Matrix.GeneralLinearGroup.map_det]
  exact (Valuation.integer.integers (valuation k)).valuation_unit _

theorem UpperTheory.V.Z.Sym.Al.locSph :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, ∀ u ∈ Hi.Uo k, ψ i u = 1) → ∃ v, v ≠ 0 ∧ ∀ u ∈ KO k (Fin n), prinSeries ψ u v = v := by
  intro k _ _ _ _ n ψ hψ
  have key : ∀ g : Levi k (fun _ : Fin n => Unit), (∀ a, g a ∈ KO k Unit) →
      (MonoidHom.comp (ofChar (torusChar ψ)) (leviTorus k (Fin n)).symm.toMonoidHom) g (1 : ℂ) = 1 := by
    intro g hg
    have hs : (leviTorus k (Fin n)).symm g = fun i => Matrix.GeneralLinearGroup.det (g i) := rfl
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ofChar_apply, hs, torusChar_apply]
    rw [Finset.prod_eq_one fun i _ => hψ i _ (det_mem_Uo k (hg i))]
    simp
  obtain ⟨f, hf, h1⟩ := GlobalTheory.SatInd.exists_fixed_apply_one (points (Fin n)) key
  refine ⟨f, ?_, fun u hu => GlobalTheory.LGrp.mem_fixed.mp hf u hu⟩
  rintro rfl
  simp at h1
end

