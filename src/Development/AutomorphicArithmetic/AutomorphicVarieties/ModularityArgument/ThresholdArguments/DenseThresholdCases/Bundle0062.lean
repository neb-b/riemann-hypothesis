module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphyUnramifiedCoefficients
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0058
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWitApi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.AutNewformW
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.SpehInfRankOneEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.SpehInfLenOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealAway
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0048
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0040
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.UnitaryTorusDescent.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.UnitCard
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0047
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0061
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0060

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphyU3OfEndoscopy
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V hiding autCsd_iso
open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V
theorem UpperTheory.GalN.V.modOfEnd'_alt {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
    {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {g₁ : G ℚ Ω}
    {B : ValuationSubring Ω} {ι : Qbar l ≃+* ℂ} (h : _root_.UpperTheory.V.Z.Win.Dn.AutEnd2A c D.η D.Ψ D.cc g₁ B e ι)
    (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] (r : G ℚ Ω →* GG (m := 3) (R := A))
    (h1 : OrdPt l D.η D.Ψ D.cc g₁ B r) (h2 : TypeII D.η (UnitaryThreeInertia.push A.val r)) (h3 : ∀ g ∈ D.η.ker, (r g).mat 1 1 = 1)
    (W' : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)) (h4 : ∀ g ∈ D.η.ker, (W' g).val = corner (UnitaryThreeInertia.push A.val r g).mat)
    (h5 : (W' D.cc).val.trace = 0) (W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)) (hi : Af.RepIso W' W) : _root_.UpperTheory.V.Z.Win.Dn.IsModularA D ι W := by
  obtain ⟨⟨f, hf⟩, hw⟩ := h A r h1 h2 h3 W' h4 h5
  refine ⟨⟨f, ?_⟩, hw.weak_admissible_iso hi⟩
  obtain ⟨g, hg⟩ := hi
  let χ := cycBar ℚ Ω l ^ (-(e : ℤ))
  have htw : ∀ s, Af.tw W χ s = g * Af.tw W' χ s * g⁻¹ := by
    intro s
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Af.tw_val, Af.tw_val, hg, Units.val_mul, Units.val_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  change f.Att ι (Af.tw W χ)
  refine ⟨?_, hf.2.mono fun w hw A' hA' => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩
  · let E : (Fin 2 → Qbar l) ≃ₗ[Qbar l] (Fin 2 → Qbar l) :=
      Matrix.toLin'OfInv (Units.mul_inv g) (Units.inv_mul g)
    have hE (v : Fin 2 → Qbar l) : E v = (↑g⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).mulVec v := rfl
    have hintertwine (s : G ℚ Ω) (v : Fin 2 → Qbar l) :
        E ((Af.tw W χ s).val.mulVec v) = (Af.tw W' χ s).val.mulVec (E v) := by
      rw [hE, hE, htw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
      congr 2
      group
    intro V hV
    obtain ⟨V', hV', hcompl⟩ := hf.1 (V.map E.toLinearMap) (by
      rintro s _ ⟨v, hv, rfl⟩
      exact ⟨_, hV s v hv, hintertwine s v⟩)
    refine ⟨V'.comap E.toLinearMap, fun s v hv => ?_, ?_⟩
    · show E _ ∈ V'
      rw [hintertwine]
      exact hV' s _ hv
    · have hcompl' : IsCompl ((V.map E.toLinearMap).comap E.toLinearMap) (V'.comap E.toLinearMap) :=
        (Submodule.orderIsoMapComap E).symm.isCompl hcompl
      rwa [Submodule.comap_map_eq_of_injective E.injective] at hcompl'
  · rw [htw, (hw A' hA').1 s hs, mul_one, mul_inv_cancel]
  · rw [← (hw A' hA').2 σ hσ, htw, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
      Matrix.charpoly_units_conj]
theorem UpperTheory.V.Pr.automorphyUnramified_of_locPrints_kisin_gdEnd :
    Loc.LocalPublishedTheorems → _root_.UpperTheory.V.Pr.GdEndAlt → _root_.UpperTheory.V.Aut.AutomorphyUnramifiedCoefficientsAlt := by
  intro hL H Ω _ _ _ K _ _ _ _ l _ c N _ e ψ D _ ι
  obtain ⟨B, hB, -, -, -, hmem, -⟩ := dat_loc D
  obtain ⟨g₁, hM, hfin, h3, h2⟩ := H Ω K l c N e ψ D ι B hB
  have hA : FinA D g₁ := finA_of_end hL D g₁ hM B hmem hfin
  refine ⟨g₁, hM, hA, fun U S ξ r hr hp hI => ?_, fun U S ξ r hp hII h11 W hW => ?_⟩
  · obtain ⟨A, _, _, t, r', ho, ht⟩ := exists_ordPt_of_point hL D g₁ hM U S hA B hmem ξ r hp
    have hl : ∀ s ∈ D.η.ker, (UnitaryThreeInertia.push A.val r' s).left = tor _ t * (r s).left * (tor _ t)⁻¹ := fun s hs => by
      have hright : (r s).right = 1 := (hr s).trans hs
      have hconj : conjBy (tor _ t) r s = GG.ofGL (tor _ t) * r s * GG.ofGL (tor _ t)⁻¹ := by
        rw [map_inv]
        rfl
      rw [ht, hconj, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
        SemidirectProduct.left_inl, SemidirectProduct.right_inl, sgnAct_one, SemidirectProduct.mul_right,
        SemidirectProduct.right_inl, hright, mul_one, sgnAct_one]
    have hI' : TypeI D.η (UnitaryThreeInertia.push A.val r') :=
      _root_.UpperTheory.Reformulated.B.Qf5.matIrr_conj (tor _ t) (fun s hs => by
        rw [mats, mats, GG.mat, GG.mat, hl s hs, ← Units.val_mul, ← Units.val_mul]
        congr 1
        group) hI
    have hm : HasMult D.η (UnitaryThreeInertia.push A.val r') := ho.red.mult
    have hiso : Af.RepIso (D.rhoK r hr) (D.rhoK _ hm) :=
      ⟨tor _ t, fun s => hl _ (D.η_ker.ge (Base.galEmb_mem ℚ K Ω s))⟩
    have key := h3 A r' ho (matIrr_open_gd D g₁ hM B hB A r' ho hI') (D.rhoK _ hm) fun s => rfl
    refine _root_.UpperTheory.GalN.V.autCsd_iso_alt ?_ key
    obtain ⟨g, hg⟩ := hiso.symm'
    refine ⟨g, fun s => Units.ext ?_⟩
    rw [Units.val_mul, Units.val_mul, Af.tw_val, Af.tw_val, hg, Units.val_mul, Units.val_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  · obtain ⟨A, _, _, t, r', ho, ht⟩ := exists_ordPt_of_point hL D g₁ hM U S hA B hmem ξ r hp
    let d : Fin 2 → (PadicAlgCl l)ˣ := ![t, t⁻¹]
    let T : GL (Fin 2) (PadicAlgCl l) :=
      Units.map (Matrix.diagonalRingHom (n := Fin 2) (α := PadicAlgCl l)).toMonoidHom
        (MulEquiv.piUnits.symm d)
    have hcorner (g : G ℚ Ω) :
        corner (conjBy (tor _ t) r g).mat = T.val * corner (r g).mat * (↑T⁻¹ : Matrix _ _ _) := by
      ext a b
      show _ = (Matrix.diagonal (fun i => (d i : PadicAlgCl l)) * corner (r g).mat *
        Matrix.diagonal (fun i => (↑(d i)⁻¹ : PadicAlgCl l))) a b
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul, corner, corner, Matrix.submatrix_apply, Matrix.submatrix_apply,
        (conjBy_tor r t).1, wt, zpow_sub, Units.val_mul, mul_right_comm]
      congr 1
      · congr 1
        fin_cases a <;> simp [d, wt1]
      · fin_cases b <;> simp [d, wt1]
    let W' : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l) := (MulAut.conj T).toMonoidHom.comp W
    have hW' : ∀ s, W' s = T * W s * T⁻¹ := fun s => rfl
    have hII' : TypeII D.η (UnitaryThreeInertia.push A.val r') := by
      rw [ht]
      refine ⟨fun g hg a b hab => ?_, _root_.UpperTheory.Reformulated.B.Qf5.matIrr_conj T (fun s _ => ?_) hII.2⟩
      · rw [(conjBy_tor r t).1, hII.1 g hg a b hab, mul_zero]
      · rw [hcorner]
        simp only [← Matrix.mul_assoc]
        rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    exact _root_.UpperTheory.GalN.V.modOfEnd'_alt D h2 A r' ho hII' (fun g hg => by
      apply Subtype.ext
      show (UnitaryThreeInertia.push A.val r' g).mat 1 1 = 1
      rw [ht, (conjBy_tor r t).1, h11 g hg]
      simp [wt]) W' (fun g hg => by
      rw [ht, hcorner, hW', Units.val_mul, Units.val_mul, hW.1 g hg]) (by
      rw [hW', Units.val_mul, Units.val_mul, Matrix.trace_units_conj, hW.2]) W (Af.RepIso.symm' ⟨T, hW'⟩)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BcOf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Desc.P
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Desc.P.dense_threshold_bc_of_prop : _root_.UpperTheory.V.Z.J.D.BcOfAlt := by
  intro H E Ω _ _ _ _ _ _ hE l _ hl ι n hn σ hσ R hRc hRi hR
  obtain ⟨r, HT, hc, hs, -, -, hL, -, hQ⟩ := _root_.UpperTheory.V.Z.Win.Gu.galUnitaryT_of_printsH H E Ω hE l hl ι n hn σ hσ
  have hss : Formalism.MainNotions.N.IsSSRep R := by
    intro M hM
    rcases hRi.2.2 M le_top hM with rfl | rfl
    · exact ⟨⊤, hRi.2.1, isCompl_bot_top⟩
    · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
      rw [(Submodule.mem_bot _).1 hv]
      simp
  have hunram : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsUnramU σ w := by
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
          rw [← mul_apply_eq_comp, ← map_mul, Subgroup.coe_inv, inv_mul_cancel,
            map_one, one_apply_eq_self] }
    have hLo : IsOpen (L : Set (finU (E := E) (n := n))) := (hσ.aut φ hφ).level
    filter_upwards [GlobalTheory.T.eventually_localIntegralPoints_mem_openSubgroup_definiteUnitary
      E n L hLo] with w hw
    exact ⟨φ, hφ, hφ0, fun x hx hxK => hw x hx hxK hx.1⟩
  have hAway : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, (l : 𝓞 E) ∉ w.asIdeal := by
    have h0 : Ideal.span {(l : 𝓞 E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : l.Prime).ne_zero
    exact (Ideal.finite_factors h0).subset fun w hw => Ideal.dvd_span_singleton.mpr (not_not.1 hw)
  have hAgree : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      IsSplitAt w → ∃ B, FrobEig ι R w B ∧ FrobEig ι r w B := by
    filter_upwards [hR, hAway, hunram] with w h1 hw hu hsp
    obtain ⟨τ, -, h2, h3⟩ := GlobalTheory.DefU.exists_locComp_split E n ⟨σ, hσ⟩ w hsp
    obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 (h3.1 hu)
    obtain ⟨b, hb⟩ := (_root_.UpperTheory.V.Af.satake_local_of_printed_results H.toClassicalTheorems E n w τ).1 ⟨v, h0, fun u hu => by simpa using hv ⟨u, hu⟩⟩
    have k : _root_.UpperTheory.V.Z.Win.LocGlobT ι r w τ := (hL w hsp τ h2).1
    exact ⟨_, _root_.UpperTheory.V.Z.Desc.W.satFrobT_alt H.toClassicalTheorems E Ω l ι n R hRc w hw τ b hb (_root_.UpperTheory.V.Z.Desc.P.lgAwayT (h1 hsp τ h2) hw),
      _root_.UpperTheory.V.Z.Desc.W.satFrobT_alt H.toClassicalTheorems E Ω l ι n r hc w hw τ b hb (_root_.UpperTheory.V.Z.Desc.P.lgAwayT k hw)⟩
  have hiso : RepIso R r := by
    have hChar : ∀ g : G E Ω, (R g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
        (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
      intro g
      ext i
      have hRcoeff : Continuous fun g : G E Ω =>
          (R g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
        (GlobalTheory.LocBound.continuous_coeff_charpoly n i).comp
          (Units.continuous_val.comp (hRc.comp continuous_inv))
      have hrcoeff : Continuous fun g : G E Ω =>
          (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
        (GlobalTheory.LocBound.continuous_coeff_charpoly n i).comp
          (Units.continuous_val.comp (hc.comp continuous_inv))
      refine congrFun (GlobalTheory.Published.chebotarevDegreeOne'.eq_of_frob
        (Filter.eventually_cofinite.1 hAgree) hRcoeff hrcoeff ?_) g
      intro w hw hd A hA s hFrob
      have hSplit := UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one E w (hE w) hd
      obtain ⟨B, hB, hB'⟩ := not_not.1 hw hSplit
      have h := ((hB A hA).2 s hFrob).trans ((hB' A hA).2 s hFrob).symm
      have h' := Polynomial.map_injective ι.toRingHom ι.injective h
      rw [h']
    obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix R r hss hs
      (fun g => by simpa using hChar g⁻¹)
    exact ⟨P⁻¹, fun g => by rw [hP g, inv_inv]⟩
  have hirr : IsIrr r := by
    obtain ⟨P, hP⟩ := hiso
    refine ⟨hRi.1, fun _ _ _ => Submodule.mem_top, fun M _ hM => ?_⟩
    let T : (Fin n → Qbar l) ≃ₗ[Qbar l] (Fin n → Qbar l) :=
      (Matrix.GeneralLinearGroup.toLin P).toLinearEquiv
    have hT : ∀ v, T v = (P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v := fun v => rfl
    have hInv : Formalism.MainNotions.N.IsInv R (M.comap T.toLinearMap) := by
      intro g v hv
      have hComm : T ((R g : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v) =
          (r g : Matrix (Fin n) (Fin n) (Qbar l)).mulVec (T v) := by
        rw [hT, hT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP g]
        simp [Matrix.mul_assoc]
      show T _ ∈ M
      rw [hComm]
      exact hM g _ hv
    have hMap := (Submodule.map_comap_eq_of_surjective T.surjective M).symm
    rcases hRi.2.2 _ le_top hInv with h | h
    · left
      rw [hMap, h, Submodule.map_bot]
    · right
      rw [hMap, h, Submodule.map_top, LinearMap.range_eq_top.2 T.surjective]
  obtain ⟨π, h1, h2, -, h4, h5, h6⟩ := hQ hirr
  refine ⟨π, h1, h2, ?_, h4, h5⟩
  filter_upwards [(_root_.UpperTheory.satake_galois_link_of_printed_hida H E n π).2] with w ⟨B, hB⟩ hsp
  obtain ⟨τ, hτ⟩ := (_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results H.toClassicalTheorems E n π w).1
  exact ⟨τ, B, h6 w hsp τ hτ, ((_root_.UpperTheory.satake_galois_link_of_printed_hida H E n π).1 w τ hτ B).1 hB, hB⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevTwoOf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem unit_card (l : ℕ) [hl : Fact l.Prime] (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))
    (hw : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (O : Type) [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] :
    IsUnit (resCard (w.adicCompletion L) : O) := by
  rw [resCard_eq_normV]
  by_contra hn
  have h1 : residue O (normV w : O) = 0 := (residue_eq_zero_iff _).2 hn
  rw [map_natCast, CharP.cast_eq_zero_iff (ResidueField O) l] at h1
  have hmax := w.isMaximal
  letI : Field (𝓞 L ⧸ w.asIdeal) := Ideal.Quotient.field _
  have hfin : Finite (𝓞 L ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Fintype.ofFinite (𝓞 L ⧸ w.asIdeal)
  have h2 : l ∣ Fintype.card (𝓞 L ⧸ w.asIdeal) := by
    rw [← Nat.card_eq_fintype_card]; exact h1
  have h3 := (prime_dvd_char_iff_dvd_card (R := 𝓞 L ⧸ w.asIdeal) l).2 h2
  have h4 : ringChar (𝓞 L ⧸ w.asIdeal) = l :=
    ((Nat.prime_dvd_prime_iff_eq hl.out (CharP.char_is_prime (𝓞 L ⧸ w.asIdeal) _)).1 h3).symm
  apply hw
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← h4]
  exact ringChar.Nat.cast_ringChar
private theorem chi_monic {n : ℕ} {A G : Type} [CommRing A] [Nontrivial A] [Group G] (D : GDet n A G) (y : MonoidAlgebra A G) :
    (D.chi y).Monic ∧ (D.chi y).natDegree = n := by
  obtain ⟨h0, -, -, -, h1, h2, -⟩ := UpperTheory.V.CA.d_chi D.toDet y
  rw [Det.lam, pow_zero, one_mul, Nat.sub_zero] at h0
  rw [(UpperTheory.V.CA.d_toDet D y).1] at h0 h1 h2
  exact ⟨h1, le_antisymm h2 (Polynomial.le_natDegree_of_ne_zero (by rw [h0]; exact one_ne_zero))⟩
private theorem lam_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (g : H) : (D.comap φ).lam i (MonoidAlgebra.single g 1) = D.lam i (MonoidAlgebra.single (φ g) 1) := by
  have : (D.comap φ).chi (MonoidAlgebra.single g 1) = D.chi (MonoidAlgebra.single (φ g) 1) := by
    change D.D _ (MonoidAlgebra.mapDomainRingHom _ φ _) = D.D _ _
    congr 1
    rw [map_sub]
    simp
  rw [GDet.lam, GDet.lam, this]
private theorem lam_map {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G] (D : GDet n A G) (f : A →+* A')
    (i : ℕ) (g : G) : (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have := ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 i
  rwa [MonoidAlgebra.mapRingHom_single, map_one] at this
private theorem fix_le {L : Type} [Field L] [NumberField L] {n q : ℕ} {w : Fin q → Plc L} {A M : Type} [CommRing A]
    [AddCommGroup M] [Module A M] (ρ : Representation A (GV n w) M) :
    fixd ρ (UK n w) ≤ fixd ρ (UC n w fun _ => ⊤) := by
  intro m hm u hu
  refine hm u fun j _ => ?_
  have h1 : iwC ((w j).adicCompletion L) n ⊤ ≤ KO _ (Fin n) := by
    rw [(memIwC _ n ⊤).2.1]
    exact iwahori_le_KO _ (Fin n)
  exact h1 (hu j trivial)
private theorem fix_at {L : Type} [Field L] [NumberField L] {n q : ℕ} {w : Fin q → Plc L} {A M : Type} [CommRing A]
    [AddCommGroup M] [Module A M] (ρ : Representation A (GV n w) M) (j : Fin q) :
    fixd ρ (UK n w) ≤ fixd (ρ.comp (atJ n w j)) (KO _ (Fin n)) := by
  intro m hm u hu
  refine hm (atJ n w j u) fun j' _ => ?_
  by_cases e : j' = j
  · subst e
    simpa [atJ] using hu
  · simp [atJ, Pi.mulSingle_eq_of_ne e]
private theorem two_gen (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (O A B M N : Type)
    [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [CommRing B] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    (ρ : Representation A (GV n w) M) (β : A →+* B) (P : Fin q → Polynomial B)
    (act : PU A q n →ₐ[A] Module.End A (fixd ρ (UC n w fun _ => ⊤)))
    (e : Fin q → Module.End A (fixd ρ (UC n w fun _ => ⊤)))
    (H : HkHyp O (qj w) act e
      (fun j => (fixd (ρ.comp (atJ n w j)) (KO _ (Fin n))).comap (fixd ρ (UC n w fun _ => ⊤)).subtype))
    (he : ∀ v, ((List.ofFn e).prod v : M) ∈ fixd ρ (UK n w))
    (eM : fixd ρ (UK n w) ≃+ N) (hM : ∀ (t : A) m, eM (t • m) = β t • eM m)
    (hP : ∀ j, (P j).Monic ∧ (P j).natDegree = n) (c : Fin q → ℕ → A)
    (hc : ∀ j k, β (c j k) = (-1) ^ k * (P j).coeff (n - k))
    (hs : ∀ j k, k ≤ n → ∀ m : fixd ρ (UC n w fun _ => ⊤), (m : M) ∈ fixd ρ (UK n w) →
      act (emb ℤ A j (MvPolynomial.esymm (Fin n) ℤ k)) m = c j k • m) :
    TwoMaps (M := N) β P act (fEl (qj w) fun j i => MvPolynomial.X (j, i)) := by
  let inc : N →+ fixd ρ (UC n w fun _ => ⊤) :=
    (Submodule.inclusion (fix_le ρ)).toAddMonoidHom.comp eM.symm.toAddMonoidHom
  have hinc : ∀ m, (inc m : M) = eM.symm m := fun _ => rfl
  let t0 : fixd ρ (UC n w fun _ => ⊤) →ₗ[A] fixd ρ (UK n w) :=
    ((fixd ρ (UC n w fun _ => ⊤)).subtype.comp (List.ofFn e).prod).codRestrict _ he
  let tr : fixd ρ (UC n w fun _ => ⊤) →+ N := eM.toAddMonoidHom.comp t0.toAddMonoidHom
  have hβ : ∀ (t : A) m, inc (β t • m) = t • inc m := fun t m => Subtype.ext (by
    obtain ⟨m, rfl⟩ := eM.surjective m
    rw [← hM, Submodule.coe_smul, hinc, hinc, eM.symm_apply_apply, eM.symm_apply_apply, Submodule.coe_smul])
  refine twoMul O A B N _ q n β P act (qj w) (multiTwo O A B N _ q n (qj w) β P act e _ inc tr H (fun j => (hP j).1)
    (fun j => (hP j).2) ?_ hβ (fun v => Subtype.ext ?_) (fun j m => fix_at ρ j (eM.symm m).2) fun j k hk m => ?_)
  · intro a b hab
    have h1 := congrArg Subtype.val hab
    rw [hinc, hinc] at h1
    exact eM.symm.injective (Subtype.ext h1)
  · rw [hinc]
    exact congrArg Subtype.val (eM.symm_apply_apply (t0 v))
  · rw [hs j k hk (inc m) (eM.symm m).2, ← hc, hβ]
theorem UpperTheory.V.Pa.Lev.twoOf_alt :
    _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (b : TWBase (pairOf B.u) J Empty D) (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (w : Fin q → Plc L) (A : LevMod b h w) (x δ : ∀ j, ((w j).adicCompletion L)ˣ), (∀ j, ((l : ℕ) : 𝓞 L) ∉ (w j).asIdeal) → (∀ j, IsUnif (x j)) → (∀ j, IsGenMod _ (ellC l _) (δ j)) → ∀ (T : ThData l A.ρ x δ) (ph ta : Fin q → (globOf r V).G₀), _root_.UpperTheory.V.Pa.Lev.LocalLevelConditions A x δ ph ta → TwoMaps (M := b.M) A.β.toRingHom (fun j => (pairOf B.u).D.chi (MonoidAlgebra.single (h.p₀ (ph j)) 1)) T.actw (fEl (qj w) fun j i => MvPolynomial.X (j, i)) := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J D b V h q w A x δ hl hx hδ T ph ta hok
  have hs := _root_.UpperTheory.V.Z.Win.T2.symOf_alt hP l L Ω s V0 O n r B J D b V h q w A x δ hl hx hδ T ph ta hok
  have hch : CharP (ResidueField O) l := UpperTheory.V.Pa.IsCoef.char
  obtain ⟨ι, hι, -⟩ := hok
  obtain ⟨e, H, he⟩ := hkHypOf L n q w l O A.R A.P A.ρ x δ T hx (fun j => unit_card l L (w j) (hl j) O)
    (fun k m hk hm => hι m fun y => by
      have h1 := congrArg y.sp hm
      rw [map_nsmul, map_zero, ← Nat.cast_smul_eq_nsmul ℂ] at h1
      exact (smul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 hk))
  refine two_gen L n q w O A.R B.B A.P b.M A.ρ A.β.toRingHom _ T.actw e H he A.eM A.eM_smul
    (fun j => chi_monic _ _) (fun j k => A.p.D.lam k (MonoidAlgebra.single (ph j) 1)) (fun j k => ?_) hs
  exact (lam_map A.p.D A.β.toRingHom k (ph j)).symm.trans
    ((congrArg (fun D' => GDet.lam D' k (MonoidAlgebra.single (ph j) 1)) A.β_pair.1).trans (lam_comap _ _ k _))
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Link2
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z UpperTheory.V.Z.Ord UpperTheory.Gal.projectedFormsSystemPart UpperTheory.GalN.V
namespace UpperTheory.Gal.projectedFormsSystemPart
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} {w : Plc F} {τ : SmIrr (GLw n w)} {B : Multiset ℂˣ}
end
theorem link2_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (hE : ∀ w : Plc E, Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) (l : ℕ) [Fact l.Prime] (hl2 : l ≠ 2)
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (hn : 1 ≤ n) (σ : Submodule ℂ (UA E n → ℂ)) (hσ : IsAutRepU σ)
    (ρ : G E Ω →* GL (Fin n) (Qbar l)) (hρc : Continuous ρ) (hρi : Af.IsIrr ρ)
    (hρF : ∀ᶠ w : Plc E in Filter.cofinite, IsSplitAt w → ∀ τ : SmIrr (GLw n w),
      IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → ∀ B, GlobalTheory.LFun.HasSatGL w τ.ρ B →
        Af.FrobEig ι ρ w (Af.algSat n (normV w) B)) :
    ∃ π : CuspSub E n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι ρ π ∧
      (∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B) ∧ ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w),
        π.IsLocComp w τ ↔ IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ := by
  obtain ⟨r, HT, hc, hs, -, -, hLG, -, hcusp⟩ := _root_.UpperTheory.V.Z.Win.Gu.galUnitaryT_of_printsH H E Ω hE l hl2 ι n hn σ hσ
  have hoff : ∀ᶠ w : Plc E in Filter.cofinite, (l : 𝓞 E) ∉ w.asIdeal := by
    have h0 : Ideal.span {(l : 𝓞 E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : l.Prime).ne_zero
    exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have hunram : ∀ᶠ w : Plc E in Filter.cofinite, IsUnramU σ w := by
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
          rw [← mul_apply_eq_comp, ← map_mul, Subgroup.coe_inv, inv_mul_cancel,
            map_one, one_apply_eq_self] }
    have hLo : IsOpen (L : Set (finU (E := E) (n := n))) := (hσ.aut φ hφ).level
    filter_upwards [GlobalTheory.T.eventually_localIntegralPoints_mem_openSubgroup_definiteUnitary E n L hLo] with w hw
    exact ⟨φ, hφ, hφ0, fun x hx hxK => hw x hx hxK hx.1⟩
  have hagree : ∀ᶠ w : Plc E in Filter.cofinite, w.asIdeal.inertiaDeg ℤ = 1 →
      ∃ B, Af.FrobEig ι r w B ∧ Af.FrobEig ι ρ w B := by
    filter_upwards [hoff, hunram, hρF] with w hl hu hw hd
    have hsp := UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one E w (hE w) hd
    obtain ⟨τ, hτ⟩ := (GlobalTheory.SplitComp.exists_comp_and_unique E n σ hσ w hsp).1
    obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.SphBC.isSpherical_of_isCompAlong_split hσ hsp τ.ρ hτ hu)
    obtain ⟨B, hB⟩ := (_root_.UpperTheory.V.Af.satake_local_of_printed_results H.toClassicalTheorems E n w τ).1 ⟨x, h0, GlobalTheory.LGrp.mem_fixed.1 hx⟩
    exact ⟨_, _root_.UpperTheory.Gal.projectedFormsSystemPart.frobLG'_alt H.toClassicalTheorems hc hl hB (hLG w hsp τ hτ).1, hw hsp τ hτ B hB⟩
  have hρss : IsSSRep ρ := fun M hM => by
    rcases hρi.2.2 M le_top hM with rfl | rfl
    · exact ⟨⊤, hρi.2.1, isCompl_bot_top⟩
    · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
      rw [(Submodule.mem_bot _).1 hv]
      simp
  have e : Af.RepIso r ρ := by
    have hchar := UpperTheory.V.Af.Es.charpoly_eq_prod ι (I := Unit) (a := fun _ => n)
      r (fun _ => ρ) hc (fun _ => hρc) (hagree.mono fun w h hd => by
        obtain ⟨B, h1, h2⟩ := h hd
        exact ⟨fun _ => B, by simpa using h1, fun _ => h2⟩)
    obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix
      r ρ hs hρss (fun g => by simpa using hchar g)
    exact ⟨P⁻¹, fun g => by rw [hP g, inv_inv]⟩
  have hri : Af.IsIrr r := by
    obtain ⟨P, hP⟩ := Af.RepIso.symm' e
    refine ⟨hρi.1, fun _ _ _ => Submodule.mem_top, fun M _ hM => ?_⟩
    let T := (Matrix.GeneralLinearGroup.toLin P).toLinearEquiv
    have hT : ∀ v, T v = (P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v := fun v => rfl
    have hi : IsInv ρ (M.comap T.toLinearMap) := fun g v hv => by
      have h1 := hM g _ hv
      change (r g : Matrix (Fin n) (Fin n) (Qbar l)).mulVec (T v) ∈ M at h1
      change T _ ∈ M
      have e1 : P * ρ g = r g * P := by rw [hP g, inv_mul_cancel_right]
      rw [hT, Matrix.mulVec_mulVec, ← Units.val_mul, e1, Units.val_mul,
        ← Matrix.mulVec_mulVec, ← hT]
      exact h1
    have hm := (Submodule.map_comap_eq_of_surjective T.surjective M).symm
    rcases hρi.2.2 _ le_top hi with h0 | h1
    · left
      rw [hm, h0, Submodule.map_bot]
    · right
      rw [hm, h1, Submodule.map_top, LinearMap.range_eq_top.2 T.surjective]
  obtain ⟨π, p1, p2, p3, -, p4, p5⟩ := hcusp hri
  refine ⟨π, p1, p2, ⟨hρss, p3.2.mono fun w ⟨b, hb, hf⟩ => ⟨b, hb, hf.of_iso e⟩⟩, p4, fun w hw τ => ⟨p5 w hw τ, fun hτ => ?_⟩⟩
  obtain ⟨τ', hτ'⟩ := (_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results H.toClassicalTheorems E n π w).1
  exact (GlobalTheory.BCT.isLocComp_iff_equiv hτ' τ).2 (UpperTheory.building_component_uniqueness E n σ hσ w hw _ _ _ _ hτ (p5 w hw τ' hτ'))
end UpperTheory.Gal.projectedFormsSystemPart
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TGalExW
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.V.Z.Sym.W.galois_exists_w_statement :
    _root_.UpperTheory.V.Z.Sym.W.GalExWAlt := by
  intro P L Ω _ _ _ _ _ _ l _ ι hl hE n hn σ hσ
  obtain ⟨r, HT, hc, hs, -, -, hLG, hp, hi⟩ := P.gal L Ω hE l hl ι n hn σ hσ
  refine ⟨r, ⟨hc, _root_.UpperTheory.V.Z.Sym.Al.exists_local_component_at_split_of_unitary_aut P.af.litN L hE n hn σ hσ,
    fun w hw τ hτ => (hLG w hw τ hτ).1, hp⟩, fun h => ?_⟩
  obtain ⟨π, h1, h2, h3, -, h4, h5⟩ := hi h
  exact ⟨π, h1, h2, h3, h4, h5⟩
end
end

