module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBoundMeansPosLogAreaNormalisedTheta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatible
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0009
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOneOfMembership
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0207
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsGlIsometryCompEqOfNondegenerate
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsVolumeTransportOfLatticeIsometry

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateLatticeMeansPosLogAreaThetaBounded
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchFree.means

open GlobalTheory.PositiveMeans

theorem exists_crv_conj {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (h2 : g2 (lamOf D cc δ) ∈ M) (h3 : g3 (lamOf D cc δ) ∈ M) :
    ∃ cc' δ', Crv D cc' δ' ∧ lamConj M ρ (lamOf D cc δ) = lamOf D cc' δ' := by
  obtain ⟨M', ρ', halg, hext⟩ := GlobalTheory.TwoTorsionPt.exists_extension M ρ
  have hl : lamConj M ρ (lamOf D cc δ) = lamConj M' ρ' (lamOf D cc δ) := by
    unfold lamConj
    rw [(hext _ h2).2, (hext _ h3).2]
  rw [hl]
  have hD : DataIn D (tor0 D cc δ) M' := by
    refine ⟨fun τ x => halg _ ?_, (hext _ h2).1, (hext _ h3).1⟩
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom
  obtain ⟨hfix, hbar, -⟩ := GlobalTheory.ThetaConj.useBar_holds D cc δ hc M' ρ' hD
  rcases hfix with hfix | hfix
  · obtain ⟨cc', δ', hc', -, e⟩ := GlobalTheory.ConjCurve.galCurve_holds D cc δ hc M' ρ' hfix hD.2.1 hD.2.2 1 one_pos
    exact ⟨cc', δ', hc', e⟩
  · obtain ⟨cc', δ', hc', -, e⟩ := GlobalTheory.ConjCurve.galCurve_holds D cc δ hc M' (rhoBar M' ρ') hfix hD.2.1 hD.2.2 1 one_pos
    have hm : (lamConj M' ρ' (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom = lamOf D cc' δ' := by
      rw [← e]
      exact (congrArg Tor.abelian₂ hbar).symm
    generalize lamConj M' ρ' (lamOf D cc δ) = Λ at hm
    obtain ⟨-, -, hdisc, -, hO⟩ := _root_.GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc' δ' hc'
    have hd : TaylorLogMetric.discr Λ = 1 := by
      rw [← hm, TaylorLogMetric.discr, g2, g3, eisG_conj, eisG_conj] at hdisc
      apply (starRingEnd ℂ).injective
      rw [map_one, ← hdisc, TaylorLogMetric.discr, g2, g3]
      simp [map_ofNat]
    obtain ⟨L, hL⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_discr_ne_zero (Λ := Λ)
      (by rw [hd]; exact one_ne_zero)
    obtain ⟨c, d, h, -, e'⟩ := GlobalTheory.ConjCurve.exists_crv D Λ L.ω₁ L.ω₂ (by simpa using L.indep.ne_zero 0)
      (fun z => (hL z).trans PeriodPair.mem_lattice) (fun r z hz => by
        obtain ⟨r', hr⟩ := exists_conj D r
        have h1 : (starRingEnd ℂ) z ∈ lamOf D cc' δ' := hm ▸ ⟨z, hz, rfl⟩
        have h4 : GlobalTheory.ConjCurve.embK D r' * (starRingEnd ℂ) z ∈ lamOf D cc' δ' := hO r' _ h1
        rw [hr, ← map_mul, ← hm] at h4
        obtain ⟨u, hu, e⟩ := h4
        have : u = _ := (starRingEnd ℂ).injective e
        exact this ▸ hu) hd 1 one_pos
    exact ⟨c, d, h, e'⟩

theorem means_le : ∃ C : ℝ, 0 < C ∧ ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ L : ℝ, 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M → wpF (lamOf D cc δ) t0 ∈ M → ∀ t : (M →ₐ[ℚ] ℂ) → ℂ, (∀ ρ, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) (t ρ)) → (∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹) / (Module.finrank ℚ M : ℝ) ≤ C * L ∧ (∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog (nrm1Sq (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) (t ρ)))) / (Module.finrank ℚ M : ℝ) ≤ C * L := by
  obtain ⟨C, hC, hA⟩ := GlobalTheory.LatticeAreaBound.area_bounded_of_discr_eq_one
  have hc1 : 0 ≤ Real.posLog C := Real.posLog_nonneg
  have hc2 : 0 ≤ Real.posLog (2 * Real.pi ^ 2) := Real.posLog_nonneg
  refine ⟨18 + 3 / 2 * (Real.posLog (2 * Real.pi ^ 2) + (Real.posLog C + 2)), by positivity, ?_⟩
  intro D cc δ t0 hc _ L hL hrd hdl M _ h2 h3 _ t ht
  obtain ⟨-, hlogd, hr1, -⟩ := _root_.GlobalTheory.NormSum.letters_and_sizes D (GlobalTheory.InducedType.induced_type D).1
  have hn : (0 : ℝ) < Module.finrank ℚ M := by exact_mod_cast Module.finrank_pos
  have hcard : (Fintype.card (M →ₐ[ℚ] ℂ) : ℝ) = Module.finrank ℚ M := by
    exact_mod_cast AlgHom.card ℚ M ℂ
  have hper := _root_.GlobalTheory.PeriodMean.mean_log_period D (GlobalTheory.InducedType.induced_type D).1 cc δ hc M h2 h3
  have hd0 : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have hpi := Real.pi_gt_three
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hlp : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith)
  have hl2p : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith)
  rw [Real.log_div (by positivity) (by positivity), Real.log_sqrt hd0.le, div_eq_iff hn.ne'] at hper
  have hB : Real.posLog (3 * (2 * D.host.rdE + 1)) ≤ 9 * L := by
    refine (Real.posLog_le_posLog (by linarith) (show _ ≤ 9 * D.host.rdE by linarith)).trans ?_
    rw [Real.posLog_eq_log (by rw [abs_of_pos (by positivity)]; linarith),
      Real.log_mul (by norm_num) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 9 by norm_num)
    linarith
  have key : ∀ ρ : M →ₐ[ℚ] ℂ,
      Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹ ≤
        Real.posLog C - Real.log (area (lamConj M ρ (lamOf D cc δ)) / Real.pi) - Real.log Real.pi ∧
      Real.posLog (nrm1Sq (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) (t ρ))) ≤
        (18 * L + 3 / 2 * Real.posLog (2 * Real.pi ^ 2)) +
          3 / 2 * Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹ := by
    intro ρ
    obtain ⟨cc', δ', hc', e⟩ := exists_crv_conj hc M ρ h2 h3
    have ht' := ht ρ
    rw [e] at ht' ⊢
    obtain ⟨hΛ, -, hdisc, -, hO⟩ := _root_.GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc' δ' hc'
    obtain ⟨ha0, haC⟩ := hA _ hΛ hdisc
    constructor
    · rw [Real.log_div ha0.ne' (by positivity)]
      have h1 := Real.posLog_le_posLog (by linarith) haC
      have h4 := Real.posLog_sub_posLog_inv (x := area (lamOf D cc' δ'))
      linarith
    · have := posLog_nrm_le _ hΛ hdisc ((_root_.GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D (GlobalTheory.InducedType.induced_type D).1).1 cc' δ' hc'.1 hc'.2)
        (_root_.GlobalTheory.GenusOneSup.value_le_mean_square D (GlobalTheory.InducedType.induced_type D).1 cc' δ' hc') ht'.1 (not_mem_lattice_of_isCMTorsionBasePoint ht' hO)
      linarith
  have s1 : ∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹ ≤
      (Real.posLog C + 2) * L * Module.finrank ℚ M := by
    refine (Finset.sum_le_sum fun ρ _ => (key ρ).1).trans ?_
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hper, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, hcard]
    have h5 := le_abs_self (logDerivativeAtOne D)
    have h6 : Real.posLog C ≤ Real.posLog C * L := le_mul_of_one_le_right hc1 hL
    have h7 : Real.posLog C - (Real.eulerMascheroniConstant + (Real.log (2 * Real.pi) - Real.log D.host.d / 2) -
      logDerivativeAtOne D) - Real.log Real.pi ≤ (Real.posLog C + 2) * L := by linarith
    have := mul_le_mul_of_nonneg_right h7 hn.le
    linarith
  have h8 : Real.posLog (2 * Real.pi ^ 2) ≤ Real.posLog (2 * Real.pi ^ 2) * L := le_mul_of_one_le_right hc2 hL
  constructor
  · rw [div_le_iff₀ hn]
    refine s1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by linarith)) hn.le)
    linarith
  · rw [div_le_iff₀ hn]
    refine (Finset.sum_le_sum fun ρ _ => (key ρ).2).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    have := mul_le_mul_of_nonneg_right h8 hn.le
    linarith

end GlobalTheory.ArchFree.means
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassStdAll
section
open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem genusMassStd_all : ∀ D : D7, GenusMassStd D :=
  genusMassStd_of_landherrHasse DefiniteOrthonormal.landherrHasse

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MassSelfDualLatticeFirstSpaceEq
section
noncomputable section

namespace GlobalTheory.ColClassNumber

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice
open GlobalTheory.IndefiniteRowSideFullHecke

theorem card_eq_index_mul_mass {G : Type} [Group G] (Γ U K : Subgroup G) (m : ℝ) (hUK : U ≤ K)
    (hidx : U.relIndex K ≠ 0) (hm : ClassesDoubleCosets.CosetMass Γ K m)
    (hfree : ∀ x γ : G, γ ∈ Γ → x⁻¹ * γ * x ∈ U → γ = 1) :
    (Nat.card (ClassSet Γ U) : ℝ) = (U.relIndex K : ℝ) * m := by
  obtain ⟨hfin, hst, hsum⟩ := hm
  letI : Fintype (ClassSet Γ K) := Fintype.ofFinite _
  have e : ∀ y : G, StabiliserCardinality.stab Γ K y ≃ stabAt Γ K y := fun y =>
    { toFun := fun γ => ⟨⟨γ.1, ((StabiliserCardinality.mem_stab Γ K y _).1 γ.2).1⟩, ((StabiliserCardinality.mem_stab Γ K y _).1 γ.2).2⟩
      invFun := fun γ => ⟨γ.1.1, (StabiliserCardinality.mem_stab Γ K y _).2 ⟨γ.1.2, γ.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hs : ∀ c : ClassSet Γ K, DoubleCoset.mk Γ K (Quotient.out c) = c := fun c => Quotient.out_eq' c
  have h := (GlobalTheory.Proof.DoubleCosetCountGlobalInterpolation.doubleCosetCount G Γ U K hUK ⟨hidx⟩
    (fun y => have := hst y; Finite.of_equiv _ (e y).symm)
    (fun x => (Subgroup.eq_bot_iff_forall _).2 fun γ hγ =>
      hfree x γ ((StabiliserCardinality.mem_stab Γ U x γ).1 hγ).1 ((StabiliserCardinality.mem_stab Γ U x γ).1 hγ).2)
    _ hs).2
  have h' := congrArg (fun q : ℚ => (q : ℝ)) h
  push_cast at h'
  rw [h', ← hsum _ hs]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [one_div, Nat.card_congr (e _)]

section Lattice

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] (sp : Spaces R F E)

theorem exists_lattice (N : Submodule (𝓞 E) (Fin R.k → E)) (hfin : Module.Finite (𝓞 E) N)
    (hspan : Submodule.span E (N : Set (Fin R.k → E)) = ⊤)
    (hdual : dualSet (sp.cm.sig : E →+* E) sp.gram0 N = (N : Set (Fin R.k → E))) :
    ∃ M : Submodule (𝓞 E) (sp.X 0).V, Submodule.IsLattice E M ∧
      Formalism.HermitianLatticesTheory.IsUnimodular (sp.X 0).hT M ∧ sp.crdLat0 M = N := by
  let e : (sp.X 0).V ≃ₗ[𝓞 E] (Fin R.k → E) := sp.crd0.restrictScalars (𝓞 E)
  have hmem : ∀ x, x ∈ N.map (e.symm : (Fin R.k → E) →ₗ[𝓞 E] (sp.X 0).V) ↔ sp.crd0 x ∈ N := fun x => by
    rw [Submodule.mem_map_equiv]; rfl
  refine ⟨N.map (e.symm : (Fin R.k → E) →ₗ[𝓞 E] (sp.X 0).V), ?_, ?_, ?_⟩
  · exact Submodule.IsLattice.of_fg E ((Module.Finite.iff_fg.1 hfin).map _)
  · ext x
    rw [hmem, ← SetLike.mem_coe (p := N), ← hdual]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply, Submodule.mem_one, hmem, sp.hermitianForm_base_coordinates, dualSet, Set.mem_setOf_eq,
      RingHom.mem_range]
    constructor
    · intro h y hy
      have := h (sp.crd0.symm y) (by simpa using hy)
      simpa using this
    · intro h y hy
      exact h _ hy
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmem x).1 hx
    · intro hy
      exact ⟨sp.crd0.symm y, (hmem _).2 (by simpa using hy), by simp⟩

end Lattice

theorem idx_pos (D : D7) : 0 < idxPi D (D.host.g 0) (D.host.g 1) := by
  have h : ∀ g k : ℕ, g.Prime → 0 < idxColLoc g k := by
    intro g k hg
    haveI : NeZero g := ⟨hg.ne_zero⟩
    haveI : Nonempty {A : GL (Fin k) (ZMod g) // IsUnitri (A : Matrix (Fin k) (Fin k) (ZMod g))} :=
      ⟨⟨1, fun i j h => by simp [h.ne'], fun i => by simp⟩⟩
    exact div_pos (Nat.cast_pos.2 Nat.card_pos) (Nat.cast_pos.2 Nat.card_pos)
  exact mul_pos (pow_pos (h _ _ (D.host.g_prime 0)) _) (pow_pos (h _ _ (D.host.g_prime 1)) _)

theorem mass_selfDualLattice_firstSpace_eq (D : D7) : letI := D.host.cmStar
    ∀ M : Submodule (𝓞 D.host.E) (D.sp.X 0).V, Submodule.IsLattice D.host.E M →
      Formalism.HermitianLatticesTheory.IsUnimodular (D.sp.X 0).hT M → Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT M = massI D D.R.k := by
  letI := D.host.cmStar
  intro M hM hu
  rw [← D.sp.rank0]
  exact GlobalTheory.genusMassStd D { D.sp.X 0 with L0 := M, standardTuple_isLattice := hM, baseLattice_isUnimodular := hu } (D.sp.X_sig 0)
    (baseSpace_posDef _ _ D.sp)

theorem classNumber (hover : SplittingProjection.SelfDualOverBase) (hindex : SelfDualLatticeIndex.StabiliserLevelIndexFormula)
    (hcos : ClassesDoubleCosets.ClassesAsDoubleCosets) (hstab : ColumnStabiliser.ColStabTrivial)
    (D : D7) (Lv : LevelData D) : ClassNumberFormula₂ D Lv := by
  letI := D.host.cmStar
  intro hg hs u hT
  obtain ⟨-, N, ⟨hfin, hspan, hdual, -⟩, -, -, hUK⟩ := hover D Lv u hT
  obtain ⟨M, hM, hu, rfl⟩ := exists_lattice D.sp N hfin hspan hdual
  have hidx := hindex D Lv u hs hT _ ⟨hfin, hspan, hdual.symm⟩ hUK
  have hm := hcos.2 D Lv u M hM hu
  rw [mass_selfDualLattice_firstSpace_eq D M hM hu] at hm
  have hrel := Subgroup.relIndex_subgroupOf (H := SelfDualLatticeIndex.levelU D Lv u)
    (SelfDualLatticeIndex.stabHat_le D (D.sp.crdLat0 M))
  have hne : (SelfDualLatticeIndex.levelU D Lv u).relIndex (SelfDualLatticeIndex.stabHat D (D.sp.crdLat0 M)) ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hidx
    exact (mul_pos (idx_pos D) (SelfDualLatticeIndex.factorT_pos D u)).ne hidx
  have h := card_eq_index_mul_mass _ ((Lv u).U.subgroupOf _) _ _ (Subgroup.comap_mono hUK)
    (hrel.trans_ne hne) hm (by
      intro x γ hγ hx
      have h1 := ColumnStabiliser.map_colStab D Lv u x
      rw [hstab D Lv u hg hs x, Subgroup.map_bot] at h1
      have h2 : γ.1 ∈ (⊥ : Subgroup _) := by
        rw [h1]
        exact ⟨hγ, ⟨_, hx, by simp [mul_assoc]⟩⟩
      exact Subtype.ext (Subgroup.mem_bot.1 h2))
  rw [Nat.card_eq_of_bijective _ (Lv u).y_bij]
  refine h.trans ?_
  rw [mul_assoc (massI D D.R.k), mul_comm (massI D D.R.k)]
  exact congrArg (· * massI D D.R.k) ((congrArg (fun n : ℕ => (n : ℝ)) hrel).trans hidx)

theorem classNumber_of_index (hover : SplittingProjection.SelfDualOverBase) (hindex : SelfDualLatticeIndex.StabiliserLevelIndexFormula)
    (D : D7) (Lv : LevelData D) : ClassNumberFormula₂ D Lv :=
  classNumber hover hindex (GlobalTheory.Proof.CosetGroupEquiv.massAsCosetSum_iff.1 GlobalTheory.Proof.TotallyDefiniteMass.massAsCosetSum)
    (GlobalTheory.Proof.StabilizerGroupMap.columnStabilisersTrivial_iff.1 GlobalTheory.Proof.EqOneOfMembership.columnStabilisersTrivial) D Lv

end GlobalTheory.ColClassNumber

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RightInvariantOfFiniteCovolume
section
noncomputable section

namespace GlobalTheory.VolumeRatioTypings

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open GlobalTheory.IndefiniteRowSideFullHecke.VolumePerpendicular
open GlobalTheory.VolRatioCompare (reLat)
open scoped TensorProduct Matrix ENNReal

theorem rightInvariant_of_finite_covolume {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G)
    [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    (hfin : μ 𝓕 ≠ ⊤) : μ.IsMulRightInvariant := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  refine ⟨fun g => ?_⟩
  have e : μ.map (· * g) = ((μ.map (· * g)).haarScalarFactor μ : ℝ≥0∞) • μ :=
    Measure.isMulLeftInvariant_eq_smul _ μ
  have h' : IsFundamentalDomain Γ ((· * g) ⁻¹' 𝓕) μ :=
    h.preimage_of_equiv (f := (· * g)) ⟨(measurable_mul_const g).aemeasurable, by rw [e]; exact Measure.smul_absolutelyContinuous⟩
      Function.bijective_id fun γ x => mul_assoc _ _ _
  have h1 : μ.map (· * g) 𝓕 = μ 𝓕 :=
    ((MeasurableEquiv.mulRight g).map_apply 𝓕).trans (h'.measure_eq h)
  rw [e, Measure.smul_apply, smul_eq_mul] at h1
  have h2 := (ENNReal.mul_left_inj (h.measure_ne_zero (NeZero.ne μ)) hfin).1 (h1.trans (one_mul _).symm)
  rw [e, h2, one_smul]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem volMeas_unique (V : HSp D) {P Q : ℕ} {μ μ' : Measure (GA D V)} (h : IsVolMeas D V P Q μ)
    (h' : IsVolMeas D V P Q μ') : μ' = μ := by
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : BorelSpace (UpqT P Q) := ⟨rfl⟩
  have : LocallyCompactSpace (UpqT P Q) :=
    (UpqUnimodular.modelEquiv P Q).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have := D.cd.haar P Q
  have := h.1
  have := h'.1
  have e : μ' = (μ'.haarScalarFactor μ : ℝ≥0∞) • μ := Measure.isMulLeftInvariant_eq_smul μ' μ
  obtain ⟨U, hU1, hU, hfin⟩ := (D.cd.cd P Q).exists_isOpen_measure_lt_top 1
  obtain ⟨θ, hθ⟩ := h.2.1
  obtain ⟨A, hA⟩ := (h.2.2 θ hθ).1
  have h1 := (h.2.2 θ hθ).2 A hA (fun _ => U) fun _ => hU.measurableSet
  have h2 := (h'.2.2 θ hθ).2 A hA (fun _ => U) fun _ => hU.measurableSet
  rw [e, Measure.smul_apply, smul_eq_mul, h1] at h2
  have h3 := (ENNReal.mul_left_inj (Finset.prod_ne_zero_iff.2 fun _ _ => hU.measure_ne_zero _ ⟨1, hU1⟩)
    (ENNReal.prod_ne_top fun _ _ => hfin.ne)).1 (h2.trans (one_mul _).symm)
  rw [e, h3, one_smul]

theorem isVol_of_pair (V : HSp D) {P Q : ℕ} {μ : Measure (GA D V)} (h : IsVolMeas D V P Q μ) {𝓕 : Set (GA D V)}
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) {x : ℝ} (hx : 0 < x) (e : μ 𝓕 = ENNReal.ofReal x) : IsVol D V P Q x := by
  refine ⟨hx, ⟨μ, h⟩, fun μ' h' => ?_⟩
  obtain rfl := volMeas_unique V h h'
  refine ⟨⟨𝓕, h𝓕⟩, fun 𝓖 h𝓖 => ?_⟩
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have := h.1
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ V)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ V) μ'
  have h𝓖' : IsFundamentalDomain (GQ V) 𝓖 μ' := h𝓖
  exact (h𝓖'.measure_eq h𝓕).trans e

theorem exists_conj (V : HSp D) (L : Submodule (𝓞 D.host.E) V.V) (h1 : Submodule.IsLattice D.host.E L)
    (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) : ∃ k ∈ GfC V, ∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      (finMat D.sp.cm.sig V.gram k).mulVec y ∈ latHat D.host.F D.host.E (L0c D (reLat V L h1 h2)) := by
  obtain ⟨γ, hfin, hγ⟩ := GlobalTheory.T.exists_local_conjugation_selfDual_lattices_host D V L h1 h2
  obtain ⟨k, hk, hkv⟩ := _root_.GlobalTheory.LocalUnitaryGlue.exists_finite_adelic D V γ hfin
  refine ⟨k, hk, fun y => ?_⟩
  refine (GlobalTheory.LatticeLocalGlobal.mem_latHat_iff D.host.F D.host.E V y).trans (Iff.trans ?_
    (GlobalTheory.LatticeLocalGlobal.mem_latHat_iff D.host.F D.host.E (reLat V L h1 h2) _).symm)
  refine forall_congr' fun v => (hγ v _).trans (iff_of_eq ?_)
  congr 1
  rw [← hkv v]
  funext i
  exact (RingHom.map_mulVec (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v)
    (AlgHom.id D.host.F D.host.E)).toRingHom _ y i).symm

theorem isVolMeas_reLat (V : HSp D) (L : Submodule (𝓞 D.host.E) V.V) (h1 : Submodule.IsLattice D.host.E L)
    (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) {P Q : ℕ} {μ : Measure (GA D V)} (h : IsVolMeas D V P Q μ)
    (hr : μ.IsMulRightInvariant) : IsVolMeas D (reLat V L h1 h2) P Q μ := by
  obtain ⟨k, hk, hkL⟩ := exists_conj V L h1 h2
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have := h.1
  refine ⟨h.1, h.2.1, fun θ hθ => ⟨(h.2.2 θ hθ).1, fun A hA B hB => ?_⟩⟩
  rw [← (h.2.2 θ hθ).2 A hA B hB, ← measure_preimage_mul μ k⁻¹, ← measure_preimage_mul_right μ k]
  refine congrArg μ (Set.ext fun (g : GA D V) => and_congr ?_ ?_)
  · show (∀ y : Fin V.rank → _, y ∈ latHat D.host.F D.host.E (L0c D (reLat V L h1 h2)) ↔
        (finMat D.sp.cm.sig V.gram g).mulVec y ∈ latHat D.host.F D.host.E (L0c D (reLat V L h1 h2))) ↔
      ∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
        (finMat D.sp.cm.sig V.gram (k⁻¹ * (g * k))).mulVec y ∈ latHat D.host.F D.host.E (L0c D V)
    have hm : ∀ (a b : GA D V) y, (finMat D.sp.cm.sig V.gram (a * b)).mulVec y =
        (finMat D.sp.cm.sig V.gram a).mulVec ((finMat D.sp.cm.sig V.gram b).mulVec y) := fun a b y => by
      rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, Matrix.mulVec_mulVec]
    have ho : ∀ y, (finMat D.sp.cm.sig V.gram k).mulVec ((finMat D.sp.cm.sig V.gram k⁻¹).mulVec y) = y := fun y => by
      rw [← hm, mul_inv_cancel, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one, Matrix.one_mulVec]
    constructor
    · intro hg y
      refine (hkL y).trans (Iff.trans (hg _) (Iff.trans (iff_of_eq ?_) (hkL _).symm))
      rw [hm, ho, hm]
    · intro hg y
      have := hg ((finMat D.sp.cm.sig V.gram k⁻¹).mulVec y)
      have := (hkL _).symm.trans (this.trans (hkL _))
      rw [hm, hm, ho, ho] at this
      exact this
  · have hk1 : ∀ a ∈ GfC V, ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) a = 1 := fun a ha ρ => by
      have ha' : infHom V a = 1 := ha
      rw [GlobalTheory.SmoothForms.RealPts.infMat_eq V, ha', Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    refine forall_congr' fun ρ => ?_
    have e : infMat D.sp.cm.sig V.gram (θ ρ) (k⁻¹ * (g * k)) = infMat D.sp.cm.sig V.gram (θ ρ) g := by
      rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_mul, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_mul, hk1 k hk, hk1 _ (inv_mem hk), one_mul, mul_one]
    exact iff_of_eq (congrArg (fun m : Matrix (Fin (reLat V L h1 h2).rank) (Fin (reLat V L h1 h2).rank) ℂ =>
      ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * m) e.symm)

theorem tMap_unimod (V V' : HSp D) (e : V.V ≃ₗ[D.host.E] V'.V) (he : ∀ x y, V'.hT (e x) (e y) = V.hT x y) :
    Formalism.HermitianLatticesTheory.IsUnimodular V'.hT (tMap e V.L0) := by
  have h : ∀ x, (∀ y ∈ V.L0, V.hT y x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) ↔ x ∈ V.L0 := fun x => by
    conv_rhs => rw [← V.baseLattice_isUnimodular]
    simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual]
  ext x
  rw [mem_tMap, ← h]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
    mem_tMap]
  refine ⟨fun H y hy => ?_, fun H y hy => ?_⟩
  · have := H (e y) (by simpa using hy)
    rwa [← e.apply_symm_apply x, he] at this
  · rw [← isoSymm e he]
    exact H _ hy

theorem isVol_of_isometry (V V' : HSp D) (e : V.V ≃ₗ[D.host.E] V'.V) (he : ∀ x y, V'.hT (e x) (e y) = V.hT x y)
    {P Q : ℕ} {x : ℝ} (h : IsVol D V P Q x) : IsVol D V' P Q x := by
  obtain ⟨hx, ⟨μ, hμ⟩, hall⟩ := h
  obtain ⟨⟨𝓕, h𝓕⟩, hv⟩ := hall μ hμ
  let V₁ := reLat V' (tMap e V.L0) (tMap_lattice e _ V.standardTuple_isLattice) (tMap_unimod V V' e he)
  obtain ⟨φ, hc, hc', hQ, hφ⟩ := _root_.GlobalTheory.VolTransport.transport D V V₁ e he fun x => by
    show _ ↔ e x ∈ tMap e V.L0
    rw [mem_tMap, e.symm_apply_apply]
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V₁.rank V₁.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V₁.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V₁.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : Countable (GQ V₁) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  let ψ : GA D V ≃ᵐ GA D V₁ := ⟨φ.toEquiv, hc.measurable, hc'.measurable⟩
  have hν := hφ P Q μ hμ
  have := hν.1
  have h𝓕' : IsFundamentalDomain (GQ V) 𝓕 μ := h𝓕
  have h𝓖 : IsFundamentalDomain (GQ V₁) (φ.symm ⁻¹' 𝓕) (μ.map φ) :=
    h𝓕'.preimage_of_equiv (f := φ.symm)
      (MeasurePreserving.symm ψ ⟨ψ.measurable, rfl⟩).quasiMeasurePreserving
      (e := fun γ => ⟨φ γ, (hQ γ).1 γ.2⟩)
      ⟨fun a b hab => Subtype.ext (φ.injective (congrArg Subtype.val hab)),
        fun b => ⟨⟨φ.symm b, (hQ _).2 (by simp)⟩, Subtype.ext (by simp)⟩⟩
      fun γ y => by
        show φ.symm (φ γ * y) = γ * φ.symm y
        rw [map_mul, φ.symm_apply_apply]
  have hvol : μ.map φ (φ.symm ⁻¹' 𝓕) = ENNReal.ofReal x := by
    rw [← hv 𝓕 h𝓕]
    refine (ψ.map_apply _).trans (congrArg μ ?_)
    ext g
    exact iff_of_eq (congrArg (· ∈ 𝓕) (φ.symm_apply_apply g))
  have hr := rightInvariant_of_finite_covolume (GQ V₁) (μ.map φ) h𝓖 (hvol ▸ ENNReal.ofReal_ne_top)
  exact isVol_of_pair V' (isVolMeas_reLat V₁ V'.L0 V'.standardTuple_isLattice V'.baseLattice_isUnimodular hν hr) h𝓖 hx hvol

end GlobalTheory.VolumeRatioTypings
end
end

