module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadLiftRealToComplexOfBaseChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.ModU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CRealEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.OrbitCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SeedPtOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.AutPtOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FinPtDown
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.AbsMain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.GdEndOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SymmetricCubeTheoremOfEndomorphisms
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0039
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.RankTwoDescentSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.GapTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Seed3
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0012

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EqOneOfUnr
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Desc.W
section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
private theorem exists_unr {ξ : kˣ →* ℂˣ} (h : IsUnram ξ) : ∃ a : ℂˣ, ξ = GlobalTheory.SmGL.unrChar k a := by
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (K := k) (ValuativeRel.uniformizer k)
  have h0 : x ≠ 0 := fun e => ValuativeRel.uniformizer_ne_zero (R := k) (by rw [← hx, e, map_zero])
  exact ⟨_, eq_unrChar h (ϖ := Units.mk0 x h0) hx⟩
private theorem full_chars [CharZero k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V)
    (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ i, IsSmoothChar (ξ i)) (hs : HasSupport ρ (GlobalTheory.RoadU.chars ξ hξ))
    (hu : GlobalTheory.RoadU.Unlinked (GlobalTheory.RoadU.chars ξ hξ)) : Nonempty (ρ.Equiv (prinSeries ξ)) ∧
    IsL ((List.ofFn fun i => Segment.single (IrrGL.ofChar (ξ i) (hξ i)) (IrrGL.isCusp_ofChar _ _) : List (Segment k)) :
      Multiset (Segment k)) ρ := by
  obtain ⟨hρ, hq⟩ := (UpperTheory.Gal.LocD.ofSupport_holds k n V ρ ξ hξ).1 hs
  let y : Fin n → IrrGL (k := k) := fun i => IrrGL.ofChar (ξ i) (hξ i)
  have hy : ∀ i, (y i).IsCusp := fun i => IrrGL.isCusp_ofChar _ _
  have hd : ∑ i, (y i).1 = n := by simp [y, IrrGL.ofChar]
  have hmem : ∀ i, y i ∈ GlobalTheory.RoadU.chars ξ hξ := fun i => Multiset.mem_map_of_mem _ (Finset.mem_univ i)
  have hnl : ∀ i j, ¬ (Segment.single (y i) (hy i)).Linked (Segment.single (y j) (hy j)) := fun i j =>
    GlobalTheory.CompanionTheory.BZPair.not_linked_single (hy i) (hy j) (hu _ (hmem j) _ (hmem i)) (hu _ (hmem i) _ (hmem j))
  have hP : (prodIrr y hd).IsIrreducible :=
    GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k n n (fun i => Segment.single (y i) (hy i)) y hd hnl
      (fun i => (single_spec (hy i)).2.1)
  obtain ⟨p⟩ := (Placing.parInd_jac_placing k _ _ _ (Equiv.sigmaUnique (Fin n) fun _ => Fin 1)
    (stdBlocks (fun i => (y i).1) hd) _).1 (piTensor fun i => detRep (Fin 1) (ξ i))
  let q := multiProdEquiv (stdBlocks (fun i => (y i).1) hd) fun i => equivRep (IrrRep.det (Fin 1) (ξ i) (hξ i))
  have hM : (multiProd (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) fun i => detRep (Fin 1) (ξ i)).IsIrreducible :=
    GlobalTheory.Parabolic.isIrreducible_of_equiv (p.trans q).symm hP
  haveI := nontrivial_of_irreducible hM
  haveI : Nontrivial (IndSp _ _) := by
    obtain ⟨S, f, hf⟩ := GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) ξ
    have := hf.nontrivial
    exact Subtype.val_injective.nontrivial (α := S.toSubmodule)
  have equiv_of_sub {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
      [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ) [Nontrivial W]
      (hρ : ρ.IsIrreducible) : Nonempty (ρ.Equiv σ) := by
    obtain ⟨S, f, hf⟩ := h
    obtain ⟨y, hy⟩ := exists_ne (0 : W)
    obtain ⟨v, rfl⟩ := hf y
    haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
    rcases eq_bot_or_eq_top S with rfl | rfl
    · exact absurd (by rw [show v = 0 from Subtype.ext v.2, map_zero]) hy
    let F : ρ.IntertwiningMap σ := f.comp (topEquiv ρ).symm.toIntertwiningMap
    have hs : Function.Surjective F := hf.comp (topEquiv ρ).symm.toLinearEquiv.surjective
    refine ⟨equivOfBijective F ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, hs⟩⟩
    rcases eq_bot_or_eq_top F.ker with h | h
    · have : x ∈ F.ker := hx
      rw [h] at this
      exact this
    · have : v.1 ∈ F.ker := by rw [h]; trivial
      exact absurd this hy
  obtain ⟨e1⟩ := equiv_of_sub (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n ξ) hM
  obtain ⟨e⟩ := hq.nonempty_equiv hρ (GlobalTheory.Parabolic.isIrreducible_of_equiv e1 hM)
  have φ : ρ.Equiv (prodIrr y hd) := (e.symm.trans e1.symm).trans (p.trans q)
  exact ⟨⟨e.symm⟩, n, y, hd, ⟨fun i => Segment.single (y i) (hy i), ⟨Fin.univ_val_map _, fun i j _ hp => hnl i j hp.1⟩,
    fun i => (single_spec (hy i)).2.1⟩, (isCosocle_self hρ).of_equiv (.refl _) φ⟩
end Loc
section WD
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
private theorem eq_one_of_unr {n : ℕ} (c : Fin n → Weil h →* ℂˣ) (hc : ∀ i, GlobalTheory.WeilDeligne.IsSmooth (c i))
    (hu : (sumList (List.ofFn fun i => WD.lpOfChar h (c i) (hc i))).unr) (i : Fin n) (t : Ine (F := E) A) :
    c i (ineIncl h t) = 1 := by
  have h1 : ∀ i g, (WD.lpOfChar h (c i) (hc i)).charPol g = X - C (c i g : ℂ) := fun i g => by
    rw [WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    simp
  have h2 : ((sumList (List.ofFn fun i => WD.lpOfChar h (c i) (hc i))).charPol (ineIncl h t)).IsRoot (c i (ineIncl h t) : ℂ) := by
    rw [GlobalTheory.LocLanglands.CuspExt.charPol_sumList, List.map_ofFn, List.prod_ofFn]
    refine IsRoot.dvd ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
    simp [h1]
  generalize sumList (List.ofFn fun i => WD.lpOfChar h (c i) (hc i)) = x at hu h2
  obtain ⟨m, b, rfl⟩ := x.exists_rep
  rw [WD.unr_mk] at hu
  rw [WD.charPol_mk, hu.2 t, ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at h2
  obtain ⟨v, hv⟩ := h2.exists_hasEigenvector
  have h3 := hv.apply_eq_smul
  refine Units.ext (smul_left_injective ℂ hv.2 ?_)
  simpa using h3.symm
end WD
theorem sphT_alt : _root_.UpperTheory.V.Z.Desc.W.SphTAlt := by
  intro _ F Ω _ _ _ _ _ l _ ι n r _ w hl A h hI rc ⟨a, ha, L⟩ σ hP hx
  haveI : CharZero (w.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F _).injective
  have e0 := hx.wdOf_eq hl
  obtain ⟨t, ht, φ, hφ, N, b, hN, -, -⟩ := id hx
  have hxu : (rc (algNorm σ)).unr := e0 ▸ (hN.unr_wdOf_iff hl ht ι).2 hI
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars _ _ hP
  have hs' : HasSupport σ.ρ (GlobalTheory.RoadU.chars ξ hξ) := hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
  obtain ⟨⟨e⟩, hL0⟩ := full_chars (n := n) σ.ρ ξ hξ hs' hu
  have hL := hL0.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
  have hr : rc (IrrGL.of σ.ρ σ.smooth σ.irred) =
      sumList (List.ofFn fun i => WD.lpOfChar h ((ξ i).comp a) (ha.smooth (hξ i))) := by
    rw [L.langlands _ _ hL, segSum, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.mpr (funext fun i => ?_)
    simp only [Function.comp_apply, Segment.single, Segment.first_ofFirst, Segment.len_ofFirst, Nat.cast_one, sub_self,
      zero_div, WD.lpTw_zero, Test.lpChar_lpSp_one, L.one]
  rw [algNorm, L.nu, hr, WD.unr_tw] at hxu
  have hun : ∀ i, IsUnram (ξ i) := fun i u hu1 => by
    obtain ⟨g, rfl⟩ := ha.surj u
    have h0 : deg g = 0 := by
      have h1 := ha.ord_eq g
      rw [ord_eq_zero_iff.2 hu1] at h1
      omega
    exact eq_one_of_unr _ _ hxu i ⟨g, deg_eq_zero_iff.1 h0⟩
  choose α hα using fun i => exists_unr (hun i)
  obtain rfl : ξ = fun i => GlobalTheory.SmGL.unrChar _ (α i) := funext hα
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1
    (GlobalTheory.PrinSat.hasSatGL_of_equiv e (GlobalTheory.PrinSat.hasSatGL_prinSeries w α)).1
  exact ⟨v, hv0, GlobalTheory.LGrp.mem_fixed.1 hv⟩
end UpperTheory.V.Z.Desc.W
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsPrimeIndex
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd Formalism.L2.Host.CT UpperTheory.V.Z.Bc
private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have hnorm : ∀ {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)),
      normV v = Ideal.absNorm v.asIdeal := by
    intro L _ _ v
    rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hnorm, hnorm]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]
private theorem algSat_pow (n q f : ℕ) (B : Multiset ℂˣ) :
    algSat n (q ^ f) (B.map (· ^ f)) = (algSat n q B).map (· ^ f) := by
  have e : ∀ (q : ℕ) (B : Multiset ℂˣ),
      algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := fun q B => by
    simp only [algSat, Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map, Function.comp_def]
  simp only [e, Multiset.map_map, Function.comp_def]
  refine Multiset.map_congr rfl fun α _ => ?_
  have h : (((q ^ f : ℕ) : ℝ)) ^ (((n : ℝ) - 1) / 2) = ((q : ℝ) ^ (((n : ℝ) - 1) / 2)) ^ f := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q),
      ← Real.rpow_mul (Nat.cast_nonneg q), mul_comm]
  rw [h, mul_pow, Units.val_pow_eq_pow_val, Complex.ofReal_pow]
private theorem upCycI (hP : _root_.UpperTheory.V.Af.Hypotheses') (hL : CyclicBaseChangeLiftRankTwo) (F E Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field E]
    [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω]
    [IsGalois F E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (hp : (Module.finrank F E).Prime) (r : G F Ω →* GL (Fin 2) (Qbar l))
    (π : CuspSub F 2) (hr : Continuous r) (hreg : (CG.mk π).IsRegAlg) (hatt : AttC ι r π) (hirr : IsIrr (r.comp (galEmb F E Ω))) :
    ∃ P : CuspSub E 2, (CG.mk P).IsRegAlg ∧ AttC ι (r.comp (galEmb F E Ω)) P ∧
      ∀ (τ : E →+* ℂ) m, π.HasInfChar (τ.comp (algebraMap F E)) m → P.HasInfChar τ m := by
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  rcases hL F E hp π hreg with ⟨η, hη, hT⟩ | ⟨P, hinf, hbc⟩
  · obtain ⟨δ, hδ1, -, hiso, hres⟩ := _root_.UpperTheory.V.Sd.self_twist_galois_of_printed_results hP F Ω l ι 2 r (CG.mk π).HasSat
      (fun _ _ _ h h' => h.unique h') hr hatt η _ hp.pos hη.2.1 hη.1 hT
    exact (hδ1 (UpperTheory.schur_twist_holds _ _ _ 2 r _ δ hirr (hres E hη) hiso)).elim
  · refine ⟨P, (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, ⟨(UpperTheory.galoisRep_irreducibility_criterion.1 _ Unit _ 2 _).2.1 hirr, ?_⟩, hinf⟩
    · have h := hreg (τ.comp (algebraMap F E))
      have hm : π.HasInfChar (τ.comp (algebraMap F E)) ((CG.mk π).infChar (τ.comp (algebraMap F E))) :=
        ParLaws.hasInfChar_infChar (CG.mk π) _
      rw [CG.HasInfChar.infChar_eq (π := CG.mk P) (hinf τ _ hm)]
      exact h
    · filter_upwards [hbc, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under F E).eventually hatt.2] with w h1 h2
      obtain ⟨B, hB, hPw⟩ := h1 _ (normV_under (K := F) w)
      obtain ⟨B', hB', hF⟩ := h2
      obtain rfl := hB.unique hB'
      refine ⟨_, hPw, ?_⟩
      have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w _ (normV_under (K := F) w)).1 2 r _ hF
      rw [← algSat_pow, ← normV_under] at h3
      exact h3
private theorem exists_prime_index (Γ : Type) [Group Γ] [Finite Γ] [Nontrivial Γ] [Group.IsSolvable Γ] :
    ∃ M : Subgroup Γ, M.Normal ∧ M.index.Prime := by
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom (commutator Γ)).resolve_left
    (Group.IsSolvable.commutator_lt_top_of_nontrivial Γ).ne
  have hn : M.Normal := ⟨fun n hn g => by
    have h1 : g * n * g⁻¹ * n⁻¹ ∈ M := hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    simpa using M.mul_mem h1 hn⟩
  refine ⟨M, hn, ?_⟩
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (n := Nat.card (Γ ⧸ M)) (mt Subgroup.index_eq_one.1 hM.1)
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  have h1 : (Subgroup.zpowers g).comap (QuotientGroup.mk' M) = ⊤ := by
    refine hM.2 _ (lt_of_le_of_ne (fun x hx => ?_) fun e => ?_)
    · rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
      exact one_mem _
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M g
      have hx : x ∈ M := e ▸ Subgroup.mem_zpowers _
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx, orderOf_one] at hg
      exact hp.one_lt.ne hg
  have h2 : Subgroup.zpowers g = ⊤ :=
    Subgroup.comap_injective (QuotientGroup.mk'_surjective M) (h1.trans (Subgroup.comap_top _).symm)
  rw [Subgroup.index, ← Subgroup.card_top, ← h2, Nat.card_zpowers, hg]
  exact hp
private theorem closure_tower (K E Ω : Type) [Field K] [Field E] [Field Ω] [Algebra K E] [Algebra K Ω] [Algebra E Ω]
    [IsScalarTower K E Ω] [Algebra.IsAlgebraic K E] [IsAlgClosure E Ω] : IsAlgClosure K Ω :=
  { isAlgClosed := IsAlgClosure.isAlgClosed E, isAlgebraic := Algebra.IsAlgebraic.trans K E Ω }
private theorem up_one (F E Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω]
    (h1 : Module.finrank F E = 1) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (π : CuspSub F n) (hreg : (CG.mk π).IsRegAlg) (ha : AttC ι r π)
    (hi : IsIrr (r.comp (galEmb F E Ω))) : ∃ P : CuspSub E n, (CG.mk P).IsRegAlg ∧ AttC ι (r.comp (galEmb F E Ω)) P ∧
      ∀ (τ : E →+* ℂ) m, π.HasInfChar (τ.comp (algebraMap F E)) m → P.HasInfChar τ m := by
  obtain ⟨-, hat⟩ := ha
  let j : E ≃+* F := (RingEquiv.ofBijective (algebraMap F E) (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1)).symm
  refine ⟨UpperTheory.V.FieldIso.pullSub j π, UpperTheory.V.FieldIso.isRegAlg_pullSub j hreg,
    ⟨(UpperTheory.galoisRep_irreducibility_criterion.1 _ (G E Ω) _ n _).2.1 hi, ?_⟩, fun τ m hm => by
      have h := (UpperTheory.V.FieldIso.hasInfChar_pullSub j π _ m).2 hm
      rwa [show (τ.comp (algebraMap F E)).comp (j : E →+* F) = τ from RingHom.ext fun x => congrArg τ (j.symm_apply_apply x)] at h⟩
  filter_upwards [(plMap_injective j).tendsto_cofinite.eventually hat] with w hw
  obtain ⟨B, hB, hF⟩ := hw
  have hu : w.under (𝓞 F) = plMap j w := HeightOneSpectrum.ext (Ideal.ext fun x => Iff.rfl)
  have hn : normV w = normV (plMap j w) := by
    have hnorm : ∀ {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)),
        normV v = Ideal.absNorm v.asIdeal := by
      intro L _ _ v
      rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [hnorm, hnorm]
    exact (absNorm_plMap j w).symm
  refine ⟨B, UpperTheory.V.FieldIso.hasSat_pullSub j hB, ?_⟩
  have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w 1 (by rw [hu, pow_one, hn])).1 n r _ (hu ▸ hF)
  rw [hn, ← hu]
  simp only [pow_one, Multiset.map_id'] at h3
  exact h3
theorem UpperTheory.V.Z.Bc.upSolI_of_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → CyclicBaseChangeLiftRankTwo → UpSolI := by
  intro P hL F E Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι
  induction hd : Module.finrank F E using Nat.strong_induction_on generalizing F with
  | _ d ih =>
  intro r π hc hreg ha hi
  by_cases h1 : Module.finrank F E = 1
  · exact up_one F E Ω h1 l ι 2 r π hreg ha hi
  haveI : Nontrivial (E ≃ₐ[F] E) := by
    rw [← Finite.one_lt_card_iff_nontrivial, IsGalois.card_aut_eq_finrank]
    have := Module.finrank_pos (R := F) (M := E)
    omega
  obtain ⟨M, hM, hp⟩ := exists_prime_index (E ≃ₐ[F] E)
  let K := IntermediateField.fixedField M
  haveI : IsGalois F K := IsGalois.of_fixedField_normal_subgroup M
  haveI : IsTotallyComplex K := isTotallyComplex_of_algebra F K
  haveI : Module.IsTorsionFree K Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure K Ω := closure_tower K E Ω
  haveI : Group.IsSolvable (E ≃ₐ[K] E) :=
    Group.isSolvable_of_isSolvable_injective (f := AlgEquiv.restrictScalarsHom F) (AlgEquiv.restrictScalars_injective F)
  have hdeg : Module.finrank F K = M.index := by
    have h2 := Module.finrank_mul_finrank F K E
    rw [IntermediateField.finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank F E, ← M.index_mul_card] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hlt : Module.finrank K E < d := by
    rw [← hd, ← Module.finrank_mul_finrank F K E, hdeg]
    exact lt_mul_of_one_lt_left Module.finrank_pos hp.one_lt
  have e : r.comp (galEmb F E Ω) = (r.comp (galEmb F K Ω)).comp (galEmb K E Ω) := rfl
  rw [e] at hi ⊢
  obtain ⟨Q, q1, q2, q3⟩ := upCycI P hL F K Ω l ι (hdeg ▸ hp) r π hc hreg ha ((UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ 2 _).1 _ hi)
  obtain ⟨Q', p1, p2, p3⟩ := ih _ hlt K rfl _ Q (hc.comp (resFacts F K Ω l 2 r).1) q1 q2 hi
  refine ⟨Q', p1, p2, fun τ m hm => p3 τ m (q3 _ m ?_)⟩
  rwa [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
theorem UpperTheory.V.Z.Bc.upQuadI_of_alt (hP : _root_.UpperTheory.V.Af.Hypotheses') (h : QuadLiftRealToComplexRankTwo) : UpQuadI := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι hE r π hr hreg hatt hirr
  obtain ⟨P, hBC⟩ := (h F E hE π hreg).resolve_left fun ⟨η, hη, ht⟩ =>
    UpperTheory.baseChange_noSelfTwist_of_frobenius_sign_irreducible (_root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results hP) UpperTheory.frobenius_eigenvalues_twist UpperTheory.exists_quadratic_sign_character UpperTheory.frobenius_sign_compatibility UpperTheory.schur_twist_holds UpperTheory.galoisRep_irreducibility_criterion F E Ω l ι hE 2 r π hr hatt hirr η hη ht
  have h1 := UpperTheory.V.Br.bcAtt0 F E Ω l ι 2 r π P hBC
  exact ⟨P, h1.1 hreg, h1.2 hatt ((UpperTheory.galoisRep_irreducibility_criterion.1 _ Unit _ 2 _).2.1 hirr), hBC.inf⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocPublished
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.V.W
theorem cohP_alt (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : Pa.CohP :=
  ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt, GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩
theorem global_compat_printed_of_literal_automorphy_n (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : GC.Hypotheses₂ :=
  ⟨⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.pt⟩, hN.coh.uo, hN.coh.gw⟩
theorem locPrints_of_litN (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : Loc.LocalPublishedTheorems :=
  ⟨hN.coh.lfK, hN.coh.ltK, hN.coh.leK, hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.bk⟩
theorem local_class_field_theory_all_of_literal_automorphy (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : LocCFTAll := locCFT hN.aut.art (_root_.UpperTheory.V.W.cohP_alt hN)
theorem modularity_unitary_of_automorphy_hida_unitary (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hP : Pa.PfromAut) (hH : _root_.UpperTheory.V.W.HidaUAlt) : _root_.UpperTheory.V.W.ModUAlt := _root_.UpperTheory.V.W.modU_of_printsH (_root_.UpperTheory.V.W.cohP_alt hN) (_root_.UpperTheory.V.W.local_class_field_theory_all_of_literal_automorphy hN) hP hH
end UpperTheory.V.W
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ModularDeformationQuotientRegularAtPoint
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
attribute [local instance high] DivisionSemiring.to_moduleIsTorsionFree
theorem UpperTheory.V.Ws.modular_deformation_quotient_regular_at_point_alt :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ (k : Type) [Field k] [Finite k] [Algebra c'.O k] (y : X.A →ₐ[c'.O] PowerSeries k),
        (∀ b ∈ maximalIdeal X.B, PowerSeries.constantCoeff (y (algebraMap X.B X.A b)) = 0) →
        (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
        (∀ v i j, i ≠ j → ∃ s ∈ T.U1 v, y (X.P.ψ v i s) ≠ y (X.P.ψ v j s)) →
        Irr (mapRep ((algebraMap (PowerSeries k) (FractionRing (PowerSeries k))).comp (y : X.A →+* PowerSeries k)) X.P.r) →
        X.LocZero J (y : X.A →+* PowerSeries k) := by
  intro _ Ω _ _ _ l _ c D T hF hD c' h K X B Λ ι J₀ hM φ hφ J hJ k _ _ _ y hy hyJ hU hI q hq hqy
  have hQ := P1.psPair D T c' h X k y hy
  haveI : IsLocalHom (algebraMap c'.O k) := ⟨fun a ha => by
    by_contra hn
    exact ha.ne_zero (hQ.loc a hn)⟩
  letI : Algebra (ResidueField c'.O) k := (ResidueField.lift (algebraMap c'.O k)).toAlgebra
  haveI : IsScalarTower c'.O (ResidueField c'.O) k := IsScalarTower.of_algebraMap_eq fun a => rfl
  obtain ⟨hfin, hchar, -⟩ := P1.coefRes c'
  obtain ⟨ρ, hρ, hρc⟩ := P1.rhoEx D T c' h K (PowerSeries k) _ (maximalIdeal _) (fun a ha => by
    rw [PowerSeries.algebraMap_apply, hQ.loc a ha, map_zero]; exact zero_mem _) hQ.pair hQ.cont
  obtain ⟨P, hP, hform⟩ := P1.formEx D T hF hD c' h K _ _ ρ hQ.pair hρ
  obtain ⟨ψ, hψ, hflag⟩ := P1.psiEx D T c' h K _ _ ρ hQ.pair hρ
  obtain ⟨hψr, hψc⟩ := P1.redPsi D T c' h K k _ hQ ψ hψ
  let x : W.Point K.r :=
    { K := k, ρ := ρ, cont := hρc, P := P, symm := hP, form := hform, red := P1.redDet D T c' h K k _ hQ ρ hρ
      ine := P1.ineTriv D T c' h K _ _ ρ hQ.pair hρ, ψ := ψ, ψ_red := hψr, flag := fun v => hflag _ _ v }
  obtain ⟨hne, hA⟩ := P1.condA D T hF hD c' h K _ _ ψ hψ (fun v i j hij => by
    obtain ⟨s, hs, hne⟩ := hU v i j hij
    have e := (sxPdMap (Φ := T.fr ∅) ((algebraMap c'.O X.A).comp (inc h)) (y : X.A →+* PowerSeries k) X.P).1
    exact ⟨s, hs, fun hh => hne ((e v i s).symm.trans (hh.trans (e v j s)))⟩)
  obtain ⟨n1, n2, n3⟩ := h4 l K.s.odd K.V.frame c'.O K.r x hne hψc hA
    (P1.irrL D T c' h K x _ hQ hρ hI) (P1.condC D T hF hD c' h K) (P1.condD D T hF hD c' h K)
  let f : B.B →ₐ[c'.O] x.A := (y.comp (IsScalarTower.toAlgHom c'.O X.B X.A)).comp φ
  have hf : B.IsPt x f := P1.mapsPt D T c' h K X B φ hφ _ y ρ ψ hρ hψ
  have key := hM.p1 x f ⟨n1, n2, n3, P1.n4V0 l _ _ 4 K.r K.v0 x⟩ hf
    (fun b hb => hyJ _ (hJ ▸ Ideal.mem_map_of_mem φ hb)) ⟨q.comap φ, hq.comap φ⟩ (fun b hb => hqy _ hb)
  rw [hJ]
  exact Ideal.map_le_iff_le_comap.2 key
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLinkEx
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk
private theorem pre_ex {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}
    (T : Tower D) (hO : T.Ok) (hG : D.Good) (hC : Ctx2 D ∨ Ctx3 D) : Nonempty (Pre T) := by
  obtain ⟨η, N, m, hN, hK, hm, hη, hcc, hun, hv⟩ := etaEx hC
  obtain ⟨κ₀, m', h1, h2, h3, h4, h5⟩ := Tw.kap0 Ω l hG.l_odd T.K T.degK (hO.split 2 hG.two_mem) η N m hN hK hm hη hcc
    (fun A => by
      by_cases hA : Raw.Away D.S A
      · exact Or.inl (hun A hA)
      · simp only [Raw.Away, not_forall, not_not] at hA
        obtain ⟨p, hp, hA⟩ := hA
        exact Or.inr (hO.split p hp A hA))
  obtain ⟨γ, g1, g2, g3, g4⟩ := halfEx hG
  have hl := hG.pl_over l Fact.out
  obtain ⟨t, β, c₁, b1, b2, b3, b4, b5, b6, b7, U, hU, b8⟩ :=
    Tw.bt0 Ω l hG.l_odd T.K T.degK (D.pl l) hl (hO.split l hG.l_mem _ hl)
  exact ⟨{ κ₀ := κ₀, γ := γ, β := β, t := t, κ₀_open := h1, κ₀_ord := ⟨m', h2, h3⟩,
           κ₀_conj := fun σ hσ s s' e hs => by rw [h4 σ hσ s s' e]; exact hv _ hs
           κ₀_unr := fun A hA => h5 A (hun A hA), γ_cont := g1, γ_red := g2, γ_sq := g3, γ_ker := g4,
           β_cont := b3, t_cont := b1, β_t := b2, β_red := fun s => (b4 s).2,
           conj := fun σ hσ s s' e => ⟨b6 σ hσ s s' e, b5 σ hσ s s' e⟩, t_unr := b7,
           cyc := betaCyc Ω l T.K T.degK (D.pl l) hl β b6 U hU b8 }⟩
theorem UpperTheory.V.Ws.nonempty_link_of_fit_deep_unramified :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∃ c₁ : Coef l, ∀ (c' : Coef l) (h : c.O ≤ c'.O), c₁.O ≤ c'.O → Nonempty (Link T c' h) := by
  intro hU Ω _ _ _ l _ c D T hF hD
  have hC : Ctx2 D ∨ Ctx3 D := hF.2.imp And.left And.left
  have hG : D.Good := hC.elim And.left And.left
  have hO := hF.1
  obtain ⟨P⟩ := pre_ex T hO hG hC
  obtain ⟨k1, k2, k3⟩ := kapCont P
  obtain ⟨u1, u2, u3⟩ := kapUnr P hG
  let Q : QCh T :=
    { κ := P.κ, β := P.βL, t := P.tL, κ_cont := k1, β_cont := k2, t_cont := k3, β_t := fun _ hg => P.β_t hg,
      β_red := fun _ => P.β_red _, conj := kapConj P hD, t_unr := u1, unr := u2, tame := u3, mu := kapMu P hG,
      cyc := kapCyc P hG }
  obtain ⟨c₁, -, hL, hκ, hβ, -⟩ := Pr.coefEx l c T.L Ω Q.κ Q.β Q.κ_cont Q.β_cont
  refine ⟨c₁, fun c' h h₁ => ?_⟩
  obtain ⟨κ, a1, a2, -⟩ := liftO c' Q.κ Q.κ_cont fun g => h₁ (hκ g)
  obtain ⟨β, b1, b2, b3⟩ := liftO c' Q.β Q.β_cont fun g => h₁ (hβ g)
  obtain ⟨X⟩ := ochOf Q c' h κ β a1 b1 a2 b2 fun g => b3 g (Q.β_red g)
  obtain ⟨Y⟩ := setEx T hG hO
  obtain ⟨V, hV⟩ := hU.lev l T.L Ω Y.s Y.s.S Y.fin subset_rfl Y.s.split
  obtain ⟨r, r1, r2, r3⟩ := residEx X Y V hG hO hV
  obtain ⟨σ, hσ, hc⟩ := Y.cc
  obtain ⟨g₀, -, hg₀⟩ := Y.om0
  exact ⟨{ s := Y.s, V := V, hV := hV, noMu := noMu hG T.L g₀ hg₀, large := fun τ x => h₁ (hL τ x), e := Y.e, hA := Y.hA,
           κ := X.κ, β := X.β, t := X.t, κ_cont := X.κ_cont, β_cont := X.β_cont, t_cont := X.t_cont, β_t := X.β_t,
           β_red := X.β_red, conj := fun g g' e => X.conj σ hσ g g' (hc g g' e), t_unr := X.t_unr,
           unr := fun A v hA hv g hg =>
             ⟨X.unr A (Y.away A v hA hv) hg, (((barFacts hG).2.2 A (Y.away A v hA hv) _ ⟨hg.1, hg.2⟩)).2⟩
           tame := X.tame
           mu := fun v g hg => by
             obtain ⟨a, ha⟩ := (prFacts l T.L Ω Y.s V).2.2.2 v g hg
             exact X.mu g a ha
           cyc := X.cyc, r := r, chib := fun i g => by rw [r1]; rfl
           psib := r2, th := r3, v0 := v0ok X Y V hG r r1 }⟩
end
end

