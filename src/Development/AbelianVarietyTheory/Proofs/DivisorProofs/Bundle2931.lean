module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2876
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFirstCohomologyDimensionBoundCocycles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2889
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2816
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesVecFlatEqSum
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1815
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1820
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2845
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjIdealEqCP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0935
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TwoRunDatumBoundUnitAtIndefinitePoint
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsEmptyOfNotAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2405
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2863
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CohomologyLogDerivativeAdjointEndomorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreCechCocyclesCombinationCoefficientNon
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.FibreH1

theorem resG_appLE {Y : Scheme.{0}} {K : Type} [CommRing K] (s : Y ⟶ Sp K) {V V' : Y.Opens} (h : V' ≤ V)
    (x : Γ(Sp K, ⊤)) : resG Y h ((s.appLE ⊤ V le_top).hom x) = (s.appLE ⊤ V' le_top).hom x := by
  exact congrArg (fun φ : Γ(Sp K, ⊤) ⟶ Γ(Y, V') => φ.hom x)
    (Scheme.Hom.appLE_map s (U := ⊤) le_top (homOfLE h).op)

theorem fieldDep : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (J : Type) (W : J → A.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = ⊤ → ∀ (e : Fin (g + 1) → ∀ i i' : J, Γ(A.left, W i ⊓ W i')), (∀ b i i' i'', resG A.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e b i i') + resG A.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e b i' i'') = resG A.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e b i i'')) → ∃ c : Fin (g + 1) → K, c ≠ 0 ∧ ∃ h : ∀ i, Γ(A.left, W i), ∀ i i', ∑ b, (A.hom.appLE ⊤ (W i ⊓ W i') le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c b)) * e b i i' = resG A.left inf_le_left (h i) - resG A.left inf_le_right (h i') := by
  intro K _ A _ g hA hsm J W hW hcov e he
  haveI := hA.proper
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun i => (W i : Set A.left))
    (fun i => (W i).isOpen) (by
      intro x _
      have hx : x ∈ (⨆ i, W i) := by rw [hcov]; trivial
      rw [TopologicalSpace.Opens.mem_iSup] at hx
      exact Set.mem_iUnion.2 hx)
  let σ : Fin t.card → J := fun k => (t.equivFin.symm k).1
  have hσ : ⨆ k, W (σ k) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨t.equivFin ⟨i, hi⟩, by simpa [σ] using hx⟩
  obtain ⟨hfin, hrk⟩ := _root_.GlobalTheory.AbCoh.FDimField.cechLB_triv_finite_finrank_one_le K A g hA hsm (Fin t.card) (fun k => W (σ k)) (fun k => hW _) hσ
  obtain ⟨c, hc, h', hh'⟩ := _root_.GlobalTheory.OrdCechDep.exists_comb_coboundary K A.left A.hom g (Fin t.card) (fun k => W (σ k)) hfin hrk
    (fun b k k' => e b (σ k) (σ k')) (fun b k k' k'' => he b _ _ _)
  refine ⟨c, hc, ?_⟩
  exact _root_.GlobalTheory.CechCobGlue.cocycle_coboundary_of_subcover A.left J W (Fin t.card) σ hσ
    (fun i i' => ∑ b, (A.hom.appLE ⊤ (W i ⊓ W i') le_top).hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c b)) * e b i i') (by
      intro i i' i''
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, resG_appLE]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← mul_add, he b]) h' hh'

theorem fibre_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (e : Fin (n + 1) → ∀ i i' : J, Γ(A.left, ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i')), (∀ b, (∀ i i' i'', resG A.left (inf_le_left : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (e b i i') + resG A.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'') (e b i' i'') = resG A.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i'') (e b i i''))) → ∃ r : Fin (n + 1) → Γ(X, U.1), (∃ b, r b ∉ m) ∧ ∃ h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i), ∀ i i', ∑ b, (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom ((t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b)) * e b i i' = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i') := by
  intro E _ _ _ H X t hprop hamp U n v hv huniq J W hWa hcov hWU m hm A _ ι hpb e he
  letI : Field (Γ(X, U.1) ⧸ m) := Ideal.Quotient.field m
  obtain ⟨hA, hsm⟩ := GlobalTheory.T.closedFibre_isAbelianScheme_relDim_of_frame E H X t hprop U n v hv huniq m hm A ι hpb
  have hsq := hpb.1
  have hw : ι ≫ t.G.hom = A.hom ≫ spMap (Ideal.Quotient.mk m) ≫ chart U := hsq.w
  have htop : ⨆ i, ι ⁻¹ᵁ W i = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : t.G.hom.base (ι.base x) ∈ (U.1 : Set X) := by
      change (ι ≫ t.G.hom).base x ∈ _
      rw [hw, ← U.2.range_fromSpec]
      exact ⟨_, rfl⟩
    have hx' : ι.base x ∈ (⨆ i, W i) := by rw [hcov]; exact hx
    rw [TopologicalSpace.Opens.mem_iSup] at hx' ⊢
    exact hx'
  have haff : ∀ i, IsAffineOpen (ι ⁻¹ᵁ W i) := fun i =>
    _root_.GlobalTheory.AffinePreimageFibre.isAffineOpen_preimage_fibre X t.G.left t.G.hom U m A.left A.hom ι hsq (W i) (hWa i) (hWU i)
  obtain ⟨c, hc, h, hh⟩ := fieldDep (Γ(X, U.1) ⧸ m) A n hA hsm J (fun i => ι ⁻¹ᵁ W i) haff htop e he
  choose r hr using fun b => Ideal.Quotient.mk_surjective (c b)
  refine ⟨r, ?_, h, fun i i' => ?_⟩
  · obtain ⟨b, hb⟩ := Function.ne_iff.1 hc
    refine ⟨b, fun hmem => hb ?_⟩
    rw [← hr b]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hmem
  · rw [← hh i i']
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [_root_.GlobalTheory.fibre_restrict_scalar_compat X t.G.left t.G.hom U m A.left A.hom ι hw (W i ⊓ W i') (inf_le_left.trans (hWU i))
      (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx), hr b]

end GlobalTheory.FibreH1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongModOfMkEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GalLab

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem three_le_level (X₁ : Setup F W i) : 3 ≤ X₁.S.r * X₁.S.N := by
  have hN := X₁.ρ.N_eq
  have hn := X₁.ρ.n_prime.two_le
  have hk := X₁.ρ.two_le
  have hr := X₁.S.r_pos
  have h4 : 4 ≤ X₁.S.N := by
    rw [hN]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (X₁.ρ.n ^ X₁.ρ.k) ^ 2 :=
        Nat.pow_le_pow_left (le_trans hn (Nat.le_self_pow (by omega) _)) 2
  nlinarith

theorem isLab_onto (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)) {p : ℕ} [Fact p.Prime]
    {z : X.M.Z} (c : CTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X))
    (h : IsLab X ε c yy) (μ : Fin 8 → c.T.D.toPre.X) : ∃ a, yy a = QuotientAddGroup.mk μ := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, -, y₀, -, u, l, j, -, hyy, -⟩ := h
  obtain ⟨a, ha⟩ := l.yy_onto (QuotientAddGroup.mk (j.symm μ))
  exact ⟨a, by rw [hyy a _ ha, AddEquiv.apply_symm_apply]⟩

theorem congMod_of_mk_eq {X : Type} [AddCommGroup X] [Module.Free ℤ X] (κ : X ≃+ X) (m d L₁ : ℕ) (hm : m = d * L₁)
    (hd : d ≠ 0) (x : X)
    (h : (QuotientAddGroup.mk (d • (Pi.single (0 : Fin 8) x : Fin 8 → X)) : ModN m (Fin 8 → X)) =
      QuotientAddGroup.mk (fun b => κ ((d • (Pi.single (0 : Fin 8) x : Fin 8 → X)) b))) : CongMod L₁ (κ x) x := by
  obtain ⟨w, hw⟩ := QuotientAddGroup.eq.1 h
  have hw0 := congrFun hw 0
  simp only [nsmulAddMonoidHom_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Pi.single_eq_same,
    map_nsmul] at hw0
  refine ⟨w 0, ?_⟩
  have key : (d : ℤ) • ((L₁ : ℤ) • w 0) = (d : ℤ) • (κ x - x) := by
    rw [← mul_smul, ← Nat.cast_mul, ← hm, natCast_zsmul, hw0, smul_sub, natCast_zsmul, natCast_zsmul]; abel
  have := smul_right_injective X (show (d : ℤ) ≠ 0 by exact_mod_cast hd) key
  rw [← natCast_zsmul, this]; abel

theorem rigid {X₁ : Setup F W i} {ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (D : Deep X₁ ε₁)
    {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (c : CTrait X₁ p z₁)
    (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)) (h₁ : IsLab X₁ ε₁ c yy₁)
    (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y)
    (yy yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X))
    (hl : IsLab D.X D.ε (D.lift c y h) yy) (hc : D.Compat yy₁ yy)
    (hl' : IsLab D.X D.ε (D.lift c y h) yy') (hc' : D.Compat yy₁ yy') : yy' = yy := by
  obtain ⟨κ, hκβ, hκ⟩ := LabUniq.main g n F W Z i D.X D.ε D.diag p (y (cPt p)) (D.lift c y h) yy yy' hl hl'
  have hdvd : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N := by
    rw [D.sq]
    exact D.dvd.trans ((dvd_pow_self D.m two_ne_zero).mul_left _)
  have hdL : D.X.S.r * D.X.S.N = D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) * (X₁.S.r * X₁.S.N) :=
    (Nat.div_mul_cancel hdvd).symm
  have hd0 : D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) ≠ 0 := by
    intro h0
    have h3 := three_le_level D.X
    rw [hdL, h0, zero_mul] at h3
    omega
  have hcong : ∀ x, CongMod (X₁.S.r * X₁.S.N) (κ x) x := by
    intro x
    obtain ⟨a, ha⟩ := isLab_onto X₁ ε₁ c yy₁ h₁ (Pi.single 0 x)
    have e1 := hc a _ ha
    have e2 := hc' a _ ha
    have e3 := hκ (D.lab a) _ e1
    rw [e2] at e3
    exact congMod_of_mk_eq κ _ _ _ hdL hd0 x e3
  let e : c.T.D.toPre.X ≃ₗ[ℤ] c.T.D.toPre.X := κ.toIntLinearEquiv
  have he : e = LinearEquiv.refl ℤ _ :=
    eq_refl_of_isometry_congMod _ c.T.β (fun x hx => Trait.beta_pos g n _ _ F c.T x hx) e hκβ _
      (three_le_level X₁) hcong
  have hκ1 : ∀ x, κ x = x := fun x => by
    have := congrArg (fun f : c.T.D.toPre.X ≃ₗ[ℤ] c.T.D.toPre.X => f x) he
    simpa [e] using this
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨μ, hμ⟩ := QuotientAddGroup.mk_surjective (yy x)
  rw [hκ x μ hμ.symm, ← hμ]
  simp [hκ1]

end GlobalTheory.Poinc.GalLab

theorem GlobalTheory.Poinc.GalLab.main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, (∀ x, a (D.lab x) = D.lab x) ∧ ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) (h' : (y ≫ s) ≫ D.q = c.y) (yy yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → IsLab D.X D.ε (D.lift c (y ≫ s) h') yy' → D.Compat yy₁ yy' → ∀ x, yy' x = yy (a x) := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D σ s hs
  obtain ⟨a, hfix, htr⟩ := _root_.GlobalTheory.Poinc.galTransport g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D σ s hs
  refine ⟨a, hfix, ?_⟩
  intro p _ z₁ c yy₁ h₁ y h h' yy yy' hl hc hl' hc' x
  have hl2 := htr p z₁ c y h h' yy hl
  have hc2 : D.Compat yy₁ (yy.comp a.toAddMonoidHom) := fun b μ hb => by
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, hfix]
    exact hc b μ hb
  have := GalLab.rigid D c yy₁ h₁ (y ≫ s) h' (yy.comp a.toAddMonoidHom) yy' hl2 hc2 hl' hc'
  exact (DFunLike.congr_fun this x)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTwistOfDiscreteSeries
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwConj

open GlobalTheory.ConjTwist

theorem scale_pow_eq {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) {c c' : ℂ}
    (h : IsScale Rl v₀ B c) (h' : IsScale Rl v₀ B c') : ∃ k : ℕ, k ≠ 0 ∧ c' ^ k = c ^ k := by
  obtain ⟨gR, cR0, cL0, hT, u, hu, hF⟩ := h
  obtain ⟨gR', cR0', cL0', hT', u', hu', hF'⟩ := h'
  obtain rfl : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  obtain ⟨a, ⟨k, hk, hak⟩, ha⟩ := _root_.GlobalTheory.CoefRoot.coef_root _ _ _ _ _ _ _ _ _ _ _ _ _ hT hT' j
  obtain ⟨F, x, hx⟩ := _root_.GlobalTheory.CoeffNonvanish.exists_coefFn_ne_zero (FWT.lamV D j)
  have e1 := hF' F
  rw [ha] at e1
  erw [LinearMap.map_smul, LinearMap.map_smul, hF F] at e1
  have e2 := congrFun e1 x
  simp only [Pi.smul_apply, smul_eq_mul] at e2
  have hc : c' = D.what₂.embLL a * c := (mul_right_cancel₀ hx ((mul_assoc _ _ _).trans e2)).symm
  exact ⟨k, hk, by rw [hc, mul_pow, ← map_pow, hak, map_one, one_mul]⟩

theorem root_mul {a b : ℂ} (ha : IsRoot1 a) (hb : IsRoot1 b) : IsRoot1 (a * b) := by
  obtain ⟨n, hn, ha⟩ := ha
  obtain ⟨m, hm, hb⟩ := hb
  exact ⟨n * m, Nat.mul_pos hn hm, by rw [mul_pow, pow_mul, ha, one_pow, mul_comm n, pow_mul, hb, one_pow, one_mul]⟩

theorem root_inv {a : ℂ} (ha : IsRoot1 a) : IsRoot1 a⁻¹ := by
  obtain ⟨n, hn, ha⟩ := ha
  exact ⟨n, hn, by rw [inv_pow, ha, inv_one]⟩

theorem root_map (τ : ℂ ≃+* ℂ) {a : ℂ} (ha : IsRoot1 a) : IsRoot1 (τ a) := by
  obtain ⟨n, hn, ha⟩ := ha
  exact ⟨n, hn, by rw [← map_pow, ha, map_one]⟩

theorem root_ne {a : ℂ} (ha : IsRoot1 a) : a ≠ 0 := by
  obtain ⟨n, hn, ha⟩ := ha
  rintro rfl
  rw [zero_pow hn.ne'] at ha
  exact zero_ne_one ha

theorem root_charOf {D : D7} (a : Recip D D.nd.Om) {R : Type} [CommRing R] (f : R →+* ℂ) {ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* Rˣ}
    (h : IsOpen (ψ.ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om))) (x : (AE D)ˣ) :
    IsRoot1 ((GlobalTheory.SeriesTie.charOf a f ψ x : Circle) : ℂ) := by
  obtain ⟨σ, hσ⟩ := a.exists_sym x
  have hfin : Finite (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om ⧸ ψ.ker) := Subgroup.quotient_finite_of_isOpen _ h
  have hn : ψ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : ψ σ ^ ψ.ker.index = 1 := by rw [← map_pow]; exact ψ.ker.pow_index_mem σ
  refine ⟨_, Nat.pos_of_ne_zero hn, ?_⟩
  rw [charOf_eq a f h hσ hn h1, ← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]

theorem root_delta {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (x : (AE D)ˣ) :
    IsRoot1 (((ρ.B i j b).de.chi x : Circle) : ℂ) := by
  rw [hρ.delta]
  refine root_charOf _ _ ?_ x
  have : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
    ext σ
    cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
  rw [this]
  exact D.ntw.delta_open i

theorem conjFun_gen {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)}
    {ph : Fin D.R.m → ℂ} {j : Fin D.R.m} {B : Base (Vc D j) (Wc D j)} {ψ ψ' : Twist D Circle}
    (hn : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) (H : HasTuples T R κ v₀ O ph j B ψ ψ') (hB : B.Good) {ω : PairRep (Vc D j) (Wc D j)}
    (hω : B.IsWeil 1 ω) (hψ : ψ.Good) (hψ' : ψ'.Good) (hQ : B.admitted ψ.Q) (hQ' : B.admitted ψ'.Q)
    (hδ : ∀ s, IsRoot1 ((B.de.chi s : Circle) : ℂ)) (hr : ∀ s, IsRoot1 ((ψ'.chi s : Circle) : ℂ))
    {c : VsV D j ℂ →ₗ[ℂ] (R.cV j).W} {u : ∀ ρ, lowT (R.MW j (sg0 D A)) ρ} (hc : ExtC R j (inC (O j).c') (O j).c0' c)
    (hu : ∀ ρ, (u ρ : (R.MW j (sg0 D A)).sm ρ) = v₀ j (sg0 D A) ρ) {τ : ℂ ≃+* ℂ} (h1 : FixBase T R j τ) (h2 : FixDat B τ)
    (h3 : ConjChar τ ψ ψ') {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j)) {x x' : VsV D j ℂ} (hx : ConjVec j τ x x') :
    ∃ ζ : ℂ, IsRoot1 ζ ∧ ConjFun (O j) (κ j) τ ζ (ph j • B.gen ω ψ h (R.ioP j (PiTensorProduct.tprod ℂ u) (c x)))
      (ph j • B.gen ω ψ' h (R.ioP j (PiTensorProduct.tprod ℂ u) (c x'))) := by
  obtain ⟨T0', A', R', F', v₀', O', k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, t, t', ht, ht'⟩ := H
  obtain ⟨c', u', hc', hu', hio⟩ := k11 c u hc hu
  obtain ⟨ζ0, hζ0, K⟩ := GlobalTheory.ConjGen.conj_gen GlobalTheory.chartIndependence_unconditional D G Pl0 T0' A' T R' F' κ v₀' O' ph hn k1 k2 k3 k4 k5
    j k6 k7 c' hc' u' hu' B hB k8 ω hω τ (k9 τ h1) h2
  obtain ⟨s, hs, -⟩ := K ψ ψ' t t' hψ hψ' hQ hQ' ht ht' h3
  have hξ : IsRoot1 ((R'.xi t' s : Circle) : ℂ) := by
    rw [ht'.1, MonoidHom.mul_apply, Circle.coe_mul]
    exact root_mul (hδ s) (hr s)
  refine ⟨_, root_mul hζ0 hξ, k10 _ _ _ _ ?_⟩
  rw [← hio, ← hio]
  exact hs h hh x x' hx

theorem smul_apply_of {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (L : M →ₗ[ℂ] N) {ν a b : ℂ} {P Q : M}
    (h : ν • P = (a * b) • Q) : ν • L P = a • b • L Q := by
  rw [← map_smul, h, map_smul, mul_smul]

theorem rescale {X : Type} (τ : ℂ ≃+* ℂ) {ξ ζ : ℂ} (hξ : ξ ≠ 0) {Φ Φ' Ψ Ψ' : X → ℂ} (h : Ψ = ξ • Φ) (h' : Ψ' = ξ • Φ') {n : ℕ}
    {b : Fin n → ℂ} {f : Fin n → X → ℂ} (e1 : Φ = ∑ l, b l • f l) (e2 : ∑ l, τ (b l) • f l = fun x => ζ⁻¹ * Φ' x) :
    Ψ = ∑ l, (ξ * b l) • f l ∧ ∑ l, τ (ξ * b l) • f l = (τ ξ * ζ⁻¹ * ξ⁻¹) • Ψ' := by
  constructor
  · rw [h, e1, Finset.smul_sum]
    simp only [smul_smul]
  · have e3 : ∑ l, τ (ξ * b l) • f l = τ ξ • ∑ l, τ (b l) • f l := by
      simp only [map_mul, Finset.smul_sum, smul_smul]
    rw [e3, e2, h', smul_smul, inv_mul_cancel_right₀ hξ, mul_smul]
    rfl

end GlobalTheory.BigOn.Exp.TwConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionClosedFibreOfPulledBackIso
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PotIso

open GlobalTheory.KS GlobalTheory.KS.AdjDlog

theorem constFn_mul_c {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) (W : Y.Opens) (a b : R) :
    constFn q W (a * b) = constFn q W a * constFn q W b := by
  simp only [constFn, map_mul]

theorem constFn_one_c {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) (W : Y.Opens) :
    constFn q W 1 = 1 := by
  simp only [constFn, map_one]

theorem constFn_zero_c {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) (W : Y.Opens) :
    constFn q W 0 = 0 := by
  simp only [constFn, map_zero]

theorem constFn_comp_spMap_c {R S : Type} [CommRing R] [CommRing S] {Y : Scheme.{0}} (q : Y ⟶ Sp S) (x : R →+* S)
    (W : Y.Opens) (t : R) : constFn (q ≫ spMap x) W t = constFn q W (x t) := by
  have e1 : (q ≫ spMap x).appLE ⊤ W le_top = (spMap x).appLE ⊤ ⊤ le_top ≫ q.appLE ⊤ W le_top :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have h2 := congrArg (fun k => k.hom t) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom x))
  change ((q ≫ spMap x).appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t) =
    (q.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (x t))
  rw [e1, CommRingCat.comp_apply]
  congr 1
  simp only [CommRingCat.comp_apply] at h2
  exact h2.symm

theorem pull_g_val {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (j j' : PUnit → L.ι) {O : Y.Opens}
    (h : O ≤ (L.pull f).U j ⊓ (L.pull f).U j') :
    (res h ((L.pull f).g j j')).val = pbT f (L.g (j PUnit.unit) (j' PUnit.unit)).val O := by
  have le : O ≤ f ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) :=
    le_inf ((h.trans inf_le_left).trans (LB.wchart_le L _ j PUnit.unit))
      ((h.trans inf_le_right).trans (LB.wchart_le L _ j' PUnit.unit))
  have e : res h ((L.pull f).g j j') = res le (pullU f _ (L.g (j PUnit.unit) (j' PUnit.unit))) := by
    show res h (∏ k : PUnit, _) = _
    erw [Fintype.prod_unique, zpow_one, res_res']
    rfl
  rw [e, val_res_pullU]

theorem isPullback_pr {k R : Type} [Field k] [CommRing R] (ρ : R →+* DualNumber k) {A B' A₀ : Scheme.{0}}
    (pA : A ⟶ Sp R) (pB : B' ⟶ Sp (DualNumber k)) (p₀ : A₀ ⟶ Sp k) (π₂ : B' ⟶ A) (m₀ : A₀ ⟶ A) (pr : B' ⟶ A₀)
    (h₂ : IsPullback π₂ pB pA (spMap (constHom ρ)))
    (hm : IsPullback m₀ p₀ pA (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)))
    (hpr : pr ≫ m₀ = π₂) (hprb : pr ≫ p₀ = pB ≫ spMap (algebraMap k (DualNumber k))) :
    IsPullback pr pB p₀ (spMap (algebraMap k (DualNumber k))) := by
  refine IsPullback.of_right ?_ hprb hm
  have e : spMap (constHom ρ) = spMap (algebraMap k (DualNumber k)) ≫
      spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) := by
    rw [← Spec.map_comp]; rfl
  rw [hpr, ← e]; exact h₂

theorem conn_of_iso : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι), ⨆ i, V i = ⊤ → (∀ i, V i ≤ P.L.U (jj i)) → ∀ d : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom P.A.hom m₀ (fun r => (ρ r).snd) ⊤ d → (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (d W f) (π₂ ⁻¹ᵁ W)) → ∀ w : LB.Iso (P.L.pull π₁) (P.L.pull π₂), w.IsGen → ∃ q : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i), GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun r => (ρ r).snd) V jj d q := by
  intro k _ R _ P ρ B' _ π₁ π₂ h₁ h₂ hfib A₀ _ m₀ hm₀ pr hpr hprb J V jj hV hVU d hd hdB w hw
  obtain ⟨a, b, hab⟩ := _root_.GlobalTheory.UnitPart.unitPart k R P ρ B' π₁ π₂ h₁ h₂ hfib A₀ m₀ hm₀ pr hpr hprb V jj hV hVU w hw
  have hpre : ∀ W : P.A.left.Opens, π₁ ⁻¹ᵁ W = π₂ ⁻¹ᵁ W := _root_.GlobalTheory.LogKS.preimage_eq_of_agree_closedFibre k P.A.left B'.left B'.hom π₁ π₂ hfib
  have hpb : IsPullback pr B'.hom A₀.hom (spMap (algebraMap k (DualNumber k))) :=
    GlobalTheory.PotIso.isPullback_pr ρ _ _ _ π₂ m₀ pr h₂.1 hm₀.1 hpr hprb
  have thick := _root_.GlobalTheory.EpsThick.existsUnique_add_eps_mul_of_field k A₀.left B'.left A₀.hom B'.hom pr hpb
  subst hpr
  refine ⟨fun i => constFn A₀.hom (m₀ ⁻¹ᵁ V i) ((a⁻¹ : kˣ) : k) * b i, hd, hV, hVU, fun i i' => ?_⟩
  have hW : V i ⊓ V i' ≤ P.L.U (jj i) ⊓ P.L.U (jj i') := inf_le_inf (hVU i) (hVU i')
  have hO₀ : m₀ ⁻¹ᵁ (V i ⊓ V i') ≤ m₀ ⁻¹ᵁ (P.L.U (jj i) ⊓ P.L.U (jj i')) := m₀.preimage_mono hW
  have hO : (pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i') ≤ pr ⁻¹ᵁ (m₀ ⁻¹ᵁ (V i ⊓ V i')) := le_rfl
  have hchart : ∀ l, (pr ≫ m₀) ⁻¹ᵁ V l ≤ (LB.div (P.L.pull (pr ≫ m₀)) (P.L.pull π₁)).U (fun _ => jj l, fun _ => jj l) := by
    intro l x hx
    refine ⟨Set.mem_iInter.2 fun _ => hVU l hx, Set.mem_iInter.2 fun _ => ?_⟩
    have : x ∈ π₁ ⁻¹ᵁ P.L.U (jj l) := by rw [hpre]; exact hVU l hx
    exact this
  have hM : (pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i') ≤ (P.L.pull (pr ≫ m₀)).U (fun _ => jj i) ⊓ (P.L.pull (pr ≫ m₀)).U (fun _ => jj i') :=
    fun x hx => ⟨(hchart i hx.1).1, (hchart i' hx.2).1⟩
  have hL : (pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i') ≤ (P.L.pull π₁).U (fun _ => jj i) ⊓ (P.L.pull π₁).U (fun _ => jj i') :=
    fun x hx => ⟨(hchart i hx.1).2, (hchart i' hx.2).2⟩
  have iso := iso_rel w hw (fun _ => jj i) (fun _ => jj i') (fun _ => jj i) (fun _ => jj i') hM hL
  rw [GlobalTheory.PotIso.pull_g_val, GlobalTheory.PotIso.pull_g_val] at iso
  have hs : ∀ l, V i ⊓ V i' ≤ V l → rsT (w.s (fun _ => jj l, fun _ => jj l)).val ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) =
      constFn B'.hom ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) (algebraMap k (DualNumber k) (a : k)) +
        constFn B'.hom ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) DualNumber.eps *
          pbT pr (rsT (b l) (m₀ ⁻¹ᵁ (V i ⊓ V i'))) ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) := by
    intro l hl
    have hl' : (pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i') ≤ (pr ≫ m₀) ⁻¹ᵁ V l := (pr ≫ m₀).preimage_mono hl
    rw [← rsT_rsT (hchart l) hl', hab l, rsT_add, rsT_mul, GlobalTheory.KS.rsT_constFn _ hl', GlobalTheory.KS.rsT_constFn _ hl',
      rsT_pbT pr (show (pr ≫ m₀) ⁻¹ᵁ V l ≤ pr ⁻¹ᵁ (m₀ ⁻¹ᵁ V l) from le_rfl) hl', pbT_rsT pr (m₀.preimage_mono hl) hO]
  have hA : constFn B'.hom ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) (algebraMap k (DualNumber k) (a : k)) =
      pbT pr (constFn A₀.hom (m₀ ⁻¹ᵁ (V i ⊓ V i')) (a : k)) ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) := by
    rw [GlobalTheory.KS.pbT_constFn A₀.hom pr hO, hprb, GlobalTheory.PotIso.constFn_comp_spMap_c]
  have hd' := hdB (V i ⊓ V i') (rsT (P.L.g (jj i) (jj i')).val (V i ⊓ V i'))
  rw [pbT_rsT π₁ hW (hpre _).ge, pbT_rsT (pr ≫ m₀) hW le_rfl, ← pbT_pbT pr m₀ hO₀ hO] at hd'
  rw [← pbT_pbT pr m₀ hO₀ hO, hd', hs i inf_le_left, hs i' inf_le_right, hA] at iso
  have hee : constFn B'.hom ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) DualNumber.eps *
      constFn B'.hom ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) DualNumber.eps = 0 := by
    rw [← GlobalTheory.PotIso.constFn_mul_c, DualNumber.eps_mul_eps, GlobalTheory.PotIso.constFn_zero_c]
  generalize d (V i ⊓ V i') (rsT (P.L.g (jj i) (jj i')).val (V i ⊓ V i')) = D at iso ⊢
  generalize pbT m₀ (P.L.g (jj i) (jj i')).val (m₀ ⁻¹ᵁ (V i ⊓ V i')) = g₀ at iso ⊢
  have key : constFn B'.hom ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) DualNumber.eps *
      pbT pr (constFn A₀.hom (m₀ ⁻¹ᵁ (V i ⊓ V i')) (a : k) * D) ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) =
      constFn B'.hom ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) DualNumber.eps *
      pbT pr (g₀ * (rsT (b i') (m₀ ⁻¹ᵁ (V i ⊓ V i')) - rsT (b i) (m₀ ⁻¹ᵁ (V i ⊓ V i'))))
        ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) := by
    rw [pbT_mul, pbT_mul, pbT_sub]
    linear_combination iso - (pbT pr (rsT (b i) (m₀ ⁻¹ᵁ (V i ⊓ V i'))) ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i')) *
      pbT pr D ((pr ≫ m₀) ⁻¹ᵁ (V i ⊓ V i'))) * hee
  obtain ⟨_, _, huniq⟩ := thick (m₀ ⁻¹ᵁ (V i ⊓ V i'))
    (constFn B'.hom (pr ⁻¹ᵁ (m₀ ⁻¹ᵁ (V i ⊓ V i'))) DualNumber.eps *
      pbT pr (constFn A₀.hom (m₀ ⁻¹ᵁ (V i ⊓ V i')) (a : k) * D) (pr ⁻¹ᵁ (m₀ ⁻¹ᵁ (V i ⊓ V i'))))
  have u₁ := huniq (0, constFn A₀.hom (m₀ ⁻¹ᵁ (V i ⊓ V i')) (a : k) * D) (by
    simp only [map_zero, zero_add, app_eq_pbT])
  have u₂ := huniq (0, g₀ * (rsT (b i') (m₀ ⁻¹ᵁ (V i ⊓ V i')) - rsT (b i) (m₀ ⁻¹ᵁ (V i ⊓ V i')))) (by
    simp only [map_zero, zero_add, app_eq_pbT]; exact key)
  have hX := congrArg Prod.snd (u₁.trans u₂.symm)
  simp only at hX
  have hc : constFn A₀.hom (m₀ ⁻¹ᵁ (V i ⊓ V i')) ((a⁻¹ : kˣ) : k) * constFn A₀.hom (m₀ ⁻¹ᵁ (V i ⊓ V i')) (a : k) = 1 := by
    rw [← GlobalTheory.PotIso.constFn_mul_c, Units.inv_mul, GlobalTheory.PotIso.constFn_one_c]
  show D = g₀ * (rsT (constFn A₀.hom (m₀ ⁻¹ᵁ V i') ((a⁻¹ : kˣ) : k) * b i') (m₀ ⁻¹ᵁ (V i ⊓ V i')) -
    rsT (constFn A₀.hom (m₀ ⁻¹ᵁ V i) ((a⁻¹ : kˣ) : k) * b i) (m₀ ⁻¹ᵁ (V i ⊓ V i')))
  rw [rsT_mul, rsT_mul, GlobalTheory.KS.rsT_constFn _ (m₀.preimage_mono inf_le_right),
    GlobalTheory.KS.rsT_constFn _ (m₀.preimage_mono inf_le_left)]
  linear_combination constFn A₀.hom (m₀ ⁻¹ᵁ (V i ⊓ V i')) ((a⁻¹ : kˣ) : k) * hX - D * hc

end GlobalTheory.PotIso
end
end

