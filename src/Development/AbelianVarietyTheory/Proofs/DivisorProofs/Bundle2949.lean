module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativesCoboundaryCoeffsMemMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0533
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2806
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2666
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeOfSmallTraits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2438
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesian
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BetaAtClosedPoint
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2725

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorEqZeroOfLogDerivCoboundary
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LieRigid

open GlobalTheory.ZH.CrdCalc (valR_res valR_spMap valR_eq valHom)

theorem dlg_sub {A : Type} [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left)
    (δ : Fld B.left) (hδ : IsField ⊤ δ) (i j : L.ι) {O T : B.left.Opens} (hO : O ≤ L.U i ⊓ L.U j) (hT : T ≤ O) :
    rsT (dlg B (𝟙 _) L δ i j O) T = rsT (dlg B (𝟙 _) L δ i j (L.U i ⊓ L.U j)) T := by
  rw [GlobalTheory.CoverRefinementPullback.dlg_res' B L δ hδ i j (hT.trans hO)]
  unfold dlg
  rw [GlobalTheory.KS.rsT_of_le hT, map_mul, GlobalTheory.CoverRefinementPullback.pbT_id' _ hO, GlobalTheory.CoverRefinementPullback.pbT_id' _ hO, ← hδ.2.2 _ _ hT le_top,
    GlobalTheory.CoverRefinementPullback.resG_resG', GlobalTheory.CoverRefinementPullback.resG_resG']
  rfl

theorem lie_inj : ∀ (R : Type) [CommRing R] [IsLocalRing R] (P : PolAV (Sp R)) (w : TanM (𝟙 (Sp R)) P.A) (δ : Fld P.A.left), IsInv P.A w δ → ∀ (K : Type) (V : K → P.A.left.Opens) (jk : K → P.L.ι), ⨆ k, V k = ⊤ → (∀ k, V k ≤ P.L.U (jk k)) → ∀ (b : ∀ k, Γ(P.A.left, V k)), (∀ k k', rsT (b k') (V k ⊓ V k') - rsT (b k) (V k ⊓ V k') = dlg P.A (𝟙 _) P.L δ (jk k) (jk k') (V k ⊓ V k')) → w = 0 := by
  intro R _ _ P w δ hδ K V jk hV hVj b hb
  have hδ1 : IsField ⊤ δ := hδ.1
  have hcob : IsCob P.L.U (fun j j' => dlg P.A (𝟙 _) P.L δ j j' (P.L.U j ⊓ P.L.U j')) := by
    refine _root_.GlobalTheory.KS.isCob_of_mixed P.A.left P.L.ι K P.L.U V hV _
      (fun k k' => dlg P.A (𝟙 _) P.L δ (jk k) (jk k') (V k ⊓ V k'))
      (fun j k => rsT (dlg P.A (𝟙 _) P.L δ j (jk k) (P.L.U j ⊓ P.L.U (jk k))) (P.L.U j ⊓ V k))
      (fun j j' k => ?_) (fun j k k' => ?_) ⟨b, fun k k' => (hb k k').symm⟩
    · have t1 : P.L.U j ⊓ P.L.U j' ⊓ V k ≤ P.L.U j ⊓ P.L.U j' := inf_le_left
      have t2 : P.L.U j ⊓ P.L.U j' ⊓ V k ≤ P.L.U j ⊓ V k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
      have t3 : P.L.U j ⊓ P.L.U j' ⊓ V k ≤ P.L.U j' ⊓ V k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
      rw [GlobalTheory.KS.rsT_rsT (inf_le_inf le_rfl (hVj k)) t2, GlobalTheory.KS.rsT_rsT (inf_le_inf le_rfl (hVj k)) t3,
        ← GlobalTheory.CoverRefinementPullback.dlg_tri _ _ P.isLB δ hδ1 j j' (jk k) t1 (t3.trans (inf_le_inf le_rfl (hVj k)))
          (t2.trans (inf_le_inf le_rfl (hVj k)))]
      abel
    · have t1 : P.L.U j ⊓ V k ⊓ V k' ≤ V k ⊓ V k' := le_inf (inf_le_left.trans inf_le_right) inf_le_right
      have t2 : P.L.U j ⊓ V k ⊓ V k' ≤ P.L.U j ⊓ V k := inf_le_left
      have t3 : P.L.U j ⊓ V k ⊓ V k' ≤ P.L.U j ⊓ V k' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
      rw [dlg_sub _ _ δ hδ1 (jk k) (jk k') (inf_le_inf (hVj k) (hVj k')) t1,
        GlobalTheory.KS.rsT_rsT (inf_le_inf le_rfl (hVj k)) t2, GlobalTheory.KS.rsT_rsT (inf_le_inf le_rfl (hVj k')) t3,
        ← GlobalTheory.CoverRefinementPullback.dlg_tri _ _ P.isLB δ hδ1 j (jk k) (jk k')
          (t2.trans (inf_le_inf le_rfl (hVj k))) (t1.trans (inf_le_inf (hVj k) (hVj k')))
          (t3.trans (inf_le_inf le_rfl (hVj k')))]
      abel
  obtain ⟨H, hH⟩ := hcob

  have hgp := GlobalTheory.Heat.DlogIndep.isGrpPullback_self P.A
  obtain ⟨u, hu⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.push_surj hgp (tv w)
  have hul : u.left = (tv w).left := (Category.comp_id _).symm.trans (congrArg (fun q => q.left) hu)
  have hut : IsTangent u :=
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.isTangent_iff hgp _).2 (by rw [hu]; exact ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem _)
  have hee : ∀ (S : Type) [CommRing S] [Algebra R S] (φ : DualNumber R →ₐ[R] S),
      φ DualNumber.eps * φ DualNumber.eps = 0 := fun S _ _ φ => by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hφ : ∀ (S : Type) [CommRing S] [Algebra R S] (φ : DualNumber R →ₐ[R] S),
      (algOverHom φ ≫ u : algOver R S ⟶ P.A) = (Chart.spMap (SqZero.epsTo R (φ DualNumber.eps) (hee S φ)) ≫ u) := by
    intro S _ _ φ
    have e : φ = SqZero.epsTo R (φ DualNumber.eps) (hee S φ) := DualNumber.algHom_ext (by simp [SqZero.epsTo, SqZero.dualTo_apply])
    conv_lhs => rw [e]
    rfl
  have h1 : u = 1 := GlobalTheory.Heat.DlogIndep.eq_one_of_coboundary P.isLB P.ktriv (DualNumber.eps : DualNumber R)
    DualNumber.eps_mul_eps u (fun j => -H j)
    (fun S _ _ φ y U hU => by
      rw [hφ S φ]; exact (GlobalTheory.Heat.DlogIndep.valR_translate hul hut hδ _ (hee S φ) y U hU).1)
    (fun S _ _ φ y j j' hj hj' => by
      rw [hφ S φ]
      have hU : ⊤ ≤ y.left ⁻¹ᵁ (P.L.U j ⊓ P.L.U j') := fun p hp => ⟨hj hp, hj' hp⟩
      have e₁ := congrArg (valHom (R := S) y.left _ hU) (hH j j')
      have r₁ : valHom (R := S) y.left _ hU (rsT (H j) _) = valHom (R := S) y.left _ hj (H j) := by
        rw [rsT, dite_eq_left inf_le_left, ← valR_eq, ← valR_eq]
        exact valR_res _ _ hU _
      have r₂ : valHom (R := S) y.left _ hU (rsT (H j') _) = valHom (R := S) y.left _ hj' (H j') := by
        rw [rsT, dite_eq_left inf_le_right, ← valR_eq, ← valR_eq]
        exact valR_res _ _ hU _
      simp only [dlg, GlobalTheory.Heat.DlogIndep.pbT_id, map_sub, map_mul, r₁, r₂] at e₁
      have e₂ : valHom (R := S) y.left _ hU (P.L.g j j').val * valHom (R := S) y.left _ hU (P.L.g j j')⁻¹.val = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      refine ((GlobalTheory.Heat.DlogIndep.valR_translate hul hut hδ _ (hee S φ) y _ hU).2 _).trans ?_
      simp only [valR_eq (R := S) _ _ hU, valR_eq (R := S) _ _ hj, valR_eq (R := S) _ _ hj', map_neg]
      linear_combination (φ DualNumber.eps * valHom (R := S) y.left _ hU (P.L.g j j').val) * e₁ +
        (-(φ DualNumber.eps * valHom (R := S) y.left _ hU (δ _ (P.L.g j j').val))) * e₂)
  have h2 : tv w = tv (0 : TanM (𝟙 (Sp R)) P.A) := by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_zero, ← hu, h1, map_one]
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.tanM_ext h2

end GlobalTheory.LieRigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoLogSectionCountChangeOfMetric
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem exists_intBasis {K : Type} [Field K] [CharZero K] (Λ : AddSubgroup K) (hΛ : Λ.FG) :
    ∃ f : Fin (Module.finrank ℤ Λ) → K, LinearIndependent ℤ f ∧ AddSubgroup.closure (Set.range f) = Λ ∧
      ∀ i, f i ∈ Λ := by
  haveI : Module.Finite ℤ Λ := Module.Finite.iff_addGroup_fg.2 ((AddGroup.fg_iff_addSubgroup_fg Λ).2 hΛ)
  haveI : Module.Free ℤ Λ := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ Λ
  refine ⟨fun i => (b i : K), ?_, le_antisymm ?_ ?_, fun i => (b i).2⟩
  · exact b.linearIndependent.map' Λ.subtype.toIntLinearMap (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  · exact (AddSubgroup.closure_le _).2 (Set.range_subset_iff.2 fun i => (b i).2)
  · intro x hx
    have h := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    change _ = x at h
    rw [← h, AddSubmonoidClass.coe_finsetSum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [AddSubgroupClass.coe_zsmul]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self (f := fun i => (b i : K)) i)) _

theorem tendsto_logCount_sub_up : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p) (a : ℝ), P.L.SemiPos D → P.L.IsSelfInter a → ∀ Λ : ℕ → AddSubgroup X.functionField, GoodFam P D (gdeg P.L D / D.factorial) Λ → ∃ t₀ : ℝ, ∀ (u : SmFn p) (B a' : ℝ), 0 ≤ B → (∀ σ y, |u.u σ y| ≤ B) → (up P.L u).SemiPos D → (up P.L u).IsSelfInter a' → ∀ t : ℝ, t₀ + B ≤ t → Tendsto (fun m : ℕ => (Real.log ((ballIn (upperParabolic P u) (Λ m) m 1 (Real.exp (t * m))).ncard : ℝ) - Real.log ((ballIn P (Λ m) m 1 (Real.exp (t * m))).ncard : ℝ)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 ((a' - a) / (D + 1).factorial)) := by
  intro HA k _ X _ p D hX hS P a hP ha Λ hΛ
  obtain ⟨C, hC1, hCs⟩ := hΛ.small
  refine ⟨Real.log C + 1, ?_⟩
  intro u B a' hB hu hup ha' t ht
  have := hX.charZero
  haveI : CharZero X.functionField :=
    charZero_of_injective_ringHom (germ_injective_of_isIntegral X (U := ⊤) _ trivial)
  choose f hli hcl hmemΛ using fun m => exists_intBasis (Λ m) (hΛ.fg m)
  let ω : ∀ σ, VolDens p σ D := fun σ => Classical.choice (_root_.GlobalTheory.HSAmp.exists_volDens k X p D hX hS σ)
  have hmem : ∀ (m : ℕ) i, f m i ∈ P.H m 1 := fun m i => hΛ.le m (hmemΛ m i)
  have hmem' : ∀ (m : ℕ) i, f m i ∈ (upperParabolic P u).H m 1 := fun m i => by
    rw [(_root_.GlobalTheory.HSAmp.upAtPrime_groups_values_norms k X p P u m 1).1]; exact hmem m i
  have hC1' : 1 ≤ C * Real.exp B := one_le_mul_of_one_le_of_one_le hC1 (Real.one_le_exp hB)
  have hlog : Real.log (C * Real.exp B) = Real.log C + B := by
    rw [Real.log_mul (by positivity) (Real.exp_pos B).ne', Real.log_exp]
  have hs : ∀ m : ℕ, 1 ≤ m → AddSubgroup.closure (Set.range (f m)) ≤
      AddSubgroup.closure (ballIn P (AddSubgroup.closure (Set.range (f m))) m 1 (C ^ m)) := by
    intro m hm; rw [hcl m]; exact hCs m hm
  have hs' : ∀ m : ℕ, 1 ≤ m → AddSubgroup.closure (Set.range (f m)) ≤
      AddSubgroup.closure (ballIn (upperParabolic P u) (AddSubgroup.closure (Set.range (f m))) m 1 ((C * Real.exp B) ^ m)) := by
    intro m hm
    rw [hcl m]
    refine (hCs m hm).trans (AddSubgroup.closure_mono ?_)
    rintro x ⟨hx, hb⟩
    refine ⟨hx, fun σ y => ?_⟩
    rw [((_root_.GlobalTheory.HSAmp.upAtPrime_groups_values_norms k X p P u m 1).2.2 σ y x).2]
    have h0 : 0 ≤ P.nu m 1 σ y x := by rw [← norm_val]; exact norm_nonneg _
    rw [mul_pow, ← Real.exp_nat_mul]
    refine mul_le_mul (hb σ y) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (by positivity)
    have hu' := (abs_le.1 (hu σ y)).1
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left (neg_le.1 hu') hm0, mul_nonneg hm0 hB]
  have h1 := _root_.GlobalTheory.HSAmp.count_ball_asymp k X p D hX hS P hP ω _ f hmem hli _ hΛ.rank C hC1 hs t (by linarith)
  have h2 := _root_.GlobalTheory.HSAmp.count_ball_asymp k X p D hX hS (upperParabolic P u) hup ω _ f hmem' hli _ hΛ.rank (C * Real.exp B) hC1' hs' t
    (by rw [hlog]; linarith)
  have h3 := _root_.GlobalTheory.HSAmpDet.tendsto_logDet_gram_sub HA k X p D hX hS P hP ω _ f hmem hli hΛ.rank u a a' hup ha ha'
  simp only [hcl] at h1 h2
  have key := (h2.sub h1).add (h3.div_const 2)
  convert key using 1
  · funext m; ring
  · congr 1; ring

end GlobalTheory.HSAmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyFormulaNormalCoverRationalThetaConstants
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

section Moves

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S}

theorem hasTh_of_sabMap (mm : SABMap t' t f) (m : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S') {N : ℕ}
    (c : Fin N → K) :
    HasTh t'.G t'.PP.L t'.PP.rig m x c ↔ HasTh t.G t.PP.L t.PP.rig m (x ≫ f) c := by
  rw [hasTh_iff, hasTh_iff]
  exact _root_.GlobalTheory.UMin.ThMove.hasTh₂_move S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen S' t'.G t'.PP.L t'.PP.rig f mm.φ t'.PP.isLB
    t'.PP.rigGen mm.cart (GlobalTheory.ModelSum.lbIso_of_map mm) m m N N K x c c

theorem polFib_of_sabMap (mm : SABMap t' t f) (g : ℕ) {R : Type} [CommRing R] (x : Sp R ⟶ S') :
    PolFib t'.G t'.PP.L g x ↔ PolFib t.G t.PP.L g (x ≫ f) :=
  (_root_.GlobalTheory.UMin.FibMove.polFib_move S S' t.G t.PP.L t'.G t'.PP.L f mm.φ t.PP.isLB t'.PP.isLB mm.cart
    (GlobalTheory.ModelSum.lbIso_of_map mm) g R x).1

end Moves

end GlobalTheory.UMin

namespace GlobalTheory.UMin


open GlobalTheory.CechPic in
theorem key_on_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (Y : Model Xo c (RingHom.id c.F)) (g : Y.X ⟶ PSpace o n), Y.j ≫ g = f → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [Algebra c.F Ω] (M : RatModel c.F Ω) (π : M.Z ⟶ Y.X) (y : Sp Ω ⟶ Xo.XF c) (d : Fin (n + 1) → Ω), Geo.Tor.IsNormalScheme M.Z → M.pt ≫ π = y ≫ Y.j → HasTh Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (y ≫ pullback.fst _ _) d → LBIso ((lbPow ((ProjSpace.O1 o n).pull g) 8).pull π) ((lbPow (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) (4 * (n + 1).factorial)).pull π) := by
  intro E _ _ _ H Dw l Xo c o _ m n f hm hm3 hmu hn hf Y g hYg Ω _ _ _ M π y d hZ hpt hth
  obtain ⟨t, ⟨mt⟩⟩ := GlobalTheory.ModelSum.exists_pull π Y.t
  have hP : PCrd (M.pt ≫ (π ≫ g)) (symTup d) := by
    have h1 : M.pt ≫ (π ≫ g) = y ≫ f := by rw [← Category.assoc, hpt, Category.assoc, hYg]
    rw [h1]; exact hf Ω y d hth
  have hD : M.HasDiv d :=
    _root_.GlobalTheory.UMin.hasDiv_of_hasDiv_symTup c.F Ω M (n + 1) d hZ (_root_.GlobalTheory.UMin.hasDiv_of_pCrd_pt c.F Ω o M n (π ≫ g) (symTup d) hP)
  obtain ⟨h, -, hhP⟩ := _root_.GlobalTheory.UMin.CrdMap.exists_map_of_hasDiv c.F Ω M n d hD
  have hsym := _root_.GlobalTheory.UMin.CrdSym.lbIso_symTup c.F Ω o M n h (π ≫ g) d hhP hP
  have hThO : HasTh Y.oF.t.G Y.oF.t.PP.L Y.oF.t.PP.rig m y d := (hasTh_of_sabMap Y.m0.toSABMap m y d).2 hth
  have hThY : HasTh Y.t.G Y.t.PP.L Y.t.PP.rig m (M.pt ≫ π) d := by
    rw [hpt]; exact (hasTh_of_sabMap Y.m m y d).1 hThO
  have hTh : HasTh t.G t.PP.L t.PP.rig m M.pt d := (hasTh_of_sabMap mt m M.pt d).2 hThY
  have hPolO : PolFib Y.oF.t.G Y.oF.t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) y :=
    (polFib_of_sabMap Y.m0.toSABMap _ y).2 (_root_.GlobalTheory.UMin.polFib_univ E H Dw l Xo c Ω _)
  have hPolY : PolFib Y.t.G Y.t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) (M.pt ≫ π) := by
    rw [hpt]; exact (polFib_of_sabMap Y.m _ y).1 hPolO
  have hPol : PolFib t.G t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) M.pt := (polFib_of_sabMap mt _ M.pt).2 hPolY
  have hmk : IsUnit (m : c.F) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (by omega))
  obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.UMin.ThBdl.pull_theta_bundle E H c.F Ω M t _ m n d h hZ hm hm3 hmk hPol hTh hhP
  obtain ⟨hab, hop, hamp⟩ := _root_.GlobalTheory.ModelAbLocus.abLocus_eq_and_pol E H Dw l Xo c Y M.Z π t ⟨mt⟩
  obtain ⟨hsmY, hvY⟩ := _root_.GlobalTheory.ModelRelDim.relDim_and_isVB_omega E H Dw l Xo c Y
  have hsm : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) t.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback mt.cart.1 hsmY
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have hne : ((⊤ : M.Z.Opens) : Set M.Z).Nonempty := ⟨M.pt (IsLocalRing.closedPoint Ω), trivial⟩
  haveI : CharZero Γ(M.Z, ⊤) := (M.res ⊤ hne).charZero
  have hne2 : (abLocus t.G).Nonempty := by
    refine ⟨M.pt (IsLocalRing.closedPoint Ω), ?_⟩
    rw [hab]
    show π (M.pt (IsLocalRing.closedPoint Ω)) ∈ Set.range Y.j
    have hq := congrArg (fun φ : Sp Ω ⟶ Y.X => φ (IsLocalRing.closedPoint Ω)) hpt
    exact ⟨y (IsLocalRing.closedPoint Ω), hq.symm⟩
  have hδ : ((ProjSpace.O1 c.F n).pull h).IsLB := pull_isLB (ProjSpace.O1_isLB c.F n) h
  have := Y.t.semi.separated
  have hHY := hvY.isLB_det
  have hHt := (GlobalTheory.LieVB.isVB_omega_of_isGrpPullback mt.cart hvY).isLB_det
  have hkey : LBIso (lbPow ((ProjSpace.O1 c.F n).pull h) 8)
      (lbPow (GlobalTheory.SiegelTor.hodge t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) 4) := by
    rcases Nat.eq_zero_or_pos (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) with h0 | h0
    · have hn0 : n = 0 := by
        rw [h0] at hn
        simpa using hn
      subst hn0
      refine (cls_eq_iff (isLB_lbPow hδ 8) (isLB_lbPow hHt 4)).1 ?_
      have hz : cls _ hHt = 0 := by
        revert hHt
        rw [h0]
        exact fun hHt => KeySmall.cls_det_zero _ hHt
      have ho : cls _ (ProjSpace.O1_isLB c.F 0) = 0 := by
        let L := ProjSpace.O1 c.F 0
        have hL := ProjSpace.O1_isLB c.F 0
        have h : L.U (0 : Fin 1) = ⊤ := top_le_iff.1 fun x _ => by
          obtain ⟨i, hi⟩ := Semi.LB.mem_of_cover hL x
          obtain rfl : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
          exact hi
        have le : ∀ j, L.U j ≤ L.U j ⊓ L.U (0 : Fin 1) := fun j => le_inf le_rfl (h ▸ le_top)
        have hm : ∀ y : PSpace c.F 0, y ∈ L.U (0 : Fin 1) := fun y => h ▸ TopologicalSpace.Opens.mem_top y
        exact (cls_eq_zero_iff hL).2 ⟨⟨fun j => res (le j) (L.g j (0 : Fin 1))⟩, fun i j => unit_ext fun y hy => by
          rw [map_mul, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy.1, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy.2]
          exact (gm_cocycle hL (𝟙 _) y hy.1 hy.2 (hm y)).symm⟩
      rw [cls_lbPow hδ, cls_lbPow hHt, hz, cls_pull (ProjSpace.O1_isLB c.F 0), ho, map_zero,
        nsmul_zero, nsmul_zero]
    · refine KeySmall.key_sab M.Z t _ _ σ h0 hZ inferInstance inferInstance (fun A _ ξ hξ => ?_) hsm hne2 hop hδ hamp
        (KeySmall.nzFib_of_geom σ hσ)
      exact KeySmall.mk_le_of_lft ((Cardinal.mk_le_of_injective (f := fun a : c.F => (a : ℂ)) Subtype.val_injective).trans_eq
        Cardinal.mk_complex) (ξ ≫ M.s)
  have hO := ProjSpace.O1_isLB o n
  have e1 := (cls_eq_iff (pull_isLB hO (π ≫ g)) (isLB_lbPow hδ _)).2 hsym
  have e2 := (cls_eq_iff (isLB_lbPow hδ 8) (isLB_lbPow hHt 4)).2 hkey
  have hHiso : LBIso ((GlobalTheory.SiegelTor.hodge Y.t.G _).pull π) (GlobalTheory.SiegelTor.hodge t.G _) :=
    (hvY.lbIso_det_pullback π).trans (pull_isLB hvY.isLB_det π) (hvY.pullback π).isLB_det
      (GlobalTheory.LieVB.isVB_omega_of_isGrpPullback mt.cart hvY).isLB_det
      ((hvY.pullback π).lbIso_det_of_iso (asIso (GlobalTheory.LieVB.omegaBase mt.cart)))
  have e3 := (cls_eq_iff (pull_isLB hHY π) hHt).2 hHiso
  rw [cls_pull hO, pull_comp, cls_lbPow hδ] at e1
  rw [cls_lbPow hδ, cls_lbPow hHt] at e2
  rw [cls_pull hHY] at e3
  refine (cls_eq_iff (pull_isLB (isLB_lbPow (pull_isLB hO g) 8) π) (pull_isLB (isLB_lbPow hHY _) π)).1 ?_
  rw [cls_pull (isLB_lbPow (pull_isLB hO g) 8), cls_pull (isLB_lbPow hHY _), cls_lbPow (pull_isLB hO g),
    cls_lbPow hHY, map_nsmul, map_nsmul, cls_pull hO, e1, e3, smul_smul, mul_comm 8, ← smul_smul, e2, smul_smul,
    mul_comm]

end GlobalTheory.UMin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToUnitTKLeft
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DDataGens

theorem toUnit_TK_left (R : Type) [CommRing R] [IsDomain R] : (toUnit (TK R)).left = jK R := by
  have := Over.w (toUnit (TK R))
  simpa using this

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → (∀ y, PsiUnitOn D y Set.univ) →
    ∃ τ₀ : GlobalTheory.UChart.Gens D, ∀ a b, (τ₀ a b).IsGen ∧ ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι),
      Good D.P.L z J → val (D.tau a b) (𝟙 _) z J = val (τ₀ a b) (toUnit (TK R)).left z J := by
  intro R _ _ D hB hU
  choose t ht hc using fun y => (GlobalTheory.ArcPull.psiUnitOn_univ_iff D y).1 (hU y)
  have key : ∀ a b, ∃ g : LB.Gen (LB.LinComb D.P.L (K := Fin 4)
      ![(D.c (a + b)).left, (D.c a).left, (D.c b).left, (D.c 0).left] ![-1, 1, 1, -1]), g.IsGen ∧
      ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        val g (toUnit (TK R)).left z J = val (t (a + b)) (toUnit (TK R)).left z J *
          (val (t a) (toUnit (TK R)).left z J)⁻¹ * (val (t b) (toUnit (TK R)).left z J)⁻¹ *
          val (t 0) (toUnit (TK R)).left z J := by
    intro a b
    let T := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (t (a + b))
      (LB.invGen D.P.L _ _ (t a))) (LB.invGen D.P.L _ _ (t b))) (t 0)
    have hT : T.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (ht _) (DVR.invGen_isGen _ _ _ _ (ht _)))
      (DVR.invGen_isGen _ _ _ _ (ht _))) (ht _)
    obtain ⟨g, hg, hv⟩ := exists_gen D.P.isLB
      (φ' := ![(D.c (a + b)).left, (D.c a).left, (D.c b).left, (D.c 0).left]) (ε' := ![-1, 1, 1, -1])
      (by
        intro U _ h
        simp [Fintype.prod_sum_type, Fin.prod_univ_four]) T hT
    refine ⟨g, hg, fun z J hJ => ?_⟩
    rw [hv _ _ z J hJ]
    simp only [T, val_mul hJ, val_inv]
  choose τ₀ hτ hv using key
  refine ⟨τ₀, fun a b => ⟨hτ a b, fun z J hJ => ?_⟩⟩
  have hp : ∀ y, val (t y) (toUnit (TK R)).left z J = val (D.psi y) (𝟙 _) z J := fun y => by
    rw [← val_corr hJ (hc y) (𝟙 _), val_pull hJ, Category.id_comp, toUnit_TK_left]
  have vρ : val D.rigK (𝟙 _) z J = val D.rig (jK R) z J := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp, toUnit_TK_left]
  rw [hv a b z J hJ, hp, hp, hp, hp, GlobalTheory.PsiZero.val_psi_zero hB hJ]
  simp only [DegPre.tau, val_mul hJ, val_inv, vρ]

end GlobalTheory.DDataGens
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionGaloisFixedCanonicalNDividedFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.CanonTors

theorem galois_fixed : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), Canon Q G P → ∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (x : Over.mk (spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ jK R) ⟶ G), x ^ n = 1 → spMap σ.toAlgHom.toRingHom ≫ x.left = x.left := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n hCN hn hnu ζ hζ Q e hD hQ G _ _ P hC σ x hx
  obtain ⟨-, D', F, A', G', _, _, U', oA, oG, inc, pr, hG', hlin, hinc, hpr, hip, hpi, -⟩ := hC
  haveI : CharZero R := hCN.2.2.2
  have hadm : AdmBase R (maximalIdeal R) := ⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩
  obtain ⟨y, hy0⟩ : ∃ y : (Over.map (jK R)).obj (TFK (R := R) (AlgebraicClosure (FractionRing R))) ⟶ G', y = x ≫ inc := ⟨_, rfl⟩
  obtain ⟨h, hh0⟩ : ∃ h : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ (Over.pullback (jK R)).obj G',
    h = (Over.mapPullbackAdj (jK R)).unit.app _ ≫ (Over.pullback (jK R)).map y := ⟨_, rfl⟩
  have hy : y ^ n = 1 := by
    rw [hy0, ← MonObj.pow_comp, hx, MonObj.one_comp]
  have hmp : ∀ m : ℕ, (Over.pullback (jK R)).map (y ^ m) = ((Over.pullback (jK R)).map y) ^ m := by
    intro m
    induction m with
    | zero => simp [Functor.map_one]
    | succ m ih => rw [pow_succ, Functor.map_mul, ih, pow_succ]
  have hh : h ^ n = 1 := by
    rw [hh0, ← MonObj.comp_pow, ← hmp, hy, Functor.map_one, MonObj.comp_one]
  haveI := U'.gen_hom
  obtain ⟨a, ha0⟩ : ∃ a : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A'.A, a = h ≫ U'.gen.hom := ⟨_, rfl⟩
  have ha : a ^ n = 1 := by
    rw [ha0, ← MonObj.pow_comp, hh, MonObj.one_comp]
  have hye : y ≫ oG.act F.e = y := by
    rw [hy0, ← hpi, Category.assoc, ← Category.assoc inc, hip, Category.id_comp]
  have hae : a ≫ oA.act F.e = a := by
    rw [ha0, Category.assoc, ← hlin.ext, hh0]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, hye]
  obtain ⟨f, hT, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hadm D' A' G' hG' U'
    (AlgebraicClosure (FractionRing R)) n hn
  obtain ⟨p, hp⟩ := hT.2.1 a ha
  obtain ⟨p₁, hy₁, hg₁, he₁⟩ := GlobalTheory.T.exists_equivalent_idempotent_image_fixed_torsion R hCN n hn hnu Q D' F A' G' U' oA oG hG' hlin a ha hae p ((hT.1 p a).2 hp.symm)
  have hf₁ : f p₁ = a := ((hT.2.2.1 p₁ p).2 he₁).trans hp
  obtain ⟨⟨p₁', hext⟩, hpt, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hadm D' A' G' hG' U'
    (AlgebraicClosure (FractionRing R)) (AlgebraicClosure (FractionRing R)) σ.toAlgHom n hn p₁
  obtain ⟨a', ha'⟩ := hpt a
  have h2 := (hiff p₁' a a' hext ha').1 ((hT.1 p₁ a).2 hf₁.symm)
  have heq := _root_.GlobalTheory.Mum.GalFixQ.eImage_equiv_conj T R iw s ε n hCN hn hnu ζ hζ Q e hD hQ D' F A' G' U' oA oG hG' hlin σ p p₁ p₁' hy₁ hg₁ hext
  have haa : a' = a := ((hT.1 p₁' a').1 h2).trans (((hT.2.2.1 p₁ p₁').2 heq).symm.trans hf₁)
  rw [haa] at ha'
  have e1 : (Over.mapPullbackAdj (jK R)).homEquiv _ _ y = h := by rw [Adjunction.homEquiv_unit, hh0]
  have hyl : y.left = h.left ≫ ((Over.mapPullbackAdj (jK R)).counit.app G').left := by
    have e2 : y = (Over.map (jK R)).map h ≫ (Over.mapPullbackAdj (jK R)).counit.app G' := by
      conv_lhs => rw [← ((Over.mapPullbackAdj (jK R)).homEquiv _ _).symm_apply_apply y, e1]
      exact Adjunction.homEquiv_counit _ _ _ _
    rw [e2, Over.comp_left]
    rfl
  have hhl : spMap σ.toAlgHom.toRingHom ≫ h.left = h.left := by
    have := congrArg (· ≫ U'.gen.inv.left) ha'
    simp only [ha0, Over.comp_left, Category.assoc] at this
    rw [← Over.comp_left _ _ _ U'.gen.hom U'.gen.inv, Iso.hom_inv_id, Over.id_left, Category.comp_id] at this
    exact this.symm
  have hyx : spMap σ.toAlgHom.toRingHom ≫ y.left = y.left := by
    rw [hyl, ← Category.assoc, hhl]
  have := congrArg (· ≫ pr.left) hyx
  simp only [hy0, Over.comp_left, Category.assoc] at this
  rw [← Over.comp_left _ _ _ inc pr, hip, Over.id_left, Category.comp_id] at this
  exact this
end GlobalTheory.Mum.CanonTors
end
end

