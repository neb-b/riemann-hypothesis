module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedCubicalSymmetricExtensionNormalB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCharts
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0142

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianSplitCubicalExtensionClosure
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.Assembly

theorem exists_sec_of_lbIso_pull {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB)
    (hL' : L'.IsLB) (H : LBIso L' (L.pull F)) (s : LB.Sec L) :
    ∃ s' : LB.Sec L', ∀ y : X', F y ∈ Out.nonzeroLocus s → y ∈ Out.nonzeroLocus s' := by
  obtain ⟨W, hW⟩ := H
  obtain ⟨s', hs'⟩ := sec_pull_down ((isGen_iff W).1 hW) hL hL' s
  refine ⟨s', fun y hy => ?_⟩
  obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ _).1 hy
  obtain ⟨k, hk⟩ := exists_chart hL' y
  have e := hs' _ (𝟙 _) y j k hj hk
  rw [Category.id_comp, gs_stalkMap F y _ hj] at e
  refine (mem_nonzeroLocus _ _).2 ⟨k, hk, ?_⟩
  exact isUnit_of_mul_isUnit_right ((congrArg IsUnit e).mp (u.map (F.stalkMap y).hom))

theorem mulN_eq_pow' {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) : mulN G n = (𝟙 G) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

theorem mulN_comm_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G]
    [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℕ) :
    (mulN G' n).left ≫ φ = φ ≫ (mulN G n).left := by
  have e := congrArg (fun q => q.left) (map_pow (pushHom h G') (𝟙 G') n)
  have e₂ : pushHom h G' (𝟙 G') ≫ mulN G n = pushHom h G' (𝟙 G') ^ n := by
    rw [mulN_eq_pow', MonObj.comp_pow, Category.comp_id]
  rw [← e₂, ← mulN_eq_pow'] at e
  refine Eq.trans e ?_
  change (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem exists_sec_fibres {H S : Scheme.{0}} (p : H ⟶ S) {L M : LB H} (hL : L.IsLB) (hM : M.IsLB) (z : S)
    (h₁ : ∃ N : S.Opens, z ∈ N ∧ LBIso (L.pull (p ⁻¹ᵁ N).ι) (M.pull (p ⁻¹ᵁ N).ι))
    (h₂ : ∃ (N : S.Opens) (σ : LB.Sec (M.pull (p ⁻¹ᵁ N).ι)), z ∈ N ∧
      ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, p ((p ⁻¹ᵁ N).ι x) = z') :
    ∃ (N : S.Opens) (σ : LB.Sec (L.pull (p ⁻¹ᵁ N).ι)), z ∈ N ∧
      ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, p ((p ⁻¹ᵁ N).ι x) = z' := by
  obtain ⟨N₁, hz₁, H₁⟩ := h₁
  obtain ⟨N₂, σ, hz₂, H₂⟩ := h₂
  have l₁ : p ⁻¹ᵁ (N₁ ⊓ N₂) ≤ p ⁻¹ᵁ N₁ := fun _ hx => hx.1
  have l₂ : p ⁻¹ᵁ (N₁ ⊓ N₂) ≤ p ⁻¹ᵁ N₂ := fun _ hx => hx.2
  have I : LBIso (L.pull (p ⁻¹ᵁ (N₁ ⊓ N₂)).ι) ((M.pull (p ⁻¹ᵁ N₂).ι).pull (H.homOfLE l₂)) :=
    H₁.chartPull (h := H.homOfLE l₁)
      (chartPullSame L _ _ _ _ fun _ => (H.homOfLE_ι l₁).symm)
      (chartPullLinComb M _ _ _ _ _ fun _ => (H.homOfLE_ι l₂).trans (H.homOfLE_ι l₁).symm)
  obtain ⟨σ', hσ'⟩ := exists_sec_of_lbIso_pull (pull_isLB hM _) (pull_isLB hL _) I σ
  refine ⟨N₁ ⊓ N₂, σ', ⟨hz₁, hz₂⟩, fun z' hz' => ?_⟩
  obtain ⟨x, hx, e⟩ := H₂ z' hz'.2
  have hm : x.1 ∈ p ⁻¹ᵁ (N₁ ⊓ N₂) := by
    change p x.1 ∈ N₁ ⊓ N₂
    exact (show p x.1 = z' from e) ▸ hz'
  refine ⟨⟨x.1, hm⟩, hσ' _ ?_, e⟩
  have : H.homOfLE l₂ ⟨x.1, hm⟩ = x := Subtype.ext (Scheme.homOfLE_apply l₂ _)
  rwa [this]

theorem exists_law_splitAll_cubical : Out.Laws → ∀ (C : Core) (T : C.Theta) (n : ℕ), C.HasTests → C.Indep → C.HasCharts → C.TorsSec n → T.Few n → ∃ L : C.Law, letI := L.grp; letI := L.comm; SplitAll C.GG ∧ IsSemiAbelian C.GG ∧ ∃ (PP : RigLB C.GG) (cub : CubicalStr C.GG PP) (m : CubeMap C.A C.GG), m.F = C.a ∧ m.e = C.U.ι ∧ m.IsPullCubical T.cub cub ∧ (T.L.IsSymmetric → PP.IsSymmetric) ∧ (∀ z : C.Z, ∃ (N : C.Z.Opens) (σ : LB.Sec (PP.L.pull (C.GG.hom ⁻¹ᵁ N).ι)), z ∈ N ∧ ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, C.GG.hom ((C.GG.hom ⁻¹ᵁ N).ι x) = z') ∧ ∀ z : C.Z, ∃ N : C.Z.Opens, z ∈ N ∧ LBIso (T.O₁.pull (C.GG.hom ⁻¹ᵁ N).ι) ((PP.L.pull (mulN C.GG T.m).left).pull (C.GG.hom ⁻¹ᵁ N).ι) := by
  intro hL C T n hT hI hC hS hF
  obtain ⟨L⟩ := Core.nonempty_law_of_hasTests_of_indep C hT hI
  refine ⟨L, ?_⟩
  letI := L.grp
  letI := L.comm
  obtain ⟨h₁, h₂⟩ := GlobalTheory.ZJ.FibreSplit.splitAll_and_isSemiAbelian C L hT hC
  obtain ⟨M, hM, hMa, hσ⟩ := GlobalTheory.T.exists_lineBundle_extension_thetaSection_semiAbelian hL.extend hL.mulN
    GlobalTheory.abelian_torsion_finite_and_mulN_surjective.2 C L T n h₂ hT hS hF
  obtain ⟨-, -, -, -, -, -, -, hcart, -, hN, -⟩ := GlobalTheory.ZJ.core_basic C
  have : Nonempty C.U.toScheme := C.ne.to_subtype
  have := h₂.smooth
  have := h₂.geomConnected
  have hgi : GeometricallyIntegral C.GG.hom := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ C.GG
  obtain ⟨PP, cub, m, hF, he, hp, hsym⟩ :=
    GlobalTheory.NormalCubeExt.exists_cubical_extension C.Z C.normal C.U.toScheme C.U.ι C.GG C.A C.a L.pull T.L T.cub M hM hMa
  have iso := _root_.GlobalTheory.lbIso_extend_of_normal C.Z C.normal C.U.toScheme C.G.toScheme C.A.left C.U.ι C.GG.hom C.e C.a C.A.hom
    h₂.smooth hgi C.e_sec hcart
  have hw : LBIso T.L.L (PP.L.pull C.a) := by
    obtain ⟨w, hw, -⟩ := hp
    exact hF ▸ ⟨w, hw⟩
  refine ⟨h₁, h₂, PP, cub, m, hF, he, hp, hsym, fun z => ?_, fun z => ?_⟩
  · refine exists_sec_fibres C.GG.hom PP.isLB hM z ((iso PP.L M PP.isLB hM ?_).2 z) (hσ z)
    exact (LBIso.trans (pull_isLB hM _) T.L.isLB (pull_isLB PP.isLB _) hMa hw).symm
  · refine (iso T.O₁ (PP.L.pull (mulN C.GG T.m).left) T.isLB (pull_isLB PP.isLB _) ?_).2 z
    have i₁ : LBIso (T.L.L.pull (mulN C.A T.m).left) ((PP.L.pull (mulN C.GG T.m).left).pull C.a) :=
      hw.chartPull (h := (mulN C.A T.m).left) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl)
        (chartPullLinComb PP.L _ _ _ _ _ fun _ => (mulN_comm_of_isGrpPullback L.pull T.m).symm)
    exact LBIso.trans (pull_isLB T.isLB _) (pull_isLB T.L.isLB _) (pull_isLB (pull_isLB PP.isLB _) _)
      (LBIso.symm ⟨T.w, T.w_gen⟩) i₁

end GlobalTheory.ZJ.Assembly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTraitSpecialisationOfMemClosureThetaPoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ThetaClosure
open GlobalTheory.ThetaCharts GlobalTheory.LevCover

theorem eval₂_smul {R K J : Type} [CommRing R] [CommRing K] (f : R →+* K) {G : MvPolynomial J R} {d : ℕ}
    (hG : G.IsHomogeneous d) (c : K) (v : J → K) :
    MvPolynomial.eval₂ f (c • v) G = c ^ d * MvPolynomial.eval₂ f v G := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h : ∑ i ∈ s.support, s i = d := by
    have := hG (MvPolynomial.mem_support_iff.1 hs)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h]
  ring

theorem exists_residue {W C : Type} [CommRing W] [IsDomain W] [IsLocalRing W] [NormedField C] [IsUltrametricDist C]
    [Algebra (FractionRing W) C] (h : CExt W (IsLocalRing.maximalIdeal W) C) :
    ∃ (S : ValuationSubring C) (κ : Type) (_ : Field κ) (_ : IsAlgClosed κ) (res : S →+* κ) (j : W →+* S),
      (∀ x, x ∈ S ↔ ‖x‖ ≤ 1) ∧ (∀ x : S, ‖(x : C)‖ < 1 → res x = 0) ∧
      ∀ w, (j w : C) = algebraMap (FractionRing W) C (algebraMap W _ w) := by
  let S := (NormedField.valuation (K := C)).valuationSubring
  have hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 := fun x => by
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
    exact Iff.rfl
  refine ⟨S, AlgebraicClosure (IsLocalRing.ResidueField S), inferInstance, inferInstance,
    (algebraMap _ _).comp (IsLocalRing.residue S),
    ((algebraMap (FractionRing W) C).comp (algebraMap W _)).codRestrict S.toSubring fun w => (hS _).2 (h.1 w), hS,
    fun x hx => ?_, fun _ => rfl⟩
  rw [RingHom.comp_apply, (IsLocalRing.residue_eq_zero_iff x).2, map_zero]
  rintro ⟨u, rfl⟩
  have e : ((u : S) : C) * ((u⁻¹ : Sˣ) : S) = 1 := congrArg (fun z : S => (z : C)) u.mul_inv
  have e' := congrArg norm e
  rw [norm_mul, norm_one] at e'
  have := (hS _).1 ((u⁻¹ : Sˣ) : S).2
  nlinarith [norm_nonneg ((u : S) : C), norm_nonneg (((u⁻¹ : Sˣ) : S) : C)]

theorem exists_lift_of_finite {F W : Type} [Field F] [Algebra ℚ F] [FiniteDimensional ℚ F] [CommRing W] [IsDomain W]
    [IsIntegrallyClosed W] [Algebra ℚ W] (g : F →+* FractionRing W) :
    ∃ b : F →+* W, (algebraMap W (FractionRing W)).comp b = g := by
  have hinj := IsFractionRing.injective W (FractionRing W)
  have hr : ∀ x, g x ∈ (algebraMap W (FractionRing W)).range := fun x => by
    have h1 : IsIntegral ℚ x := IsIntegral.of_finite ℚ x
    have h2 : IsIntegral W (g x) := h1.map_of_comp_eq (algebraMap ℚ W) g (Subsingleton.elim _ _)
    exact IsIntegrallyClosed.algebraMap_eq_of_integral h2
  let e := RingEquiv.ofBijective (algebraMap W (FractionRing W)).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  exact ⟨e.symm.toRingHom.comp (g.codRestrict _ hr), RingHom.ext fun x =>
    congrArg Subtype.val (e.apply_symm_apply (g.codRestrict _ hr x))⟩

theorem theta_iff (hL : Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {K : Type}
    [Field K] (o : Full D K) {m : ℕ} (hm : Odd m) {v v' : D.La → K} (hv : o.Theta m v) :
    o.Theta m v' ↔ ∃ c : Kˣ, v' = (c : K) • v := by
  haveI := o.closed
  haveI := o.charZero
  obtain ⟨-, h2, h3, -⟩ := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL K (Sp K) o.P (𝟙 _) m hm (Nat.cast_ne_zero.2 hm.pos.ne') D.La
    (o.I.ev (m ^ 2)) (fun a => (o.I.onto _ (pow_pos hm.pos 2) _).2 ⟨a, rfl⟩)
  exact (h3 v').trans (h2 1 v v' ((h3 v).1 hv))

theorem finiteType_of_qproj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsQProjOver f) :
    QuasiCompact f ∧ LocallyOfFiniteType f := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have := isProper_str R N
  exact ⟨inferInstance, inferInstance⟩

theorem exists_trait : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (m : ℕ) (ρ z : K) (v : D.La → K), Odd m → Compat H (m ^ 2) z ρ → v ≠ 0 → (∀ G, VanishC D m G → MvPolynomial.eval₂ (cf z ρ) v G = 0) → ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : CharZero C) (S : ValuationSubring C) (κ : Type) (_ : Field κ) (_ : IsAlgClosed κ) (res : S →+* κ) (i : K →+* κ) (o : Full D C) (_ : Mdl o) (v' : D.La → S) (r' z' : S), (∀ n : ℕ, 0 < n → ‖(n : C)‖ = 1) ∧ (∀ x, x ∈ S ↔ ‖x‖ ≤ 1) ∧ (∀ x : S, ‖(x : C)‖ < 1 → res x = 0) ∧ o.Theta m (fun x => v' x) ∧ (∀ x, res (v' x) = i (v x)) ∧ (r' : C) = o.ρ ∧ res r' = i ρ ∧ (z' : C) = o.I.ζ (m ^ 2) ∧ res z' = i z := by
  intro hV h6 hU hX hT hE hA E _ _ _ H D l Xo c W₀ Y K _ _ _ m ρ z v hm hc hv hvan
  letI := H.starRing
  have hL : Laws := hV.1.1
  have hN : 0 < m ^ 2 := pow_pos hm.pos 2
  haveI := c.fin
  have hζ : IsPrimitiveRoot (zeta (m ^ 2)) (m ^ 2) := Complex.isPrimitiveRoot_exp _ hN.ne'
  let L : IntermediateField c.F ℂ := IntermediateField.adjoin c.F {zeta (m ^ 2)}
  haveI : FiniteDimensional c.F L := IntermediateField.adjoin.finiteDimensional (hζ.isIntegral hN).tower_top
  let ξ₀ : L := ⟨zeta (m ^ 2), IntermediateField.mem_adjoin_simple_self _ _⟩
  have hξ₀ : IsPrimitiveRoot ξ₀ (m ^ 2) := IsPrimitiveRoot.of_map_of_injective (f := L.val.toRingHom) hζ
    Subtype.val_injective
  let ξ : Lˣ := (hξ₀.isUnit hN.ne').unit
  have hξ : IsPrimitiveRoot ξ (m ^ 2) := IsPrimitiveRoot.coe_units_iff.1 hξ₀
  let r₀ : c.F := IntermediateField.inclusion c.le (baseKA l).ρ
  obtain ⟨hqc, hlft⟩ := finiteType_of_qproj Xo.qproj
  obtain ⟨Ix, _, A, _, x, gam, J, _, q, w, hq, hft, hs, hcov, hpt⟩ := exists_charts (L := L) hL hV.1.2.1 Y.oF
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) hm hξ
  let χ₀ : MvPolynomial (Fin 2) ℤ →+* L := cf ξ₀ (algebraMap c.F L r₀)
  have hχ₀ : L.val.toRingHom.comp χ₀ = cf (zeta (m ^ 2)) H.rt0 := by
    refine MvPolynomial.ringHom_ext (fun n => by simp) fun i => ?_
    fin_cases i
    · simp [χ₀, ξ₀]
    · simp [χ₀]; rfl
  have key : ∀ (G : MvPolynomial D.La (MvPolynomial (Fin 2) ℤ)) (d : ℕ), G.IsHomogeneous d →
      (∀ i, MvPolynomial.eval₂ ((gam i).comp χ₀) (fun a => w i (q a)) G = 0) →
      MvPolynomial.eval₂ (cf z ρ) v G = 0 := fun G d hG h0 => by
    refine hvan G ⟨hm, ⟨d, hG⟩, fun o hρ hz u hu => ?_⟩
    obtain ⟨I', hI'⟩ := GlobalTheory.TateRoot.exists_tateIso_zeta_eq E H D l ℂ _ _ _ o.I l.A (zeta l.A) l.A_pos
      (Complex.isPrimitiveRoot_exp _ l.A_pos.ne')
    obtain ⟨y, ⟨hy, φ, h1, h2, h3, -⟩, -⟩ := (_root_.GlobalTheory.FullPoint.fullAt_existsUnique_exists_ext hV h6 hU hX hT hE hA E H D l Xo c W₀ Y ℂ c.F.val.toRingHom).1
      { o with I := I' } (fun r hr => hρ.trans hr.symm) (fun r hr => hI'.trans hr.symm)
    obtain ⟨i, f, hf, hth⟩ := hcov ℂ y o φ L.val.toRingHom ⟨h1, h2, h3⟩ hy hz
    obtain ⟨s, rfl⟩ := (theta_iff hL o hm hth).1 hu
    have e := congrArg f (h0 i)
    rw [MvPolynomial.eval₂_comp_left, ← RingHom.comp_assoc, hf, hχ₀, map_zero] at e
    rw [eval₂_smul _ hG]
    exact mul_eq_zero_of_right _ e
  let r := Function.surjInv hq
  have hr : ∀ j, q (r j) = j := Function.surjInv_eq hq
  have hvr : ∀ a, v (r (q a)) = v a := fun a => by
    have := key (MvPolynomial.X (r (q a)) - MvPolynomial.X a) 1
      ((MvPolynomial.isHomogeneous_X _ _).sub (MvPolynomial.isHomogeneous_X _ _)) fun i => by simp [hr]
    simpa [sub_eq_zero] using this
  letI : ∀ i, Algebra ℚ (A i) := fun i => (((gam i).comp (algebraMap c.F L)).comp (algebraMap ℚ c.F)).toAlgebra
  haveI := Fintype.ofFinite J
  obtain ⟨i, W, _, _, _, _, f, s, w', hW, hs0, hf, hw⟩ := _root_.GlobalTheory.cone_closure_arc_of_integral_image_reduction _root_.GlobalTheory.exists_complete_discreteValuationRing_of_mem_closure_cones _root_.GlobalTheory.exists_field_of_isIntegral_image _
    (cf (zeta (m ^ 2)) H.rt0) (fun p => by
      have h1 : IsIntegral ℤ H.rt0 := IsIntegral.of_pow two_pos (by
        rw [H.sqrt_neg_disc_sq]; exact (isIntegral_natCast H.d).neg)
      induction p using MvPolynomial.induction_on with
      | C a => simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := a)
      | add p p' hp hp' => rw [map_add (f := _)]; exact hp.add hp'
      | mul_X p i hp =>
        rw [map_mul]
        refine hp.mul ?_
        fin_cases i
        · simpa using hζ.isIntegral hN
        · simpa using h1)
    K J Ix (cf z ρ) hc A
    (fun i => (hft i).comp (RingHom.finite_algebraMap.2 (inferInstance : Module.Finite ℚ c.F)).finiteType)
    (fun i => (gam i).comp χ₀) (fun i p hp => by
      have : χ₀ p = 0 := Subtype.val_injective ((RingHom.congr_fun hχ₀ p).trans hp)
      rw [RingHom.comp_apply, this, map_zero])
    w (fun j => v (r j)) (fun h => hv (funext fun a => (hvr a).symm.trans (congrFun h (q a))))
    (fun G d hG h0 => by
      have := key (MvPolynomial.rename r G) d hG.rename_isHomogeneous fun i => by
        rw [MvPolynomial.eval₂_rename]
        simpa only [Function.comp_def, hr] using h0 i
      rwa [MvPolynomial.eval₂_rename] at this)
  haveI : CharZero W := charZero_of_injective_algebraMap (algebraMap K W).injective
  have hcdv : CDV W := ⟨inferInstance, hW, inferInstance⟩
  obtain ⟨C, _, _, _, _, _, g, hg, hext⟩ := GlobalTheory.Ex.exists_complete_isAlgClosed_cExt W (FractionRing W)
  have hg' : ∀ t, g t = algebraMap (FractionRing W) C t := hg
  haveI : CharZero C := charZero_of_injective_algebraMap (algebraMap (FractionRing W) C).injective
  obtain ⟨S, κ, _, _, res, j, hS, hres, hj⟩ := exists_residue hext
  letI : Algebra ℚ W := ((algebraMap K W).comp (algebraMap ℚ K)).toAlgebra
  obtain ⟨b, hb⟩ := exists_lift_of_finite (f.comp ((gam i).comp (algebraMap c.F L)))
  let bF : c.F →+* C := (g.comp f).comp ((gam i).comp (algebraMap c.F L))
  obtain ⟨o₁, ho₁⟩ := (_root_.GlobalTheory.FullPoint.fullAt_existsUnique_exists_ext hV h6 hU hX hT hE hA E H D l Xo c W₀ Y C bF).2.1 (spMap g ≫ spMap f ≫ x i)
  obtain ⟨M, -⟩ := GlobalTheory.T.moduli_model_ultrametric_points hV h6 hU hX hT hE hA E H D l Xo c W₀ Y C W hcdv hext (FractionRing W) g hg
    (spMap f ≫ x i) (b.comp (c.V W₀).subtype) (by
      rw [Model.j, Category.assoc Y.jQ, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, Category.assoc,
        ← Category.assoc (x i), hs, spMap_comp'', spMap_comp'', ← RingHom.comp_assoc, ← hb]
      refine Eq.trans ?_ (congrArg (spMap _ ≫ ·) (spMap_comp'' _ (algebraMap W (FractionRing W))).symm)
      rw [spMap_comp'']) o₁ ho₁
  rw [← Category.assoc, spMap_comp''] at ho₁
  obtain ⟨φ, h1, h2, h3, -⟩ := ho₁
  obtain ⟨hdet, -⟩ := Y.oF.geom C (𝟙 _ ≫ spMap (g.comp f) ≫ x i)
    (bF.comp (IntermediateField.inclusion c.le).toRingHom) (by
      rw [Category.id_comp, pullback.condition, Category.assoc, ← Category.assoc (x i), hs, spMap_comp'', spMap_comp''])
  let o₂ : Full D C :=
    { o₁ with
      ρ := bF r₀
      ρ_sq := by
        have := congrArg (bF.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ_sq
        rwa [map_pow, map_neg, map_natCast] at this
      det := fun τ => by
        have e := GlobalTheory.LiePull.lieMult_pull _ _ _ Y.oF.t.G o₁.P.A _ φ Y.oF.t.act (ofRingAct o₁.oa.toRingAct) h1 h3 C (𝟙 _) τ
        rw [e, e]
        exact hdet τ }
  obtain ⟨I', hI', hth⟩ := hpt i C (g.comp f) o₂ φ ⟨h1, h2, h3⟩
  have hjK : ∀ p, (j (algebraMap K W (cf z ρ p)) : C) = g (f (gam i (χ₀ p))) := fun p => by
    rw [hj, ← hg', ← hf]; rfl
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, S, κ, inferInstance,
    inferInstance, res, (res.comp j).comp (algebraMap K W), { o₂ with I := I' },
    { M with }, fun a => j (w' (q a)), j (algebraMap K W ρ), j (algebraMap K W z), fun n hn => ?_, hS, hres, ?_,
    fun a => ?_, ?_, rfl, ?_, rfl⟩
  · have h1 := hext.1 (algebraMap K W n)
    have h2 := hext.1 (algebraMap K W (n : K)⁻¹)
    have e : algebraMap (FractionRing W) C (algebraMap W _ (algebraMap K W n)) *
        algebraMap (FractionRing W) C (algebraMap W _ (algebraMap K W (n : K)⁻¹)) = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), map_one, map_one, map_one]
    have e' := congrArg norm e
    rw [norm_mul, norm_one] at e'
    rw [map_natCast, map_natCast, map_natCast] at e' h1
    nlinarith [norm_nonneg (n : C)]
  · refine (theta_iff hL _ hm hth).2 ⟨Units.mk0 (g s) ((map_ne_zero g).2 hs0), funext fun a => ?_⟩
    rw [hj, ← hg', (hw _).1, map_mul]
    rfl
  · have := hres (j (w' (q a) - algebraMap K W (v (r (q a))))) (by rw [hj]; exact hext.2 _ (hw _).2)
    rw [map_sub, map_sub, sub_eq_zero, hvr] at this
    exact this
  · have := hjK (MvPolynomial.X 1)
    simp only [χ₀, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at this
    exact this
  · have := hjK (MvPolynomial.X 0)
    simp only [χ₀, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at this
    exact this.trans hI'.symm

end GlobalTheory.ThetaClosure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FlatAndSurjectiveOfSurjectivePoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS


open UnramifiedEndFlat in
theorem flat_of_isDominant_grpHom (K : Type) [Field K] [IsAlgClosed K]
    (G G' : Over (Sp K)) [GrpObj G] [GrpObj G'] [IrreducibleSpace G.left] [IsIntegral G'.left]
    [LocallyOfFiniteType G.hom] [LocallyOfFiniteType G'.hom] (φ : G ⟶ G') [IsMonHom φ]
    [QuasiCompact φ.left] [IsDominant φ.left] : Flat φ.left := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  have : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  have : LocallyOfFiniteType (φ.left ≫ G'.hom) := by rw [Over.w φ]; infer_instance
  have : LocallyOfFiniteType φ.left := locallyOfFiniteType_of_comp _ G'.hom
  have hξ : φ.left (genericPoint G.left) = genericPoint G'.left := by
    have h := (genericPoint_spec G.left).image φ.left.continuous
    rw [Set.image_univ, φ.left.denseRange.closure_range] at h
    exact h.eq (genericPoint_spec G'.left)
  obtain ⟨W, hW, H⟩ := IntDiv.exists_open_flat φ.left hξ
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hW W.2.isLocallyClosed
  refine flat_of_closedPoints _ fun x hx => ?_
  let x' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2
  let y' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨y, hyc⟩).2
  let α := GrpObj.mulRight (A := G) (y'⁻¹ * x')
  let β := GrpObj.mulRight (A := G') ((y'⁻¹ * x') ≫ φ)
  have hαβ : α.hom ≫ φ = φ ≫ β.hom := by
    simp only [α, β]
    generalize y'⁻¹ * x' = z
    simp [comp_lift_assoc]
  have hα : y' ≫ α.hom = x' := by
    have : y' ≫ α.hom = y' * (y'⁻¹ * x') := by
      simp [α, comp_lift_assoc, Hom.mul_def]
    rw [this, mul_inv_cancel_left]
  have hα' : α.hom.left y = x := by
    have h := congr(($hα).left (IsLocalRing.closedPoint K))
    rw [← pointOfClosedPoint_apply G.hom x hx (IsLocalRing.closedPoint K),
      ← pointOfClosedPoint_apply G.hom y hyc (IsLocalRing.closedPoint K)]
    exact h
  have : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).map α.hom))
  have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  have h1 : ((φ.left ≫ β.hom.left).stalkMap y).hom.Flat := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (Flat.stalkMap β.hom.left _).comp (H y hy)
  rw [← Over.comp_left, ← hαβ, Over.comp_left, Scheme.Hom.stalkMap_comp] at h1
  rw [← hα']
  exact (RingHom.Flat.respectsIso.cancel_right_isIso
    (φ.left.stalkMap (α.hom.left y)) (α.hom.left.stalkMap y)).mp h1

theorem flat_and_surjective_of_surjective_points : ∀ (k : Type) [Field k] [IsAlgClosed k] (G G' : Over (Sp k)) [GrpObj G] [GrpObj G'], SmConn G → SmConn G' → ∀ i : G ⟶ G', IsMonHom i → (∀ y : (𝟙_ (Over (Sp k)) ⟶ G'), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ≫ i = y) → Flat i.left ∧ Surjective i.left := by
  intro k _ _ G G' _ _ ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ i _ hi
  have := grpObj_geometricallyIntegral_of_smooth _ G
  have := grpObj_geometricallyIntegral_of_smooth _ G'
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_subsingleton G.hom
  have : IsIntegral G'.left := GeometricallyIntegral.isIntegral_of_subsingleton G'.hom
  have : QuasiCompact (i.left ≫ G'.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact i.left := .of_comp _ G'.hom
  have : Surjective i.left := DivisiblePart.surjective_of_rationalPoints i hi
  exact ⟨flat_of_isDominant_grpHom k G G' i, this⟩

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemiAbelianReductionOfRetract
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

private theorem smConn_of_semiAbelian {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (hG : IsSemiAbelian G) : SmConn G := by
  obtain ⟨c, sm, se, qc, gc, -⟩ := hG
  exact ⟨c, sm, se, qc, gc⟩

theorem exists_semiAbelian_model_of_retract (W L : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L]
    (G : Over (Sp W)) [GrpObj G] (hG : IsSemiAbelian G) (C : Over (Sp L)) [GrpObj C]
    (a : C ⟶ (Over.pullback (spMap (algebraMap W L))).obj G)
    (b : (Over.pullback (spMap (algebraMap W L))).obj G ⟶ C) [IsMonHom a] [IsMonHom b]
    (hab : a ≫ b = 𝟙 C) :
    ∃ (G₁ : Over (Sp W)) (_ : GrpObj G₁), IsSemiAbelian G₁ ∧
      ∃ e : (Over.pullback (spMap (algebraMap W L))).obj G₁ ≅ C, IsMonHom e.hom := by

  obtain ⟨F, ⟨hF, hFe⟩, huniq⟩ :=
    GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W L G G hG hG (b ≫ a) inferInstance
  have hFF : F ≫ F = F := huniq (F ≫ F) ⟨inferInstance, by
    simp only [CategoryTheory.Functor.map_comp, hFe, Category.assoc, reassoc_of% hab]⟩

  obtain ⟨G₁, _, i, r, hSm₁, hi, hr, hir, hri⟩ :=
    _root_.GlobalTheory.SS.smConn_idempotent_splits (Sp W) G (smConn_of_semiAbelian G hG) F hF hFF
  have hG₁ : IsSemiAbelian G₁ := _root_.GlobalTheory.SS.isSemiAbelian_of_retract (Sp W) G G₁ hG hSm₁ i r hr hir
  subst hri

  refine ⟨G₁, inferInstance, hG₁,
    { hom := (Over.pullback (spMap (algebraMap W L))).map i ≫ b
      inv := a ≫ (Over.pullback (spMap (algebraMap W L))).map r
      hom_inv_id := ?_
      inv_hom_id := ?_ }, ?_⟩
  · calc ((Over.pullback (spMap (algebraMap W L))).map i ≫ b) ≫ a ≫ (Over.pullback (spMap (algebraMap W L))).map r = (Over.pullback (spMap (algebraMap W L))).map i ≫ (Over.pullback (spMap (algebraMap W L))).map (r ≫ i) ≫ (Over.pullback (spMap (algebraMap W L))).map r := by
          rw [hFe]; simp only [Category.assoc]
      _ = (Over.pullback (spMap (algebraMap W L))).map (i ≫ r ≫ i ≫ r) := by simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      _ = 𝟙 _ := by rw [reassoc_of% hir, hir, CategoryTheory.Functor.map_id]
  · calc (a ≫ (Over.pullback (spMap (algebraMap W L))).map r) ≫ (Over.pullback (spMap (algebraMap W L))).map i ≫ b = a ≫ (Over.pullback (spMap (algebraMap W L))).map (r ≫ i) ≫ b := by
          simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      _ = 𝟙 C := by rw [hFe, Category.assoc, reassoc_of% hab, hab]
  · show IsMonHom ((Over.pullback (spMap (algebraMap W L))).map i ≫ b)
    infer_instance

theorem potModel_semiAbelian_of_retract : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (B Q : Over (Sp K)) [GrpObj B] [GrpObj Q] (i : B ⟶ Q) (r : Q ⟶ B), IsMonHom i → IsMonHom r → i ≫ r = 𝟙 B → PotModel V K Q (fun _ _ _ G _ => IsSemiAbelian G) → PotModel V K B (fun _ _ _ G _ => IsSemiAbelian G) := by
  intro V K _ _ _ _ _ _ _ _ B Q _ _ i r hi hr hir hQ
  obtain ⟨W, L, _, _, _, _, _, _, _, _, hcomp, hfin, hloc, hcompl, G, _, ⟨e, he⟩, hG⟩ := hQ

  have hab : ((Over.pullback (spMap (algebraMap K L))).map i ≫ e.inv) ≫ e.hom ≫ (Over.pullback (spMap (algebraMap K L))).map r = 𝟙 ((Over.pullback (spMap (algebraMap K L))).obj B) := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← CategoryTheory.Functor.map_comp, hir, CategoryTheory.Functor.map_id]
  obtain ⟨G₁, _, hG₁, e₁, he₁⟩ :=
    exists_semiAbelian_model_of_retract W L G hG ((Over.pullback (spMap (algebraMap K L))).obj B) ((Over.pullback (spMap (algebraMap K L))).map i ≫ e.inv) (e.hom ≫ (Over.pullback (spMap (algebraMap K L))).map r) hab
  exact ⟨W, L, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, hcomp, hfin, hloc, hcompl, G₁, ‹_›, ⟨e₁, he₁⟩, hG₁⟩

end GlobalTheory.SS
end

