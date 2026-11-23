module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulPullSec
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFramePowEqIntegralGenerator
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExpansionCoefMemAdicPow
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory.PsiRing

theorem eq_zero_of_cst_eq_zero {S : Type} [CommRing S] [IsLocalRing S] {X : Scheme.{0}} (p : X ⟶ Sp S) [Flat p] (x : X)
    (hx : p x = IsLocalRing.closedPoint S) {a : S} (ha : cst p x a = 0) : a = 0 := by
  let φ : S →+* X.presheaf.stalk x := (p.stalkMap x).hom.comp
    (((Sp S).presheaf.germ ⊤ (p x) trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom)
  have hφ : ∀ c, φ c = cst p x c := fun c => by
    rw [cst, gs_stalkMap p x ⊤ trivial, gs_eq _ _ ⊤ trivial]; rfl
  have fl : φ.Flat := by
    refine RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv)) ?_) (Flat.stalkMap p x)
    have hU := isAffineOpen_top (Sp S)
    let _ := (Sp S).presheaf.algebra_section_stalk (U := ⊤) ⟨p x, trivial⟩
    have := hU.isLocalization_stalk ⟨p x, trivial⟩
    exact IsLocalization.flat ((Sp S).presheaf.stalk ((⟨p x, trivial⟩ : (⊤ : (Sp S).Opens)) : Sp S))
      (hU.primeIdealOf ⟨p x, trivial⟩).asIdeal.primeCompl
  let _ := φ.toAlgebra
  have : Module.Flat S (X.presheaf.stalk x) := fl
  have : IsLocalHom (algebraMap S (X.presheaf.stalk x)) := ⟨fun c hc => by
    by_contra h
    exact cst_not_isUnit p x hx h (hφ c ▸ hc)⟩
  have : Module.FaithfullyFlat S (X.presheaf.stalk x) := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective S (X.presheaf.stalk x) ((hφ a).trans (ha.trans (map_zero _).symm))

theorem coef_mem_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), I ≠ ⊤ → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (σ : U.SecGT (𝟙_ _) 1) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (th : SecBT D (𝟙_ _) 1 0), U.ExpT (𝟙_ _) 1 σ f → FibNZ (𝟙_ _ ⊗ D.P.A).hom th → ∀ e : ℕ, ∃ s : Finset D.X, ∀ χ ∉ s, ∀ (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (b : R), Coef D χ u th (f χ) b → b ∈ I ^ (e + 1) := by
  intro R _ _ _ I hI D A G _ _ U σ f th hE hth e
  obtain ⟨s, hs⟩ := hE e
  refine ⟨s, fun χ hχ u b hb => ?_⟩
  have hI' : I ^ (e + 1) ≠ ⊤ := fun h => hI (top_unique (h ▸ Ideal.pow_le_self e.succ_ne_zero))
  haveI : Nontrivial (R ⧸ I ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hI'
  haveI : IsLocalRing (R ⧸ I ^ (e + 1)) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk (I ^ (e + 1))) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hcl : thick R I e (IsLocalRing.closedPoint _) = IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint (Ideal.Quotient.mk (I ^ (e + 1)))
  haveI := U.semi.smooth
  haveI : Flat (thickObj R I e G).hom := inferInstanceAs (Flat (pullback.snd G.hom (thick R I e)))
  obtain ⟨z₀, hz₀, hnz⟩ := hth (IsLocalRing.closedPoint R)
  let T := (Over.map (thick R I e)).obj (thickObj R I e G)
  let y : T ⟶ D.P.A := (U.gt e).pG
  let m : 𝟙_ _ ⊗ D.P.A ⟶ D.P.A := snd (𝟙_ _) D.P.A * (cT D _ χ)⁻¹
  let τ : D.P.A ⟶ 𝟙_ _ ⊗ D.P.A := lift (toUnit _) (𝟙 _ * cT D _ χ)
  have hc : ∀ {T₁ T₂ : Over (Spec (CommRingCat.of R))} (g : T₁ ⟶ T₂), g ≫ cT D _ χ = cT D _ χ := fun g => by
    rw [cT, ← Category.assoc, toUnit_unique (g ≫ toUnit _) (toUnit _)]
  have hmτ : m ≫ τ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · exact toUnit_unique _ _
    · rw [Category.assoc, lift_snd, MonObj.comp_mul, hc, Category.comp_id, inv_mul_cancel_right, Category.id_comp]
  have hyτ : y ≫ τ = lift (toUnit T) (y * cT D T χ) := by
    apply CartesianMonoidalCategory.hom_ext
    · exact toUnit_unique _ _
    · rw [Category.assoc, lift_snd, MonObj.comp_mul, hc, Category.comp_id, lift_snd]
  have h1 : D.P.A.hom (m.left z₀) = IsLocalRing.closedPoint R := by
    rw [← Scheme.Hom.comp_apply, Over.w m]; exact hz₀
  obtain ⟨w, hw, hw'⟩ := Scheme.Pullback.exists_preimage_pullback (f := D.P.A.hom) (g := thick R I e)
    (m.left z₀) (IsLocalRing.closedPoint (R ⧸ I ^ (e + 1))) (h1.trans hcl.symm)
  obtain ⟨z, rfl⟩ := (U.gt e).q_surj.1 w
  have hy : y.left z = m.left z₀ := hw
  have hz : (thickObj R I e G).hom z = IsLocalRing.closedPoint _ := by
    rw [← Over.w (U.gt e).q, Scheme.Hom.comp_apply]; exact hw'
  have h2 : (lift (toUnit T) (y * cT D T χ)).left z = z₀ := by
    rw [← hyτ, Over.comp_left, Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, ← Over.comp_left, hmτ]
    rfl
  obtain ⟨J, hJ⟩ := exists_good_pt (Z := T.left) D.P.isLB z
  obtain ⟨JG, hJG⟩ := exists_good_pt (Z := T.left) U.P.L.isLB z
  have hu := (MulPullSec.mem_nonzeroLocus_iff th (lift (toUnit T) (y * cT D T χ)).left z hJ).1 (h2 ▸ hnz)
  have h0 := (hs T.left (𝟙 _) (lift (toUnit T) (fstG I e G)).left (lift (toUnit T) y).left
    (by rw [← Over.comp_left, lift_snd, Category.id_comp])
    (by rw [← Over.comp_left, lift_snd, Category.id_comp])
    (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]) z JG J hJG hJ).1 χ hχ
  have h3 := hb T y z J hJ
  rw [h0] at h3
  have h4 : cst T.hom z b = 0 := ((Units.isUnit _).mul hu).mul_left_eq_zero.1 h3.symm
  have h5 : cst (thickObj R I e G).hom z (Ideal.Quotient.mk _ b) = 0 :=
    (cst_comp (thickObj R I e G).hom (Ideal.Quotient.mk (I ^ (e + 1))) z b).symm.trans h4
  exact Ideal.Quotient.eq_zero_iff_mem.1 (eq_zero_of_cst_eq_zero _ z hz h5)

end GlobalTheory.PsiRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FinrankSpanReductionLe
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

namespace ModHilb

theorem finrank_span_reduction_le {O K I A B : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [Finite I] (f : I → A → K) (g : I → B → IsLocalRing.ResidueField O)
    (h : ∀ b : B, ∃ (a : A) (w : I → O), ∀ i, f i a = algebraMap O K (w i) ∧ g i b = IsLocalRing.residue O (w i)) :
    Module.finrank (IsLocalRing.ResidueField O) (Submodule.span (IsLocalRing.ResidueField O) (Set.range g)) ≤
      Module.finrank K (Submodule.span K (Set.range f)) := by
  first
  | exact @_root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le
  | exact _root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le
  | (apply _root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le ..)

theorem hilb_eq_finrank_span {k J : Type} [Field k] [Finite J] (C : Set (J → k)) (d : ℕ) :
    hilb C d = Module.finrank k (Submodule.span k (Set.range
      fun (m : {m : J →₀ ℕ // m.degree = d}) (v : C) => m.1.prod fun j n => v.1 j ^ n)) := by
  unfold hilb
  have : (MvPolynomial.homogeneousSubmodule J k d).map
      (LinearMap.pi fun v : C => (MvPolynomial.aeval (R := k) v.1).toLinearMap) =
      Submodule.span k (Set.range
      fun (m : {m : J →₀ ℕ // m.degree = d}) (v : C) => m.1.prod fun j n => v.1 j ^ n) := by
    rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
    rw [AddMonoidAlgebra.supported_eq_span_single, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
      refine ⟨⟨m, hm⟩, ?_⟩
      funext v
      change _ = MvPolynomial.aeval v.1 (MvPolynomial.monomial m (1 : k))
      simp [MvPolynomial.aeval_monomial]
    · rintro ⟨⟨m, hm⟩, rfl⟩
      refine ⟨_, ⟨m, hm, rfl⟩, ?_⟩
      funext v
      change MvPolynomial.aeval v.1 (MvPolynomial.monomial m (1 : k)) = _
      simp [MvPolynomial.aeval_monomial]
  rw [this]

theorem hilb_reduction_le : (∀ (O K J : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Fintype J] (C : Set (J → K)) (C' : Set (J → IsLocalRing.ResidueField O)), (∀ v' ∈ C', ∃ w : J → O, (fun j => algebraMap O K (w j)) ∈ C ∧ v' = fun j => IsLocalRing.residue O (w j)) → ∀ d, hilb C' d ≤ hilb C d) := by
  intro O K J _ _ _ _ _ _ _ C C' h d
  rw [hilb_eq_finrank_span, hilb_eq_finrank_span]
  haveI : Finite {m : J →₀ ℕ // m.degree = d} :=
    (Finsupp.finite_of_degree_eq d).to_subtype
  apply finrank_span_reduction_le
  rintro ⟨v', hv'⟩
  obtain ⟨w, hw, rfl⟩ := h v' hv'
  refine ⟨⟨_, hw⟩, fun m => m.1.prod fun j n => w j ^ n, fun m => ⟨?_, ?_⟩⟩
  · simp [Finsupp.prod]
  · simp [Finsupp.prod]

end ModHilb

theorem Mod.hilb_special_le_generic : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] (j : V →+* OO p) (G : Over (Sp V)) [GrpObj G] (g N N' : ℕ) (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (H : LB G.left) (J : Type) [Fintype J] (σ : J → H.Sec) (cls : J → X) (m : Mod p j G g N q H σ cls) (d : ℕ), hilb (cone m.Φ.G.hom (m.Φ.H 1) m.F) d ≤ hilb {w : J → PadicAlgCl p | ∃ a : Sp (PadicAlgCl p) ⟶ G.left, a ≫ G.hom = gPt p ≫ spMap j ∧ Crd H σ a w} d := by
  intro p _ V _ j G _ g N _ X _ q H J _ σ cls m d
  refine ModHilb.hilb_reduction_le (OO p) (PadicAlgCl p) J _ _ ?_ d
  rintro v ⟨x, hx, hv⟩
  have hred : Crd H σ (x ≫ m.r) v := m.red (Over.homMk x hx) v hv
  haveI := m.smooth
  haveI : Smooth G.hom := SmoothOfRelativeDimension.smooth g G.hom
  obtain ⟨c, hc, hcx⟩ := GlobalTheory.ZJ.exists_classical_lift_of_smooth p G.left (Sp V) G.hom (spMap j)
    (x ≫ m.r) (by
      rw [Category.assoc, m.cart.1.w, ← Category.assoc, hx]
      exact Category.id_comp _)
  obtain ⟨w, hw⟩ := CrdCalc.crd_exists m.isLB σ c
  have hw' : Crd H σ (x ≫ m.r) (fun i => IsLocalRing.residue (OO p) (w i)) := by
    rw [← hcx]
    exact CrdCalc.crd_map _ hw
  obtain ⟨u, hu⟩ := CrdCalc.crd_unique hw' hred
  obtain ⟨u₀, hu₀⟩ := IsLocalRing.residue_surjective (u : kb p)
  have hunit : IsUnit u₀ := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hu₀]
    exact u.ne_zero
  obtain ⟨u₁, rfl⟩ := hunit
  refine ⟨fun i => (u₁ : OO p) * w i, ⟨gPt p ≫ c, by rw [Category.assoc, hc], ?_⟩, ?_⟩
  · exact CrdCalc.crd_map (OO p).subtype (CrdCalc.crd_smul u₁ hw)
  · funext i
    rw [hu, map_mul, hu₀]

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ForallTermNeZeroOfPsiRelation
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory

theorem psiRel_field_ne_zero_iff {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (s : Raw D F 1) (h : PsiRel D (TF (R := R) F) s) (χ : D.X) :
    (∃ j, (s χ).f j ≠ 0) ↔ ∃ j, (s 0).f j ≠ 0 := by
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have : IsIntegral (DegPre.BF D F).left := isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (TF (R := R) F)
  obtain ⟨J, hJ⟩ := exists_good_pt (Z := (DegPre.BF D F).left) D.P.isLB (genericPoint _)
  have := PsiExists.isIso_trF D F χ
  have : IsIso (DegPre.trF D F χ).left := inferInstanceAs (IsIso ((Over.forget _).map (DegPre.trF D F χ)))
  let κ : DegPre.BF D F ⟶ TK R := Over.homMk ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F)
    ((Category.assoc _ _ _).trans (Over.w (fst (TF (R := R) F) D.P.A)))
  have e := h χ (DegPre.BF D F) (fst _ _) κ (snd _ _) _ J hJ
  have e₁ : (lift (fst (TF (R := R) F) D.P.A) (snd _ _)).left = 𝟙 (DegPre.BF D F).left :=
    congrArg (fun q : DegPre.BF D F ⟶ DegPre.BF D F => q.left) lift_fst_snd
  have e₂ : sval (s χ) (𝟙 (DegPre.BF D F).left) (genericPoint _) J =
      (val (D.psi χ) κ.left (genericPoint _) J * rigV D (T := DegPre.BF D F) (genericPoint _) J).val *
        sval (s 0) (DegPre.trF D F χ).left (genericPoint _) J :=
    (congrArg (fun q => sval (s χ) q (genericPoint _) J) e₁).symm.trans e
  rw [exists_ne_zero_iff_sval_ne_zero _ hJ, e₂]
  constructor
  · intro h0
    by_contra hn
    simp only [not_exists, not_not] at hn
    exact h0 (by rw [sval_eq_zero_of_local_eq_zero (s 0) hn _ _ J hJ, MulZeroClass.mul_zero])
  · intro h0
    exact mul_ne_zero (Units.ne_zero _) (sval_ne_zero_of_isIso _ _ D.P.L D.P.isLB _ _ _ (s 0) h0 _ _ _ J hJ)

theorem forall_ne_zero_of_psiRel : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (f : ∀ α, SecBT D (𝟙_ _) 1 α), PsiRel D (𝟙_ _) f → (∃ α j, (f α).f j ≠ 0) → ∀ α, ∃ j, (f α).f j ≠ 0 := by
  rintro R _ _ D f h ⟨α, hα⟩ β
  obtain ⟨s, hs⟩ := PsiExists.exists_pullB D (FractionRing R) (toUnit _) 1 f
  have h' := psiRel_of_pullB R D _ f s hs h
  have i := pullB_ne_zero_iff R D _ 1 f s hs
  exact (i β).1 ((psiRel_field_ne_zero_iff D _ s h' β).2 ((psiRel_field_ne_zero_iff D _ s h' α).1 ((i α).2 hα)))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrameUnit
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.ZHPre
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

abbrev LOne : LB Q.G.left := LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => 1)

abbrev SecFam (N : M.Z.Opens) : Type := ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j)

abbrev ThMul (c : Ω) (N : M.Z.Opens) (σ : Q.SecFam N) : Prop :=
  GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w 1 (fun _ : Unit => ρ.th₁) (fun _ => c) _ σ

abbrev FibNe (N : M.Z.Opens) (σ : Q.SecFam N) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), Set.range x ⊆ N →
    ∃ (g : Sp K ⟶ Q.G.left) (j : _), g ≫ Q.G.hom = x ∧ valF g _ (σ j) ≠ 0

abbrev ExtPt (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) : Prop :=
  h ≫ Q.G.hom = W.ι ∧
  ∀ (x : Sp Ω ⟶ W.toScheme) (x' : Sp Ω ⟶ pullback ρ.P.A.hom Q.u₀), x ≫ W.ι = M.pt → x' ≫ Q.φ ≫ Q.G.hom = M.pt →
    x' ≫ pullback.fst _ _ = spMap S.R.val.toRingHom ≫ (ρ.pt a).left → x ≫ h = x' ≫ Q.φ

def MulRel (n : ℕ)
    (α : LB.Gen (LB.LinComb ρ.P.L (K := Fin 2) ![𝟙 ρ.P.A.left, (mulA ρ.P.A n).left] ![(n : ℤ) ^ 2, -1]))
    (κ : LB.Gen (LB.LinComb Q.L.L (K := Fin 2) ![𝟙 Q.G.left, (mulA Q.G n).left] ![(n : ℤ) ^ 2, -1])) : Prop :=
  ∀ (K : Type) [Field K] (g g' : Sp K ⟶ pullback ρ.P.A.hom Q.u₀) (jP jP' : ρ.P.L.ι) (jL jL' : Q.L.L.ι),
    g' ≫ pullback.fst _ _ = g ≫ pullback.fst _ _ ≫ (mulA ρ.P.A n).left →
    g' ≫ pullback.snd _ _ = g ≫ pullback.snd _ _ →
    Set.range (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP → Set.range (g ≫ Q.φ) ⊆ Q.L.L.U jL →
    Set.range (g' ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP' → Set.range (g' ≫ Q.φ) ⊆ Q.L.L.U jL' →
    valF (g ≫ pullback.fst ρ.P.A.hom Q.u₀) _ (α.s ![jP, jP']).val *
        valF g' _ (Q.w.s (fun _ => jP', fun _ => jL')).val =
      valF g _ (Q.w.s (fun _ => jP, fun _ => jL)).val ^ (n ^ 2) * valF (g ≫ Q.φ) _ (κ.s ![jL, jL']).val

def FrameUnit (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) (w : W.toScheme) : Prop :=
  ∀ (jP : ρ.P.L.ι) (jL : Q.L.L.ι) (x' : Sp Ω ⟶ pullback ρ.P.A.hom Q.u₀) (e : Ω), h w ∈ Q.L.L.U jL →
    x' ≫ Q.φ ≫ Q.G.hom = M.pt → x' ≫ pullback.fst _ _ = spMap S.R.val.toRingHom ≫ (ρ.pt a).left →
    Set.range (x' ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP →
    e = valF (X := (baseOver (Sp S.R)).left) (spMap S.R.val.toRingHom) _ ((ρ.fr a).s fun _ => jP).val /
      valF x' _ (Q.w.s (fun _ => jP, fun _ => jL)).val →
    e ≠ 0 ∧ e ∈ M.O (W.ι w) ∧ e⁻¹ ∈ M.O (W.ι w)

def TestFac {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)
    (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme) : Prop :=
  (∀ x, (jV x : PadicAlgCl p) = algebraMap (FractionRing u.V) _ (algebraMap u.V (FractionRing u.V) x)) ∧
    spMap jV ≫ yV = y ∧ yK ≫ U₀.ι = jK u.V ≫ yV ∧ yK ≫ Q.u₀ = spMap u.yK

def TestMap {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)
    (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme) (F : u.G.left ⟶ Q.G.left)
    (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀) : Prop :=
  IsGrpPullback u.G Q.G yV F ∧ ψ ≫ pullback.fst _ _ = u.U.gen.hom.left ≫ u.φ ∧
    ψ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ yK ∧ ψ ≫ Q.φ = pullback.fst _ _ ≫ F

end GlobalTheory.ZH.ZHPre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GtAddIotaSubExist
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH

theorem gt_add_iota_sub_exist : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), (∀ g g' : GtPtF u.D.toPre (PadicAlgCl p), ∃ g'', GtPtF.IsAdd g g' g'') ∧ (∀ y, ∃ g : GtPtF u.D.toPre (PadicAlgCl p), GtPtF.IsIota y g) ∧ ∀ g h : GtPtF u.D.toPre (PadicAlgCl p), ∃ g', GtPtF.IsAdd g' h g := by
  intro _ o Ω _ _ _ _ S ρ p _ y₀ u
  letI := GlobalTheory.TorusExt.gtGroup u.D.toPre (PadicAlgCl p)
  exact ⟨fun g g' => ⟨g + g', (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl⟩,
    fun y => GlobalTheory.TorusExt.exists_iota u.D.tau_bimult y,
    fun g h => ⟨g - h, (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 (sub_add_cancel g h).symm⟩⟩

end GlobalTheory.ZH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem isLocallyNoetherian [IsNoetherianRing o] : IsLocallyNoetherian M.Z :=
  have := M.lft
  LocallyOfFiniteType.isLocallyNoetherian M.s

def ptOpen (V : M.Z.Opens) (hV : (V : Set M.Z).Nonempty) : Sp Ω ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι M.pt (by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hV))

theorem ptOpen_ι (V : M.Z.Opens) (hV : (V : Set M.Z).Nonempty) : M.ptOpen V hV ≫ V.ι = M.pt :=
  IsOpenImmersion.lift_fac _ _ _

def openPart [IsNoetherianRing o] (V : M.Z.Opens) (hV : (V : Set M.Z).Nonempty) : RatModel o Ω :=
  haveI : Nonempty V.toScheme := ⟨⟨hV.some, hV.some_mem⟩⟩
  haveI : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  { Z := V.toScheme
    s := V.ι ≫ M.s
    sep := have := M.sep; inferInstance
    lft := have := M.lft; inferInstance
    qc := have := M.qc; have := M.isLocallyNoetherian; inferInstance
    pt := M.ptOpen V hV
    pt_s := by rw [← Category.assoc, ptOpen_ι, M.pt_s]
    gen := by
      have h : ∀ w : Sp Ω, M.ptOpen V hV w = genericPoint V.toScheme := fun w => by
        apply V.ι.isOpenEmbedding.injective
        rw [genericPoint_eq_of_isOpenImmersion, ← M.pt_apply w, ← M.ptOpen_ι V hV]
        rfl
      exact Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, h (IsLocalRing.closedPoint Ω)⟩, by
        rintro _ ⟨w, rfl⟩
        exact h w⟩
    onto := fun x => by
      obtain ⟨U, f, hU, rfl⟩ := M.onto x
      obtain ⟨z, hz, hz'⟩ := M.nonempty_inf hU hV
      refine ⟨V.ι ⁻¹ᵁ U, V.ι.app U f, ⟨⟨z, hz'⟩, hz⟩, ?_⟩
      refine (valR_comp _ _ U f).symm.trans ?_
      rw [ptOpen_ι]
      rfl }

theorem isHom_openPart [IsNoetherianRing o] (V : M.Z.Opens) (hV : (V : Set M.Z).Nonempty) :
    M.IsHom (M.openPart V hV) (AlgHom.id o Ω) V.ι :=
  (M.ptOpen_ι V hV).trans ((Category.id_comp _).symm.trans (congrArg (· ≫ M.pt) (Spec.map_id _).symm))

variable {M}

theorem IsHom.O_eq {N : RatModel o Ω} {j : N.Z ⟶ M.Z} (h : M.IsHom N (AlgHom.id o Ω) j) [IsOpenImmersion j]
    (z : N.Z) : N.O z = M.O (j z) := by
  refine le_antisymm ?_ fun x hx => h.map_mem_O hx
  rintro _ ⟨U, g, hz, rfl⟩
  have hz' : j z ∈ j ''ᵁ U := ⟨z, hz, rfl⟩
  refine ⟨j ''ᵁ U, (j.appIso U).inv g, hz', ?_⟩
  refine (h.valF_app ⟨_, hz'⟩ _).symm.trans ?_
  have e := congrArg (fun φ => φ.hom g) (j.appIso_inv_app U)
  refine (congrArg _ e).trans ?_
  exact N.valF_resG (j.preimage_image_eq U).le ⟨z, hz'⟩ g

variable (M)

structure GenTriv (H : LB M.Z) (d : H.ι → Ω) : Prop where
  ne : ∀ k, d k ≠ 0
  g_eq : ∀ k k', ((H.U k ⊓ H.U k' : M.Z.Opens) : Set M.Z).Nonempty →
    valF M.pt (H.U k ⊓ H.U k') (H.g k k' : Γ(M.Z, H.U k ⊓ H.U k')) = d k' / d k

def HasVal {H : LB M.Z} (d : H.ι → Ω) (σ : H.Sec) (x : Ω) : Prop :=
  ∀ k, (H.U k : Set M.Z).Nonempty → valF M.pt (H.U k) (σ.f k) = x / d k

def ProjChart {Ω' : Type} [Field Ω'] [Algebra o Ω'] (N : RatModel o Ω') (φ : Ω →ₐ[o] Ω') (q : N.Z ⟶ M.Z)
    (W : M.Z.Opens) {J : Type} (t : J → Ω') : Prop :=
  (∀ z', q z' ∈ W → ∃ i, N.Div t i z') ∧ ∀ i, t i ≠ 0 → ∃ U : N.Z.Opens, IsAffineOpen U ∧
    (U : Set N.Z) = {z' | q z' ∈ W ∧ N.Div t i z'} ∧
    N.ringOn U = Algebra.adjoin o (φ '' (M.ringOn W : Set Ω) ∪ Set.range fun j => t j / t i)

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFramePowEqIntegralGeneratorStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionFrame_pow_eq_integral_generator : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (M : RigLB G) (B : Scheme.{0}) (P : PolAV B) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (t : Sp (FractionRing V) ⟶ B) (ψ : pullback G.hom (jK V) ⟶ P.A.left), IsGrpPullback ((Over.pullback (jK V)).obj G) P.A t ψ → ∀ (w : LB.Iso (M.L.pull (pullback.fst G.hom (jK V))) (P.L.pull ψ)), w.IsGen → ∀ n : ℕ, ∃ lam : FractionRing V, lam ≠ 0 ∧ ∀ (z : baseOver B ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver B).left) (K := Fin 1) (fun _ => z.left) (fun _ => 1))), IsTorsFrame P rig n z τ → ∀ (h : baseOver (Sp V) ⟶ G) (x : Sp (FractionRing V) ⟶ pullback G.hom (jK V)), x ≫ pullback.fst G.hom (jK V) = jK V ≫ h.left → x ≫ pullback.snd G.hom (jK V) = 𝟙 _ → x ≫ ψ = t ≫ z.left → ∀ (i : M.L.ι) (k : P.L.ι), ⊤ ≤ h.left ⁻¹ᵁ M.L.U i → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ P.L.U k → ∃ v : Vˣ, valR (X := (baseOver B).left) t _ (τ.s (fun _ => k)).val ^ (n ^ 2) = (lam * valR x _ (w.s (fun _ => k, fun _ => i)).val) ^ (n ^ 2) * algebraMap V (FractionRing V) v := by
  first | exact @GlobalTheory.TorsFrameInt.torsFrame_pow_eq | exact GlobalTheory.TorsFrameInt.torsFrame_pow_eq | (intros; apply GlobalTheory.TorsFrameInt.torsFrame_pow_eq <;> assumption)
end

