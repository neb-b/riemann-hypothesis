module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsContraction
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteSeparableCompositum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem exists_finite_separable_compositum (K K' k : Type) [Field K] [Field K'] [Field k] [Algebra K k]
    [FiniteDimensional K k] [Algebra.IsSeparable K k] (φ : K →+* K') :
    ∃ (k' : Type) (_ : Field k') (_ : Algebra K' k') (g : k →+* k'), FiniteDimensional K' k' ∧
      Algebra.IsSeparable K' k' ∧ g.comp (algebraMap K k) = (algebraMap K' k').comp φ := by
  let Ω := AlgebraicClosure K'
  let _ : Algebra K K' := φ.toAlgebra
  let σ : k →ₐ[K] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let bs := Module.finBasis K k
  let k' := IntermediateField.adjoin K' (Set.range fun i => σ (bs i))
  have sepσ : ∀ z : k, IsSeparable K' (σ z) := fun z =>
    ((Algebra.IsSeparable.isSeparable K z).map σ σ.injective).tower_top _
  have h₁ : FiniteDimensional K' k' :=
    IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨i, rfl⟩; exact (sepσ _).isIntegral)
  have h₂ : Algebra.IsSeparable K' k' :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable _ _).2 (by rintro _ ⟨i, rfl⟩; exact sepσ _)
  have hmem : ∀ z : k, σ z ∈ k' := fun z => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← bs.sum_repr z, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply K K' Ω]
    exact mul_mem (k'.algebraMap_mem _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  refine ⟨k', inferInstance, inferInstance, σ.toRingHom.codRestrict k'.toSubring hmem, h₁, h₂, ?_⟩
  ext z
  exact σ.commutes z

theorem splitFibres_of_isGrpPullback : Out.GtBaseChangeSt → ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → (∀ x : X, ∃ (k : Type) (_ : Field k) (_ : Algebra (X.residueField x) k), FiniteDimensional (X.residueField x) k ∧ Algebra.IsSeparable (X.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k)) ≫ X.fromSpecResidueField x)).obj G)) → (∀ x : X', ∃ (k : Type) (_ : Field k) (_ : Algebra (X'.residueField x) k), FiniteDimensional (X'.residueField x) k ∧ Algebra.IsSeparable (X'.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField x) k)) ≫ X'.fromSpecResidueField x)).obj G')) := by
  intro hB X X' f G _ G' _ φ hφ hS x'
  obtain ⟨k, _, _, hfin, hsep, S, hGt⟩ := hS (f x')
  obtain ⟨k', _, _, g, h₁, h₂, hg⟩ :=
    exists_finite_separable_compositum (X.residueField (f x')) (X'.residueField x') k (f.residueFieldMap x').hom
  refine ⟨k', inferInstance, inferInstance, h₁, h₂, ?_⟩
  have key : spMap g ≫ Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (f x')) k)) ≫
      X.fromSpecResidueField (f x') =
      (Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField x') k')) ≫ X'.fromSpecResidueField x') ≫ f := by
    have a₁ : spMap g ≫ Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (f x')) k)) =
        spMap (algebraMap (X'.residueField x') k') ≫ Spec.map (f.residueFieldMap x') :=
      (spMap_comp _ _).symm.trans ((congrArg spMap hg).trans (spMap_comp _ _))
    rw [← Category.assoc, a₁, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      Category.assoc]
  obtain ⟨S', -, -, -, -, hGt'⟩ := hB _ _ (spMap g) S _ hGt
  refine ⟨S', ?_⟩
  have : IsMonHom (pullCompIso (spMap g) (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (f x')) k)) ≫
      X.fromSpecResidueField (f x')) G).symm.hom := by
    show IsMonHom (pullCompIso _ _ _).inv
    infer_instance
  have h₀ := isGt_of_iso (pullCompIso (spMap g) _ G).symm hGt'
  rw [key] at h₀
  have h₃ := isGt_of_iso (pullCompIso _ f G) h₀
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback G f) hφ
  have : IsMonHom ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField x') k')) ≫
      X'.fromSpecResidueField x')).mapIso e).hom := by
    rw [Functor.mapIso_hom]
    infer_instance
  exact isGt_of_iso ((Over.pullback _).mapIso e) h₃

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsumSmulEqOneOfTame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
theorem _root_.GlobalTheory.exists_finsum_smul_eq_one_of_tame :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (B : Type) [CommRing B] [MulSemiringAction Γ B],
      (∀ q : Ideal B, q.IsPrime → (Nat.card (q.inertia Γ) : B) ∉ q) →
        ∃ b : B, ∑ᶠ g : Γ, g • b = 1 := by
  intro Γ _ _ B _ _ htame
  classical
  haveI := Fintype.ofFinite Γ
  let A := FixedPoints.subring B Γ
  haveI : Algebra.IsInvariant A B Γ := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  haveI := Algebra.IsInvariant.isIntegral A B Γ
  have tr_inv : ∀ b : B, ∑ g : Γ, g • b ∈ A := by
    intro b h
    rw [Finset.smul_sum]
    simp_rw [← mul_smul]
    exact Equiv.sum_comp (Equiv.mulLeft h) (fun g => g • b)
  let T : Ideal A := Ideal.span {t | ∃ b : B, (t : B) = ∑ g : Γ, g • b}
  have hT : ∀ t ∈ T, ∃ b : B, (t : B) = ∑ g : Γ, g • b := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht => exact ht
    | zero => exact ⟨0, by simp⟩
    | add t u _ _ htb hub =>
      obtain ⟨b, hb⟩ := htb
      obtain ⟨c, hc⟩ := hub
      exact ⟨b + c, by simp [hb, hc, Finset.sum_add_distrib]⟩
    | smul a t _ htb =>
      obtain ⟨b, hb⟩ := htb
      refine ⟨(a : B) * b, ?_⟩
      simp only [smul_eq_mul, Subring.coe_mul, hb, Finset.mul_sum, smul_mul']
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [a.2 g]
  suffices h1 : (1 : A) ∈ T by
    obtain ⟨b, hb⟩ := hT 1 h1
    exact ⟨b, by rw [finsum_eq_sum_of_fintype, ← hb]; rfl⟩
  by_contra h1
  obtain ⟨m, hm, hTm⟩ := Ideal.exists_le_maximal T ((Ideal.ne_top_iff_one T).mpr h1)
  have hker : RingHom.ker (algebraMap A B) ≤ m := by
    intro z hz
    have : z = 0 := Subtype.ext hz
    rw [this]
    exact m.zero_mem
  obtain ⟨Q, hQ, hQm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral m hker
  obtain ⟨n, c, d, s, hs, hsep⟩ := _root_.GlobalTheory.exists_sum_smul_separating_inertia Γ B Q hQ.isPrime
  have trace_mem : ∀ j, ∑ g : Γ, g • c j ∈ Q := by
    intro j
    have hmemT : (⟨∑ g : Γ, g • c j, tr_inv (c j)⟩ : A) ∈ T :=
      Ideal.subset_span ⟨c j, rfl⟩
    have := hTm hmemT
    rw [← hQm, Ideal.mem_comap] at this
    exact this
  have hz : ∑ g : Γ, ∑ j, d j * g • c j ∈ Q := by
    rw [Finset.sum_comm]
    exact Q.sum_mem fun j _ => by
      rw [← Finset.mul_sum]
      exact Q.mul_mem_left _ (trace_mem j)
  have hdiff : ∑ g : Γ, (∑ j, d j * g • c j - if g ∈ Q.inertia Γ then s else 0) ∈ Q := by
    refine Q.sum_mem fun g _ => ?_
    split_ifs with hg
    · exact (hsep g).1 hg
    · simpa using (hsep g).2 hg
  rw [Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul] at hdiff
  have hcs := Q.sub_mem hz hdiff
  rw [sub_sub_cancel] at hcs
  rcases hQ.isPrime.mem_or_mem hcs with hc | hc
  · apply htame Q hQ.isPrime
    convert hc using 2
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  · exact hs hc

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGoodUniformisationKodairaSpencer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KSInh

variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g)

theorem dom_id (W : A₀.left.Opens) : dom u (𝟙 _) W = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ W} := by
  ext z
  unfold dom
  simp only [Category.comp_id]

theorem fn_id (W : A₀.left.Opens) (f : Γ(A₀.left, W)) :
    fn u (𝟙 _) W f = fun z => valAt' (u.ex z).left W f := by
  funext z
  unfold fn
  rw [Category.comp_id]

theorem isOpen_dom (W : A₀.left.Opens) : IsOpen (dom u (𝟙 _) W) := by
  rw [dom_id]
  exact (u.hol W 0).1

theorem differentiableOn_fn (W : A₀.left.Opens) (f : Γ(A₀.left, W)) :
    DifferentiableOn ℂ (fn u (𝟙 _) W f) (dom u (𝟙 _) W) := by
  rw [dom_id, fn_id]
  exact (u.hol W f).2

theorem differentiableAt_fn (W : A₀.left.Opens) (f : Γ(A₀.left, W)) {z : Fin g → ℂ} (hz : z ∈ dom u (𝟙 _) W) :
    DifferentiableAt ℂ (fn u (𝟙 _) W f) z :=
  (differentiableOn_fn u W f).differentiableAt ((isOpen_dom u W).mem_nhds hz)

theorem ex_add_period (l : u.Λ) (z : Fin g → ℂ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]

theorem ksRel_const (w : Fin g → ℂ) :
    KSRel u A₀.hom (𝟙 _) (fun _ => 0) 0 (fun z W f => fderiv ℂ (fn u (𝟙 _) W f) z w) := by
  refine { der := ?der, base := ?base, hol := ?hol, per := ?per }
  case der =>
    intro z
    have hd : ∀ (W : A₀.left.Opens) (k : Γ(A₀.left, W)), ⊤ ≤ ((u.ex z).left ≫ 𝟙 _) ⁻¹ᵁ W →
        DifferentiableAt ℂ (fn u (𝟙 _) W k) z :=
      fun W k hW => differentiableAt_fn u W k hW
    refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW' f => ?_⟩
    · have e : fn u (𝟙 _) W (f + f') = fn u (𝟙 _) W f + fn u (𝟙 _) W f' := by
        funext y
        simp only [fn, valAt', Pi.add_apply]
        split_ifs with hy
        · simp only [valAt, map_add (f := _)]
        · exact (add_zero 0).symm
      show fderiv ℂ (fn u (𝟙 _) W (f + f')) z w =
        fderiv ℂ (fn u (𝟙 _) W f) z w + fderiv ℂ (fn u (𝟙 _) W f') z w
      rw [e, fderiv_add (hd W f hW) (hd W f' hW)]
      rfl
    · have e : fn u (𝟙 _) W (f * f') = fn u (𝟙 _) W f * fn u (𝟙 _) W f' := by
        funext y
        simp only [fn, valAt', Pi.mul_apply]
        split_ifs with hy
        · simp only [valAt, map_mul]
        · exact (mul_zero 0).symm
      show fderiv ℂ (fn u (𝟙 _) W (f * f')) z w =
        fn u (𝟙 _) W f z * fderiv ℂ (fn u (𝟙 _) W f') z w + fn u (𝟙 _) W f' z * fderiv ℂ (fn u (𝟙 _) W f) z w
      rw [e, fderiv_mul (hd W f hW) (hd W f' hW)]
      rfl
    · show fderiv ℂ (fn u (𝟙 _) W' (resG A₀.left h f)) z w = fderiv ℂ (fn u (𝟙 _) W f) z w
      have hev : fn u (𝟙 _) W' (resG A₀.left h f) =ᶠ[nhds z] fn u (𝟙 _) W f := by
        filter_upwards [(isOpen_dom u W').mem_nhds hW'] with y hy
        have hyW' : ⊤ ≤ ((u.ex y).left ≫ 𝟙 _) ⁻¹ᵁ W' := hy
        have hy' : ⊤ ≤ ((u.ex y).left ≫ 𝟙 _) ⁻¹ᵁ W := hyW'.trans (Scheme.Hom.preimage_mono _ h)
        simp only [fn, valAt', dite_eq_left hyW', dite_eq_left hy']
        unfold valAt resG
        have key : A₀.left.presheaf.map (homOfLE h).op ≫ Scheme.Hom.appLE ((u.ex y).left ≫ 𝟙 _) W' ⊤ hyW' =
            Scheme.Hom.appLE ((u.ex y).left ≫ 𝟙 _) W ⊤ hy' :=
          Scheme.Hom.map_appLE _ _ _
        rw [← key]
        rfl
      rw [hev.fderiv_eq]
  case base =>
    intro z r
    show fderiv ℂ (fn u (𝟙 _) ⊤ (constFn A₀.hom ⊤ r)) z w = 0
    obtain ⟨K, hK⟩ : ∃ K : ℂ, ∀ y, fn u (𝟙 _) ⊤ (constFn A₀.hom ⊤ r) y = K := by
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
        ((Scheme.Hom.appLE (𝟙_ (Over (Sp ℂ))).hom ⊤ ⊤ (Scheme.Hom.preimage_top _).ge).hom
          ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)), fun y => ?_⟩
      have ht : ⊤ ≤ ((u.ex y).left ≫ 𝟙 _) ⁻¹ᵁ (⊤ : A₀.left.Opens) := (Scheme.Hom.preimage_top _).ge
      have key : Scheme.Hom.appLE A₀.hom ⊤ ⊤ (Scheme.Hom.preimage_top _).ge ≫ Scheme.Hom.appLE ((u.ex y).left ≫ 𝟙 _) ⊤ ⊤ ht =
          Scheme.Hom.appLE (𝟙_ (Over (Sp ℂ))).hom ⊤ ⊤ (Scheme.Hom.preimage_top _).ge := by
        rw [Scheme.Hom.appLE_comp_appLE]
        congr 1
        simp
      simp only [fn, valAt', dite_eq_left ht]
      unfold valAt constFn
      rw [← key]
      rfl
    have e : fn u (𝟙 _) ⊤ (constFn A₀.hom ⊤ r) = fun _ => K := funext hK
    rw [e]
    simp
  case hol =>
    intro W f
    exact ((cauchyRiemann_iff_differentiableOn_complex g _ _ (isOpen_dom u W)).2 (differentiableOn_fn u W f)).2 w
  case per =>
    intro l W f z _
    show fderiv ℂ (fn u (𝟙 _) W f) (z + l) w =
      fderiv ℂ (fn u (𝟙 _) W f) z w + fderiv ℂ (fn u (𝟙 _) W f) z ((0 : Matrix (Fin g) (Fin g) ℂ).mulVec (star (l : Fin g → ℂ)))
    have hp : (fun y => fn u (𝟙 _) W f (y + l)) = fn u (𝟙 _) W f := by
      funext y
      unfold fn
      rw [ex_add_period]
    rw [Matrix.zero_mulVec, map_zero, add_zero, ← fderiv_comp_add_right, hp]

theorem exists_goodU_ksRel : ThetaUnifAV → ∀ P₀ : Out.PolAV (Sp ℂ), ∃ (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ ∧ ∀ w : Fin P₀.g → ℂ, KSRel u P₀.A.hom (𝟙 _) (fun _ => 0) 0 (fun z W f => fderiv ℂ (fn u (𝟙 _) W f) z w) := by
  intro hT P₀
  obtain ⟨rig, hrig⟩ : ∃ rig : LB.Gen (P₀.L.pull (eSec P₀.A)), rig.IsGen := P₀.rigid
  obtain ⟨u, Hm, χ, _, hAH, -, ht₁, ht₂, hend, hth, -⟩ := hT P₀ rig hrig
  exact ⟨u, Hm, χ, ⟨hAH, ht₁, ht₂, hend, fun n θ hθ => ((hth n).2 θ hθ).exists⟩, fun w => ksRel_const u w⟩

end GlobalTheory.KSInh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsDominantGeometricPointOfIsPreimmersion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem exists_isDominant_geometricPoint_of_isPreimmersion {Z W : Scheme.{0}} [IrreducibleSpace W]
    (a : Z ⟶ W) [IsPreimmersion a] [IsDominant a] [QuasiCompact a] :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (t : Sp k ⟶ Z), IsDominant t := by
  have hη : genericPoint W ∈ genericPoints W := by
    rw [genericPoints_eq_singleton]; rfl
  obtain ⟨z, hz⟩ := genericPoints_subset_range_of_isDominant a hη
  let k := AlgebraicClosure (Z.residueField z)
  let t : Sp k ⟶ Z := spMap (algebraMap (Z.residueField z) k) ≫ Z.fromSpecResidueField z
  refine ⟨k, inferInstance, inferInstance, t, ⟨fun z' => ?_⟩⟩
  have h₁ : z ⤳ z' := by
    rw [← a.isEmbedding.isInducing.specializes_iff, hz]
    exact genericPoint_specializes _
  have h₂ : z ∈ Set.range t :=
    ⟨IsLocalRing.closedPoint k, Scheme.fromSpecResidueField_apply z _⟩
  exact closure_mono (Set.singleton_subset_iff.mpr h₂) (specializes_iff_mem_closure.mp h₁)

theorem isOpenImmersion_of_etale_of_mono_pullback_snd {X U W : Scheme.{0}}
    [GlobalTheory.IsNormalScheme X] (j : U ⟶ X) [IsDominant j] (q : W ⟶ X) [Etale q] [IsSeparated q]
    [Mono (pullback.snd q j)] : IsOpenImmersion q := by
  let r : pullback q q ⟶ X := pullback.fst q q ≫ q
  have := isNormalScheme_of_smooth r
  have := isDominant_pullback_fst_of_isOpenMap j r r.isOpenMap
  have h : pullback.lift (f := q) (g := j) (pullback.fst r j ≫ pullback.fst q q) (pullback.snd r j)
        (by rw [Category.assoc]; exact pullback.condition) =
      pullback.lift (pullback.fst r j ≫ pullback.snd q q) (pullback.snd r j)
        (by rw [Category.assoc, ← pullback.condition (f := q) (g := q)]
            exact pullback.condition) := by
    rw [← cancel_mono (pullback.snd q j), pullback.lift_snd, pullback.lift_snd]
  have h' : pullback.fst r j ≫ pullback.fst q q = pullback.fst r j ≫ pullback.snd q q := by
    simpa only [pullback.lift_fst] using congrArg (· ≫ pullback.fst q j) h
  have he : pullback.fst q q = pullback.snd q q :=
    ext_of_isDominant_of_isSeparated q pullback.condition _ h'
  have : Mono q := ⟨fun a b hab => by
    rw [← pullback.lift_fst a b hab, he, pullback.lift_snd]⟩
  exact IsOpenImmersion.of_flat_of_mono q

theorem exists_opens_isOpenImmersion_extending_section : ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (Y : Scheme.{0}) (p : Y ⟶ X) (I : Type) [Finite I] (σ : I → (U ⟶ Y)), Etale p → IsSeparated p → (∀ i, σ i ≫ p = j) → (∀ (k : Type) [Field k] [IsAlgClosed k] (u : Sp k ⟶ U) (y : Sp k ⟶ Y), y ≫ p = u ≫ j → ∃ i, y = u ≫ σ i) → ∀ y : Y, ∃ (i : I) (W : Y.Opens), y ∈ W ∧ IsOpenImmersion (W.ι ≫ p) ∧ pullback.fst (W.ι ≫ p) j ≫ W.ι = pullback.snd (W.ι ≫ p) j ≫ σ i := by
  intro X U _ j hN _ _ _ _ Y p I _ σ _ _ hσ hgeo y
  have := IsNormalScheme.of_pred hN
  have := isNormalScheme_of_smooth p
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  let W : Y.Opens :=
    IsNormalScheme.component ⟨_, irreducibleComponent_mem_irreducibleComponents y⟩
  have hy : y ∈ W := mem_irreducibleComponent
  have : IsIntegral W.toScheme := inferInstance
  let q : W.toScheme ⟶ X := W.ι ≫ p
  have := isDominant_pullback_fst_of_isOpenMap j q q.isOpenMap
  have : ∀ z, IsIso ((pullback.fst q j).stalkMap z) :=
    isIso_stalkMap_of_flat_of_surjectiveOnStalks _
  have := IsNormalScheme.of_isIso_stalkMap (pullback.fst q j)
  obtain ⟨k, _, _, t, _⟩ := exists_isDominant_geometricPoint_of_isPreimmersion (pullback.fst q j)
  obtain ⟨i, hi⟩ := hgeo k (t ≫ pullback.snd q j) (t ≫ pullback.fst q j ≫ W.ι)
    (by simp only [Category.assoc]; rw [← pullback.condition])
  have he : pullback.fst q j ≫ W.ι = pullback.snd q j ≫ σ i :=
    ext_of_isDominant_of_isSeparated p
      (by simp only [Category.assoc]; rw [hσ, ← pullback.condition]) t
      (by rw [hi, Category.assoc])
  have : Mono (pullback.snd q j ≫ σ i) := by rw [← he]; infer_instance
  have : Mono (pullback.snd q j) := mono_of_mono _ (σ i)
  exact ⟨i, W, hy, isOpenImmersion_of_etale_of_mono_pullback_snd j q, he⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearLiftOfIsMonHomPolAV
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_linear_lift_of_isMonHom_polAV :
    ∀ (P P' : Out.PolAV (Sp ℂ)) (L : LB P.A.left) (L' : LB P'.A.left) (u : HolUnif P.A L P.g) (u' : HolUnif P'.A L' P'.g) (f : P.A ⟶ P'.A), IsMonHom f → ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ), ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  intro P P' L L' u u' f hf
  obtain ⟨F, hF, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom P.A P'.A P.3 P'.3 L L' P.g P'.g u u'
    (GlobalTheory.TorusTransfer.tangent_bijective u' P'.5).1 (GlobalTheory.TorusTransfer.tangent_bijective u' P'.5).2 f hf
  exact ⟨F, hF⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPeriodDomainParam
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
theorem _root_.GlobalTheory.exists_period_domain_param :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTypeFn H D.p D.q ty → ∃ (B : Set (Fin D.dim → ℂ)) (P : (Fin D.dim → ℂ) → (D.La →+ (Fin g → ℂ))), IsOpen B ∧ Convex ℝ B ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolPeriods D ty B P ∧ ∀ P', _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P' → ∃! b, b ∈ B ∧ ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, P' a = h (P b a) := by
  intro E _ _ _ H D g ty hty
  obtain ⟨P₀, hP₀⟩ := _root_.GlobalTheory.PeriodNonempty.exists_isPeriod E H D g ty hty
  obtain ⟨m, B, P, hm, hB, hBc, -, -, hP, huniq⟩ :=
    _root_.GlobalTheory.PeriodChart.period_chart E H D g ty hty P₀ hP₀
  have hdim : m = D.dim := by
    have h2 : Module.finrank ℚ E = 2 * InfinitePlace.nrComplexPlaces E :=
      IsTotallyComplex.finrank E
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.dim
    rw [h2] at hm ⊢
    rw [Nat.mul_div_cancel_left _ two_pos]
    linarith
  subst hdim
  exact ⟨B, P, hB, hBc, hP, huniq⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SubsingletonSpDualNumber
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.DualRigidity

theorem eq_comp_section_of_const {X T Y : Scheme.{0}} (p : X ⟶ T) (ε : T ⟶ X) (g : X ⟶ Y)
    (h : ε ≫ p = 𝟙 T) (hs : Function.Surjective p.appTop.hom) (y : Y) (hy : ∀ x : X, g x = y) :
    g = p ≫ ε ≫ g := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  haveI : IsAffine W := hW
  have hr : Set.range g ⊆ Set.range (Scheme.Opens.ι W) := by
    rintro _ ⟨x, rfl⟩
    rw [hy x, Scheme.Opens.range_ι]
    exact hyW
  have key := GlobalTheory.eq_comp_section_of_surjective_appTop p ε (IsOpenImmersion.lift (Scheme.Opens.ι W) g hr) h hs
  have := congrArg (· ≫ Scheme.Opens.ι W) key
  simpa only [Category.assoc, IsOpenImmersion.lift_fac] using this

end GlobalTheory.DualRigidity
end

