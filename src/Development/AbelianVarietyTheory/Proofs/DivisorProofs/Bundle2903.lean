module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2870
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2634
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1522
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2782
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLatticeLocalBases
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1756
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2859
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeTorusCompare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusOpenFamilyOverLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2872
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2840
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FrameSqEqOfSymmetricThetaElement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepsXSt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionMetricSegmentPolynomial
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.SelfPoly

open MvPolynomial

theorem eval_pow_expand (Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    Θ ((C t * X 0 + X 1) ^ (D + 1)) = ∑ i ∈ Finset.range (D + 2),
      t ^ i * ((D + 1).choose i * Θ (X 0 ^ i * X 1 ^ (D + 1 - i))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [add_pow, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (C t * X 0) ^ i * X 1 ^ (D + 1 - i) * ((D + 1).choose i : MvPolynomial (Fin 2) ℝ)
      = C (t ^ i * (D + 1).choose i) * (X 0 ^ i * X 1 ^ (D + 1 - i)) := by
    rw [C_mul, C_pow, map_natCast]; ring
  rw [this, C_mul', LinearMap.map_smul, smul_eq_mul]; ring

theorem eval_mul_pow_expand (Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    Θ (X 0 * (C t * X 0 + X 1) ^ D) = ∑ j ∈ Finset.range (D + 1),
      t ^ j * (D.choose j * Θ (X 0 ^ (j + 1) * X 1 ^ (D - j))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [add_pow, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : X 0 * ((C t * X 0) ^ j * X 1 ^ (D - j) * (D.choose j : MvPolynomial (Fin 2) ℝ))
      = C (t ^ j * D.choose j) * (X 0 ^ (j + 1) * X 1 ^ (D - j)) := by
    rw [C_mul, C_pow, map_natCast]; ring
  rw [this, C_mul', LinearMap.map_smul, smul_eq_mul]; ring

def poly (Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (D + 2),
    Polynomial.C ((D + 1).choose i * Θ (X 0 ^ i * X 1 ^ (D + 1 - i))) * Polynomial.X ^ i

theorem poly_eval (Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    (poly Θ D).eval t = Θ ((C t * X 0 + X 1) ^ (D + 1)) := by
  rw [eval_pow_expand, poly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

theorem poly_derivative_eval (Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    (poly Θ D).derivative.eval t = ((D : ℝ) + 1) * Θ (X 0 * (C t * X 0 + X 1) ^ D) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eval_mul_pow_expand, poly, map_sum, Polynomial.eval_finsetSum, Finset.sum_range_succ', Finset.mul_sum]
  simp only [Polynomial.derivative_C_mul_X_pow, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, Nat.cast_zero, mul_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e₁ : D + 1 - (j + 1) = D - j := Nat.add_sub_add_right D 1 j
  have e₂ : (((D + 1).choose (j + 1) : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) = ((D : ℝ) + 1) * (D.choose j : ℝ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq D j).symm
  rw [e₁, Nat.add_sub_cancel]
  calc ((D + 1).choose (j + 1) : ℝ) * Θ (X 0 ^ (j + 1) * X 1 ^ (D - j)) * ((j + 1 : ℕ) : ℝ) * t ^ j
      = (((D + 1).choose (j + 1) : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) * (t ^ j * Θ (X 0 ^ (j + 1) * X 1 ^ (D - j))) := by ring
    _ = _ := by rw [e₂]; ring

end GlobalTheory.HSAmp.SelfPoly

namespace GlobalTheory.HSAmp.SelfPoly

open MvPolynomial HermLB

theorem selfInter_poly : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (u : SmFn p) (a a' : ℝ), L.IsSelfInter a → (up L u).IsSelfInter a' →
    ∃ s : Polynomial ℝ, s.eval 0 = a ∧ s.eval 1 = a' ∧
      ∀ t : ℚ, ((D : ℝ) + 1) / 2 * chInt (up L (u.smul t)) D u.u = s.derivative.eval (t : ℝ) := by
  intro H k _ X _ p D hX L u a a' ha ha'
  obtain ⟨Θ, hΘ⟩ := ((H.arExists k X p D hX).2 _ ![fnB u.u u.cInf u.conj, L]).1
  refine ⟨poly Θ D, ?_, ?_, fun t => ?_⟩
  · rw [poly_eval, map_zero, zero_mul, zero_add]
    exact (ha.unique hX (((H.arIso k X p D hX).2 _ _ _ hΘ).1 1)).symm
  · rw [poly_eval, map_one, one_mul]
    have i : (comb ![fnB u.u u.cInf u.conj, L] fun _ => 1).Isometric (up L u) := icls_eq_iff.1 (by
      show _ = (L.raise u.u u.cInf u.conj).icls
      rw [← icls_eq_iff.2 (isometric_tens_fnB _ _ _ _), icls_tens, icls_comb, Fin.sum_univ_two,
        one_smul, one_smul, add_comm]
      rfl)
    rw [ha'.unique hX (i.isSelfInter hX (hΘ.1 _))]
    simp [lin, Fin.sum_univ_two]
  · rw [poly_derivative_eval]
    have hd : (t.den : ℝ) ≠ 0 := Nat.cast_ne_zero.2 t.den_nz
    have hq : (t.den : ℝ) * (t : ℝ) = t.num := by
      rw [Rat.cast_def]; field_simp
    let n : Fin 2 → ℤ := ![t.num, t.den]
    have h₁ := GlobalTheory.SelfCont.mixed_eq H hX u.cInf u.conj L hΘ n
    have h₂ := (GlobalTheory.SelfCont.isometric_comb_raise u.cInf u.conj L n).chInt_eq D u.u
    have h₃ : ((zp L (n 1)).raise (fun σ y => (n 0 : ℝ) * u.u σ y) (fun σ y => (u.cInf σ y).const_mul _)
        (GlobalTheory.SelfCont.isConj_mul u.conj _)).Isometric ((up L (u.smul t)).pow t.den) := icls_eq_iff.1 (by
      rw [← icls_eq_iff.2 (isometric_tens_fnB _ _ _ _), icls_tens, icls_pow]
      show _ = t.den • ((L.raise (u.smul t).u (u.smul t).cInf (u.smul t).conj).icls)
      rw [← icls_eq_iff.2 (isometric_tens_fnB _ _ _ _), icls_tens, icls_zp, smul_add, ← natCast_zsmul,
        ← natCast_zsmul, ← GlobalTheory.SelfCont.icls_fnB_mul (u.smul t).cInf (u.smul t).conj]
      congr 1
      refine icls_eq_iff.2 (isometric_of_eqOn fun σ _ y _ => ?_)
      show (t.den : ℤ) * ((t : ℝ) * u.u σ y) = (t.num : ℝ) * u.u σ y
      rw [← hq]; push_cast; ring)
    have h₄ := _root_.GlobalTheory.HSAmp.chInt_pow k X p D hX (up L (u.smul t)) t.den u.u
    have h₅ : (lin fun i => (n i : ℝ)) = C (t.den : ℝ) * (C (t : ℝ) * MvPolynomial.X 0 + MvPolynomial.X 1) := by
      simp only [lin, Fin.sum_univ_two, n, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [mul_add, ← mul_assoc, ← C_mul, hq]; push_cast; ring
    have h₆ : Θ (MvPolynomial.X 0 * (lin fun i => (n i : ℝ)) ^ D) = (t.den : ℝ) ^ D * Θ (MvPolynomial.X 0 * (C (t : ℝ) * MvPolynomial.X 0 + MvPolynomial.X 1) ^ D) := by
      rw [h₅, mul_pow, ← C_pow, mul_left_comm, C_mul', LinearMap.map_smul, smul_eq_mul]
    have key : (t.den : ℝ) ^ D * chInt (up L (u.smul t)) D u.u =
        (t.den : ℝ) ^ D * (2 * Θ (MvPolynomial.X 0 * (C (t : ℝ) * MvPolynomial.X 0 + MvPolynomial.X 1) ^ D)) := by
      rw [← h₄, ← h₃.chInt_eq, ← h₂]
      linarith
    have := mul_left_cancel₀ (pow_ne_zero D hd) key
    rw [this]; ring

end GlobalTheory.HSAmp.SelfPoly
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCommGroupSchemeHomTangentAtOriginSurjectiv
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

noncomputable section

namespace GlobalTheory.LieSurjLocal

theorem map_surjective : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G B : Over (Sp R)) [GrpObj G] [GrpObj B] [IsCommMonObj G] [IsCommMonObj B] (q : G ⟶ B) [IsMonHom q], Smooth q.left → ∀ u : TanM (𝟙 (Sp R)) B, ∃ v : TanM (𝟙 (Sp R)) G, tv v ≫ q = tv u := by
  intro R _ _ G B _ _ _ _ q _ hsm u
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  let π : CommRingCat.of (DualNumber R) ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom
  have hπ : Function.Surjective π := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  have hn : IsNilpotent (RingHom.ker π.hom) := ⟨2, by
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx', hy']⟩
  have hu : Spec.map π ≫ (tv u).left = η[B].left := GlobalTheory.RayBasis.isTangent_pt u
  have h0 : η[G].left ≫ q.left = Spec.map π ≫ (tv u).left :=
    (congrArg (·.left) (IsMonHom.one_hom q)).trans hu.symm
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ :=
    GlobalTheory.exists_isAffineOpen_pair q.left (η[G].left (IsLocalRing.closedPoint R)) (O := ⊤) trivial
  obtain ⟨x, hx, hq⟩ := GlobalTheory.exists_lift_of_smooth_of_isAffineOpen q.left hU hV hVU π
    (tv u).left η[G].left h0
    (GlobalTheory.range_subset_opens_of_isLocalRing _ (by
      have : IsLocalHom π.hom := .of_surjective _ hπ
      have e : q.left (η[G].left (IsLocalRing.closedPoint R)) =
        (tv u).left (Spec.map π (IsLocalRing.closedPoint R)) := congr($h0 (IsLocalRing.closedPoint R))
      rw [← Spec_closedPoint (f := π), ← e]
      exact hVU hxV))
    (GlobalTheory.range_subset_opens_of_isLocalRing _ hxV) (by
      intro R' S _ _ _ _ _ _ p hp φ
      have hs : Function.Surjective p := fun c => (hπ c).imp fun b hb => (hp b).trans hb
      have hk : IsNilpotent (RingHom.ker p.toRingHom) := by
        convert hn using 1
        exact Ideal.ext fun b => Eq.congr_left (hp b)
      exact ⟨Algebra.FormallySmooth.liftOfSurjective φ p hs hk,
        Algebra.FormallySmooth.comp_liftOfSurjective φ p hs hk⟩)
  let xo : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G :=
    Over.homMk x (by rw [← Over.w q, reassoc_of% hq]; exact Over.w (tv u))
  have hz : smT (𝟙 (Sp R)) 0 xo = 1 := by
    apply Over.OverMorphism.ext
    rw [smT_left, Hom.one_def, Over.comp_left, Over.toUnit_left]
    show spMap _ ≫ x = (spMap (algebraMap R (DualNumber R)) ≫ 𝟙 _) ≫ _
    rw [Category.comp_id, ← hx, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    ext <;> simp [π, epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  exact ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT xo hz, Over.OverMorphism.ext hq⟩

end GlobalTheory.LieSurjLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapDualMapCompEq
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
namespace GlobalTheory.HeatV

open GlobalTheory.LogKSBal GlobalTheory.KS GlobalTheory.TangentOrigin

theorem spMap_resV (R : Type) [CommRing R] (c : R) : spMap (resV R c) = chart (bo R c) := by
  have h := (isAffineOpen_top (Sp R)).map_fromSpec (bo R c).2
    (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c))).op
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  exact h

theorem exists_isTr {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S]
    (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v : TanM (𝟙 (Sp R)) G) : ∃ w, IsTr G φ g v w := by
  have e : (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap S (DualNumber S)).comp φ := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have h1 : (tv v).left ≫ G.hom = spMap (algebraMap R (DualNumber R)) := (Over.w (tv v)).trans (Category.comp_id _)
  have h2 : (spMap (dualMap φ) ≫ (tv v).left) ≫ G.hom = (tEpsG (g ≫ G.hom)).hom := by
    show _ = spMap (algebraMap S (DualNumber S)) ≫ g ≫ G.hom
    rw [Category.assoc, h1, hg, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]
  exact ⟨_, Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ g) (Category.assoc _ _ _),
    Over.homMk (spMap (dualMap φ) ≫ (tv v).left) h2, rfl, rfl, rfl⟩

theorem spMap_dualMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (dualMap (g.comp f)) = spMap (dualMap g) ≫ spMap (dualMap f) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap]

theorem ksRel_operators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R), (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (c : R), c = ∏ i, tt i → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (DV : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), IsKS t (GlobalTheory.HeatV.bo R c).1 (GlobalTheory.HeatV.bo R c) (fun a => spMap (dualMap (GlobalTheory.HeatV.resV R c)) ≫ (tv (v' a)).left) DV Θ₁ → ∃ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → Fld t.G.left) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 ∧ (∀ i, W i ≤ t.PP.L.U (j i)) ∧ (∀ i, IsField (W i) (d i)) ∧ (∀ i O (h : O ≤ W i) (a : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), d i O (GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) a) = GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) (DV a)) ∧ (∀ i i' O (h : O ≤ W i ⊓ W i') (f : Γ(t.G.left, O)), d i O f - d i' O f = ∑ a, ∑ b, GlobalTheory.HeatV.cst t.G.hom (GlobalTheory.HeatV.bo R c).1 (h.trans (inf_le_left.trans (hW i))) (Θ₁ a b) * (dd' b O (rsT (t.PP.L.g (j i) (j i')).val O) * rsT (t.PP.L.g (j i) (j i'))⁻¹.val O) * dd' a O f) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt _ _ c _ n v' dd' hdd DV Θ₁ hKS
  obtain ⟨J, W, j, d, hcov, hWj, hfld, hlift, hdiff⟩ := hKS
  rw [inf_idem] at hcov
  have hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (bo R c).1 := fun i => (le_iSup W i).trans hcov.le
  refine ⟨J, W, j, d, hW, hcov, hWj, hfld, fun i O h a => ?_, fun i i' O h f => ?_⟩
  · have e : ∀ s : Γ(Sp R, (bo R c).1), cst t.G.hom _ (h.trans (hW i)) s = resG _ h (cst t.G.hom _ (hW i) s) := fun s => by
      rw [← rsT_of_le h, ← pbT_of_le, ← pbT_of_le, rsT_pbT t.G.hom (hW i) h]
    rw [e, e, (hfld i).2.2 _ _ h le_rfl, hlift]
  · refine ext_valR _ _ fun S _ x hx => ?_
    have hO : O ≤ t.G.hom ⁻¹ᵁ (bo R c).1 := h.trans (inf_le_left.trans (hW i))
    have hr : Set.range (x ≫ t.G.hom) ⊆ Set.range (chart (bo R c)) := by
      rintro _ ⟨p, rfl⟩
      exact (bo R c).2.range_fromSpec.superset (hO (hx (Set.mem_univ p)))
    have : IsOpenImmersion (chart (bo R c)) := (bo R c).2.isOpenImmersion_fromSpec
    obtain ⟨φ, hφ⟩ : ∃ φ : Γ(Sp R, (bo R c).1) →+* S, x ≫ t.G.hom = spMap φ ≫ chart (bo R c) :=
      ⟨(Spec.preimage (IsOpenImmersion.lift _ _ hr)).hom, by
        rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
    have hφ' : x ≫ t.G.hom = spMap (φ.comp (resV R c)) := by
      rw [hφ, ← spMap_resV, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    choose w hw using fun a => exists_isTr t.G _ x hφ' (v' a)
    have key := hdiff i i' O h f S φ x w hφ hx fun a => by
      obtain ⟨g', u, h₁, h₂, h₃⟩ := hw a
      exact ⟨g', u, h₁, by rw [h₂, spMap_dualMap_comp_eq, Category.assoc], h₃⟩
    have hOg : O ≤ t.PP.L.U (j i) ⊓ t.PP.L.U (j i') := fun p hp => ⟨hWj i (h hp).1, hWj i' (h hp).2⟩
    have hxg : ⊤ ≤ x ⁻¹ᵁ (t.PP.L.U (j i) ⊓ t.PP.L.U (j i')) := fun p hp => hOg (hx hp)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [key, valR_eq x hx, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, map_mul, map_mul, ← valR_eq, ← valR_eq, ← valR_eq, ← valR_eq,
      (hdd a).2 S _ x (w a) O f hφ' hx (hw a), (hdd b).2 S _ x (w b) _ _ hφ' hxg (hw b), valR_rsT x hOg hx,
      rsT_of_le hOg, (hdd b).1.2.2 _ _ hOg le_top, ← rsT_of_le hOg, valR_rsT x hOg hx, ← pbT_of_le,
      valR_pbT x _ hO hx, hφ, valR_chart]

end GlobalTheory.HeatV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleHypothesesOfStanding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FunObj

theorem squareTriple_of_standing {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}
    (hL : L.Is μ₀) (W : G.Weil) (t : T) (i j : Fin D.R.m) (hst : SquareStanding G t) : SquareTriple W t i j := by
  intro M hM
  obtain ⟨S₀, Q, hSQ, hX⟩ := _root_.GlobalTheory.FunObj.squareChars_isGood hL t i j hst
  choose τf hτf using (_root_.GlobalTheory.ConjTypeOverReal.conj_tauE_over_realPlace (D := D))
  obtain ⟨mα, mβ, hα, hβ, hκ⟩ := _root_.GlobalTheory.SquareExps.exps hL t i j hst τf hτf
  obtain ⟨v₁, hv₁P, hv₁s, hv₁l, ⟨τ₁⟩⟩ := _root_.GlobalTheory.GoodPlace.exists_good_place (G := G) hL t (S₀ ∪ Q)
  have hτP : ∀ v : (S₀ ∪ Q : Finset (HeightOneSpectrum (𝓞 D.host.F))),
      Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v) := fun v => (hSQ v v.2).2
  let B : Base D.host.F D.host.E :=
    ⟨W.ψ, fun w => ⟨_, hτf w⟩, mα, mβ, S₀ ∪ Q, fun v => (hτP v).some, v₁, τ₁⟩
  have hB : B.IsGood D.sp.cm.sig := _root_.GlobalTheory.FunObj.base_isGood_of_standing hL W t hst B rfl fun v hv => (hSQ v hv).1
  have hemb : ∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x) := fun _ _ => rfl
  obtain ⟨e⟩ := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.nonempty_num (G := G) (i := i) (j := j) hL (by omega) (by omega)
  obtain ⟨ΛV, basV, hV⟩ := _root_.GlobalTheory.FunObj.isHerm_spaceW hL W i j B τf hemb
  obtain ⟨ΛV', basV', hV'⟩ := _root_.GlobalTheory.TripleSpace.negConj_isHerm hL W i j B τf hemb
  obtain ⟨ΛW, basW, hW⟩ := _root_.GlobalTheory.SkewLat.bigSpace_isSkew hL W i j e B τf hemb
  obtain ⟨co, vac, dom, hMo⟩ := GlobalTheory.T.exists_goodSchrodingerModel_conjugateDoubled hL t i j M hM B hB _ _ rfl _ _ _ _ hV hW
  obtain ⟨co', vac', dom', hMo'⟩ := GlobalTheory.T.squareModel_negSpace_goodSchroedinger hL t i j M hM B hB _ _ rfl _ _ _ _ hV' hW
  obtain ⟨om, hom⟩ := _root_.GlobalTheory.WeilTripleW.exists_isWeil hL t i j hst B hB _ _ _ _ _ _ hV hW _ hMo
  obtain ⟨om', hom'⟩ := _root_.GlobalTheory.FunObj.squareWeil₁ hL t i j hst B hB _ _ _ _ _ _ hV' hW _ hMo'
  obtain ⟨h1, h2, h3, h4⟩ := _root_.GlobalTheory.Div.SquareRanks.square_ranks (G := G) hL i j
  refine ⟨e, B, ⟨(D.R.m - j - 1) / 2, (D.R.m - j) / 2, _, _, _, Model.mk co vac ((M.ν (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))).map
      (conjU (spW G i j) (J := (1 : D.host.E) • (spW G i j).gram) 1 rfl)) dom,
    Model.mk co' vac' ((M.ν (.grid (i : ℕ) (j : ℕ))).map
      (conjU (spW₁ G i j) (J := (-1 : D.host.E) • (spW₁ G i j).gram) (-1) rfl)) dom'⟩,
    ⟨alpha G t i j, beta G i j, S₀, Q⟩, om, om', ?_, ?_, hv₁l⟩
  · exact ⟨rfl, rfl, rfl, rfl, fun w => ⟨τf w, fun _ => rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
  · exact ⟨hB, ⟨h1, h2, hκ, h3, h4, hV, hV', hW, hMo, hMo'⟩, hX B subset_rfl hv₁P hv₁s hα hβ, hom, hom'⟩

end GlobalTheory.FunObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureH1NakayamaClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct

namespace GlobalTheory.AbCohFibre

theorem mem_smul_top_of_tmul_tmul_eq_zero {R S M : Type} [CommRing R] [CommRing S] [Algebra R S] (m : Ideal R)
    [Algebra S (R ⧸ m)] [IsScalarTower R S (R ⧸ m)] [AddCommGroup M] [Module R M] (x : M)
    (hx : ((1 : R ⧸ m) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] x) : (R ⧸ m) ⊗[S] (S ⊗[R] M)) = 0) :
    x ∈ m • (⊤ : Submodule R M) := by
  have h1 := congrArg (AlgebraTensorModule.cancelBaseChange R S (R ⧸ m) (R ⧸ m) M) hx
  rw [AlgebraTensorModule.cancelBaseChange_tmul, one_smul, map_zero] at h1
  have h2 := congrArg (TensorProduct.quotTensorEquivQuotSMul M m) h1
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero, Submodule.Quotient.mk_eq_zero] at h2
  exact h2

theorem mem_smul_top_of_pull_eq_zero : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (m : Ideal R), m.IsMaximal → ∀ (Y : Scheme.{0}) (s' : Y ⟶ Sp (R ⧸ m)) (φ : Y ⟶ A.left) (h : IsPullback φ s' A.hom (spMap (algebraMap R (R ⧸ m)))) (x : GlobalTheory.CechDR.HO1 A.hom), GlobalTheory.CechDR.pullHO1 h.w x = 0 → x ∈ m • (⊤ : Submodule R (GlobalTheory.CechDR.HO1 A.hom)) := by
  intro R _ A _ hA m hm Y s' φ h x hx
  haveI : m.IsMaximal := hm
  haveI : m.IsPrime := hm.isPrime
  let f := spMap (algebraMap R (Localization.AtPrime m))
  letI : GrpObj ((Over.pullback f).obj A) := Functor.grpObjObj
  have hAm : IsAbelianScheme ((Over.pullback f).obj A) := GlobalTheory.AbLaw.CubeGen.isAb_baseChange hA f
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim (Localization.AtPrime m) ((Over.pullback f).obj A) hAm
  have hsq0 : IsPullback (pullback.fst A.hom f) ((Over.pullback f).obj A).hom A.hom f :=
    IsPullback.of_hasPullback A.hom f
  have := hA.proper
  obtain ⟨⟨e₁, he₁⟩, -⟩ := GlobalTheory.AbCoh.flat_baseChange_HO R (Localization.AtPrime m) A.left _ A.hom _ _ hsq0
    inferInstance inferInstance
  obtain ⟨-, -, hbc, -⟩ := GlobalTheory.AbCoh.oStr (Localization.AtPrime m) ((Over.pullback f).obj A) g hAm hg
  let ψ : Localization.AtPrime m →+* R ⧸ m :=
    IsLocalization.lift (M := m.primeCompl) (g := Ideal.Quotient.mk m) (fun y : m.primeCompl => by
      show IsUnit (Ideal.Quotient.mk m (y : R))
      have hy : Ideal.Quotient.mk m (y : R) ≠ 0 := by rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact y.2
      letI := Ideal.Quotient.field m
      exact isUnit_iff_ne_zero.mpr hy)
  letI : Algebra (Localization.AtPrime m) (R ⧸ m) := ψ.toAlgebra
  have hcomp : (algebraMap (Localization.AtPrime m) (R ⧸ m)).comp (algebraMap R (Localization.AtPrime m)) =
      algebraMap R (R ⧸ m) := IsLocalization.lift_comp _
  haveI : IsScalarTower R (Localization.AtPrime m) (R ⧸ m) := IsScalarTower.of_algebraMap_eq'  hcomp.symm
  have hsp : spMap (algebraMap (Localization.AtPrime m) (R ⧸ m)) ≫ f = spMap (algebraMap R (R ⧸ m)) := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  let φ' : Y ⟶ ((Over.pullback f).obj A).left :=
    pullback.lift φ (s' ≫ spMap (algebraMap (Localization.AtPrime m) (R ⧸ m))) (by
      rw [h.w, Category.assoc, hsp])
  have hφ' : φ' ≫ pullback.fst A.hom f = φ := pullback.lift_fst _ _ _
  have hs' : φ' ≫ ((Over.pullback f).obj A).hom = s' ≫ spMap (algebraMap (Localization.AtPrime m) (R ⧸ m)) :=
    pullback.lift_snd _ _ _
  have hbig : IsPullback (φ' ≫ pullback.fst A.hom f) s' A.hom
      (spMap (algebraMap (Localization.AtPrime m) (R ⧸ m)) ≫ f) := by
    rw [hφ', hsp]; exact h
  have hsq : IsPullback φ' s' ((Over.pullback f).obj A).hom (spMap (algebraMap (Localization.AtPrime m) (R ⧸ m))) :=
    IsPullback.of_right hbig hs' hsq0
  obtain ⟨e₂, he₂⟩ := hbc (R ⧸ m) Y s' φ' hsq
  have cong : ∀ (φ₁ : Y ⟶ A.left) (σ₁ : R →+* R ⧸ m) (h₁ : φ₁ ≫ A.hom = s' ≫ spMap σ₁), φ₁ = φ →
      σ₁ = algebraMap R (R ⧸ m) → GlobalTheory.CechDR.pullHO1 h₁ x = GlobalTheory.CechDR.pullHO1 h.w x := by
    rintro _ _ _ rfl rfl; rfl
  have h'' : (φ' ≫ pullback.fst A.hom f) ≫ A.hom =
      s' ≫ spMap ((algebraMap (Localization.AtPrime m) (R ⧸ m)).comp (algebraMap R (Localization.AtPrime m))) := by
    rw [hφ', hcomp]; exact h.w
  have key : GlobalTheory.CechDR.pullHO1 hsq.w (GlobalTheory.CechDR.pullHO1 hsq0.w x) = 0 := by
    rw [GlobalTheory.CechDR.pullHO1_comp hsq0.w hsq.w h'', cong _ _ h'' hφ' hcomp]
    exact hx
  have k1 : ((1 : R ⧸ m) ⊗ₜ[Localization.AtPrime m] (GlobalTheory.CechDR.pullHO1 hsq0.w x)) = 0 := by
    apply e₂.injective
    rw [he₂, map_zero]; exact key
  have k2 := congrArg (LinearMap.lTensor (R ⧸ m) e₁.symm.toLinearMap) k1
  rw [LinearMap.lTensor_tmul, map_zero, ← he₁, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at k2
  exact mem_smul_top_of_tmul_tmul_eq_zero m x k2

end GlobalTheory.AbCohFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetrySignsTwoTorsionRelationOfLbIsoStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetry_signs_two_torsion_relation_of_lbIso : AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, LBIso U.LG.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → ∃ σ : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(ι[A.A]).left, 𝟙 A.A.left] ![1, -1]), σ.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ σ (eSec A.A)) (LB.oneGen A.L) ∧ ∀ (T : Over (Spec (CommRingCat.of (FractionRing R)))) (x : T ⟶ A.A), x ^ 2 = 1 → ∀ z J, Good A.L z J → val σ (x * (x ≫ oA.act w)).left z J = val σ x.left z J ^ 2 * val σ (x ≫ oA.act w).left z J := by
  first | exact @GlobalTheory.SignSym.sign_sym | exact GlobalTheory.SignSym.sign_sym | (intros; apply GlobalTheory.SignSym.sign_sym <;> assumption)
end

