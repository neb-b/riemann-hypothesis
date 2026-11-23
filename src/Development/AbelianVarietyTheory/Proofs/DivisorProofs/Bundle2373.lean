module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0486
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0590
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1995
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionExtendsAbLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2323
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTauLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackGenMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.TauFormHom

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues GlobalTheory.TauForm

theorem isGrpPullback_genMap {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal R) D A G) : IsGrpPullback A.A G (jK R) (genMap U) := by
  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := by show IsMonHom U.gen.inv; infer_instance
  exact ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK R))).congr
    (Category.id_comp _) rfl

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (p : G' ⟶ G), IsMonHom p → ∀ (ρ : D.toPre.X →+ D'.toPre.X) (s : D'.toPre.X →+ D.toPre.X), TorMatch U U' (RingHom.id R) p.left ρ → (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), IsUnit (k : R) → ∀ (q : QkPt D.toPre F k) (q' : QkPt D'.toPre F k) (a : TFK (R := R) F ⟶ A.A) (a' : TFK (R := R) F ⟶ A'.A), QkToAkU U.toUnifPre F k q a → QkToAkU U'.toUnifPre F k q' a' → a.left ≫ genMap U = a'.left ≫ genMap U' ≫ p.left → ∃ z, q.y = s q'.y + k • z) → ∀ (a' : D'.toPre.X) (b : D.toPre.X) (x x' : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D.toPre (s a') b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D'.toPre a' (ρ b) x' → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * (x' : FractionRing R) := by
  intro R _ _ _ hRb hdvr G _ _ hG D A U G' _ _ hG' D' A' U' P hP ρ s hM hlab a' b x x' hx hx'
  haveI := hdvr
  obtain ⟨hR, hR0⟩ := id hRb
  obtain ⟨-, -, -, hRc⟩ := id hR
  haveI := hRc
  haveI := hR0
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let F := AlgebraicClosure (FractionRing R)
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv (isGrpPullback_genMap U) (TFK (R := R) F)
    ((TFK (R := R) F).hom ≫ jK R) rfl
  obtain ⟨e', he'⟩ := GlobalTheory.LiePull.exists_pushEquiv (isGrpPullback_genMap U') (TFK (R := R) F)
    ((TFK (R := R) F).hom ≫ jK R) rfl
  let Pm : (Over.mk ((TFK (R := R) F).hom ≫ jK R) ⟶ G') →* (Over.mk ((TFK (R := R) F).hom ≫ jK R) ⟶ G) :=
    { toFun := fun y => y ≫ P, map_one' := MonObj.one_comp P, map_mul' := fun y y' => MonObj.mul_comp y y' P }
  have hPm : ∀ y, (Pm y).left = y.left ≫ P.left := fun y => Over.comp_left (f := y) (g := P)
  have key : ∀ k : ℕ, IsUnit (k : R) → (k : ℤ) ∣ (ord_vw R).toFun x - (ord_vw R).toFun x' := by
    intro k hk
    obtain ⟨O, φ, σ, π, h₁, h₂, h₃, h₄, h₅⟩ := _root_.GlobalTheory.InertiaTameRoot.exists_inertia_moves_root R F ϖ hϖ k hk
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
    have hkO : IsUnit (k : O) := by simpa using hk.map φ
    obtain ⟨f, ⟨i₁, s₁, -, a₁, w₁⟩, p₁⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR D A G hG U F k hk1
    obtain ⟨f', ⟨i₂, s₂, -, a₂, w₂⟩, p₂⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR D' A' G' hG' U' F k hk1
    have wt₁ : ∀ (p p' : QkPt D.toPre F k) (τ : Multiplicative D.toPre.X →* Fˣ), p.y = 0 → GlobalTheory.UT.IsTor τ p.g →
        WeilIs A.A A.L (k : ℤ) (f p) (f p') (unitOn (τ (Multiplicative.ofAdd p'.y))) := fun p p' τ hy hτ =>
      (w₁ p p' _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns p p' hy hτ)
    have c₁ : ∀ p p', QkExt σ.toRingHom p p' → (f p').left = spMap σ.toRingHom ≫ (f p).left := by
      intro p p' hpp'
      obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hR D A G hG U F F σ k hk1 p
      obtain ⟨y, hy⟩ := hx (f p)
      have : y = f p' := (i₁ p' y).1 ((hiff p' (f p) y hpp' hy).1 ((i₁ p (f p)).2 rfl))
      rw [← this, hy]
    have c₂ : ∀ p p', QkExt σ.toRingHom p p' → (f' p').left = spMap σ.toRingHom ≫ (f' p).left := by
      intro p p' hpp'
      obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hR D' A' G' hG' U' F F σ k hk1 p
      obtain ⟨y, hy⟩ := hx (f' p)
      have : y = f' p' := (i₂ p' y).1 ((hiff p' (f' p) y hpp' hy).1 ((i₂ p (f' p)).2 rfl))
      rw [← this, hy]
    have uniq : ∀ (u v : TFK (R := R) F ⟶ A.A) (c c' : Fˣ), WeilIs A.A A.L (k : ℤ) u v (unitOn c) →
        WeilIs A.A A.L (k : ℤ) u v (unitOn c') → c = c' := fun u v c c' h h' =>
      GlobalTheory.weilIs_unique_fieldPoint _ A.A A.L A.isLB F _ k u v c c' h h'

    obtain ⟨p', hp'⟩ := GlobalTheory.TorusExt.exists_qkPt (F := F) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1) hB' hk0 a'
    obtain ⟨q, hq⟩ := s₁ (e.symm (Pm (e' (f' p')))) (by rw [← map_pow, ← map_pow, ← map_pow, p₂, map_one, map_one, map_one])
    have hqe : e (f q) = Pm (e' (f' p')) := by rw [hq, e.apply_symm_apply]
    have hql : (f q).left ≫ genMap U = (f' p').left ≫ genMap U' ≫ P.left := by
      rw [← he, hqe, hPm, he', Category.assoc]
    obtain ⟨z, hz⟩ := hlab F k hk q p' (f q) (f' p') ((i₁ _ _).2 rfl) ((i₂ _ _).2 rfl) hql
    rw [hp'] at hz

    obtain ⟨r, hr, -⟩ := GlobalTheory.TorusExt.existsUnique_qkExt hB σ.toRingHom (RingHom.ext σ.commutes) q
    obtain ⟨r', hr', -⟩ := GlobalTheory.TorusExt.existsUnique_qkExt hB' σ.toRingHom (RingHom.ext σ.commutes) p'
    obtain ⟨τ₁, q₁, -, y₁, t₁, d₁, v₁⟩ := GlobalTheory.KummerConj.conj_eq_add_tor R _ hB F O φ h₂ k σ q r hr
      (GlobalTheory.InertiaFix.sigma_fixes_abelianPart R _ hB F O φ h₂ k hkO σ h₃ q)
    obtain ⟨τ₂, q₂, k₂, y₂, t₂, d₂, v₂⟩ := GlobalTheory.KummerConj.conj_eq_add_tor R _ hB' F O φ h₂ k σ p' r' hr'
      (GlobalTheory.InertiaFix.sigma_fixes_abelianPart R _ hB' F O φ h₂ k hkO σ h₃ p')
    have hr₁ : e (f r) = Pm (e' (f' r')) := Over.OverMorphism.ext (by
      rw [he, hPm, he', c₁ q r hr, c₂ p' r' hr']
      simp only [Category.assoc, hql])
    have hq₁ : e (f q₁) = Pm (e' (f' q₂)) := by
      rw [a₁ _ _ _ d₁, a₂ _ _ _ d₂, map_mul, map_mul, map_mul, hqe] at hr₁
      exact mul_left_cancel hr₁
    obtain ⟨qT, yT, tT⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor hB (k := k) (F := F)
      (τ₂.comp (AddMonoidHom.toMultiplicative ρ)) (MonoidHom.ext fun χ => DFunLike.congr_fun k₂ _)
    have hT := hM F (fun _ => rfl) k hk _ τ₂ qT q₂ (f qT) (f' q₂) k₂ (fun _ => rfl) yT tT y₂ t₂
      ((i₁ _ _).2 rfl) ((i₂ _ _).2 rfl)
    have hfq : f qT = f q₁ := e.injective (by
      rw [hq₁]
      exact Over.OverMorphism.ext (by rw [he, hPm, he', hT, Category.assoc]))
    obtain ⟨pb, rfl⟩ := GlobalTheory.TorusExt.exists_qkPt (F := F) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1) hB hk0 b
    have hτ : τ₁ (Multiplicative.ofAdd pb.y) = τ₂ (Multiplicative.ofAdd (ρ pb.y)) := by
      have h := wt₁ qT pb _ yT tT
      rw [hfq] at h
      exact uniq _ _ _ _ (wt₁ q₁ pb τ₁ y₁ t₁) h

    obtain ⟨xq, hxq⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D.toPre q.y pb.y
    obtain ⟨xz, hxz⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D.toPre z pb.y
    obtain ⟨u, hu⟩ := GlobalTheory.TauShift.main R D.toPre hB (s a') z pb.y k x xz xq hx hxz (by rw [← hz]; exact hxq)
    obtain ⟨t, t0, tv, tσ⟩ := v₁ _ xq hxq
    obtain ⟨t', t0', tv', tσ'⟩ := v₂ _ x' (by rw [hp']; exact hx')
    have dv := GlobalTheory.Member.TameDivOrd.tame_fixed_dvd_ord R F ϖ hϖ k O φ σ π hkO h₁ h₂ h₃ h₄ h₅ (t / t') (xq / x')
      (by rw [map_div₀, tσ, tσ', hτ, mul_div_mul_left _ _ (Units.ne_zero _)])
      (by rw [map_div₀, div_pow, tv, tv', Units.val_div_eq_div_val, map_div₀, map_div₀])
    rw [val_div, hu, (ord_vw R).map_mul, (ord_vw R).map_unit, (ord_vw R).map_mul, val_pow, zero_add,
      nsmul_eq_mul] at dv
    have e₀ : (ord_vw R).toFun x - (ord_vw R).toFun x' =
        ((ord_vw R).toFun x + (k : ℤ) * (ord_vw R).toFun xz - (ord_vw R).toFun x') - (k : ℤ) * (ord_vw R).toFun xz := by
      ring
    rw [e₀]
    exact dvd_sub dv (dvd_mul_right _ _)
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℕ, 2 ≤ l ∧ IsUnit (l : R) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := (3 : R)) (b := -2) (by norm_num) with h | h
    · exact ⟨3, by norm_num, by simpa using h⟩
    · exact ⟨2, le_rfl, by simpa using h.neg⟩
  exact GlobalTheory.TauForm.exists_unit_of_ord_eq (W := R) (x := x) (y := x') (by
    rw [← sub_eq_zero]
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (key (l ^ Int.natAbs
      ((ord_vw R).toFun x - (ord_vw R).toFun x')) (by simpa using hl.pow _)) ?_
    rw [Int.natAbs_natCast]
    exact Nat.lt_pow_self (by omega))

end GlobalTheory.TauFormHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackSelf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LevSpread

theorem eq_of_comp_eq {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) (Z : Over S) [PreconnectedSpace Z.left] (x y : Z ⟶ A) (hx : x ^ n = 1)
    (hy : y ^ n = 1) (T : Over S) (z : T ⟶ Z) [Nonempty T.left] (h : z ≫ x = z ≫ y) : x = y := by
  have hw : (x * y⁻¹) ^ n = 1 := by rw [mul_pow, inv_pow, hx, hy, inv_one, _root_.mul_one]
  obtain ⟨C, hC, hz⟩ := GlobalTheory.TorsionCover.exists_clopen_eq_one A hA hn (x * y⁻¹) hw
  have h1 : z ≫ (x * y⁻¹) = 1 := by
    show (preHom z) (x * y⁻¹) = 1
    rw [map_mul, map_inv]
    show (z ≫ x) * (z ≫ y)⁻¹ = 1
    rw [h, mul_inv_cancel]
  have hsub := (hz T z).1 h1
  obtain ⟨p⟩ := ‹Nonempty T.left›
  have hne : C.Nonempty := ⟨_, hsub ⟨p, rfl⟩⟩
  have huniv : C = Set.univ := hC.eq_univ hne
  have h2 : 𝟙 Z ≫ (x * y⁻¹) = 1 := (hz Z (𝟙 Z)).2 (by rw [huniv]; exact Set.subset_univ _)
  rw [Category.id_comp] at h2
  exact mul_inv_eq_one.1 h2

theorem isGrpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

end GlobalTheory.LevSpread

namespace GlobalTheory.LevSpread

theorem l1 : ∀ (S T : Scheme.{0}) (A₀ : Over T) [GrpObj A₀] [IsCommMonObj A₀] (P₀ : LB (G2 A₀).left) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) (f : T ⟶ S), P₀.IsLB → P.IsLB → SameFib A₀ P₀ (𝟙 _) A P f → ∃ (φ : A₀.left ⟶ A.left) (φ₂ : (G2 A₀).left ⟶ (G2 A).left), IsGrpPullback A₀ A f φ ∧ IsSquare φ φ₂ ∧ LBIso P₀ (P.pull φ₂) ∧ LBIso (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) := _root_.GlobalTheory.FibrePull.fibre_isPull

theorem l2a : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsIntegrallyClosed R₀] (A : Over (Sp R₀)) [GrpObj A] [IsCommMonObj A] (n : ℕ), IsAbelianScheme A → IsUnit (n : R₀) → TorsRat A n → ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ Sp R₀) (x : Over.mk t ⟶ A), x ^ n = 1 → ∃ σ : 𝟙_ (Over (Sp R₀)) ⟶ A, σ ^ n = 1 ∧ toUnit (Over.mk t) ≫ σ = x := _root_.GlobalTheory.TorsConst.exists_section_of_torsRat

theorem l2 : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsIntegrallyClosed R₀] (A : Over (Sp R₀)) [GrpObj A] [IsCommMonObj A] (n : ℕ), IsAbelianScheme A → IsUnit (n : R₀) → TorsRat A n → ∀ (K : Type) [Field K] (t : Sp K ⟶ Sp R₀) (x : Over.mk t ⟶ A), x ^ n = 1 → ∃ σ : 𝟙_ (Over (Sp R₀)) ⟶ A, σ ^ n = 1 ∧ toUnit (Over.mk t) ≫ σ = x := by
  intro R₀ _ _ _ _ A _ _ n hA hnR hT K _ t x hx
  have hnΓ : IsUnit (n : Γ(Sp R₀, ⊤)) := by
    have := hnR.map (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom
    rwa [map_natCast] at this
  let t' : Sp (AlgebraicClosure K) ⟶ Sp R₀ := spMap (algebraMap K (AlgebraicClosure K)) ≫ t
  let z : Over.mk t' ⟶ Over.mk t := Over.homMk (spMap (algebraMap K (AlgebraicClosure K))) rfl
  obtain ⟨σ, hσ, hσx⟩ := l2a R₀ A n hA hnR hT (AlgebraicClosure K) t' (z ≫ x)
    (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
  refine ⟨σ, hσ, ?_⟩
  haveI : PreconnectedSpace (Over.mk t).left := inferInstanceAs (PreconnectedSpace (Sp K))
  haveI : Nonempty (Over.mk t').left := inferInstanceAs (Nonempty (Sp (AlgebraicClosure K)))
  refine eq_of_comp_eq A hA hnΓ (Over.mk t) _ x (by rw [← MonObj.comp_pow, hσ, MonObj.comp_one]) hx (Over.mk t') z ?_
  rw [← Category.assoc, show z ≫ toUnit (Over.mk t) = toUnit (Over.mk t') from toUnit_unique _ _, hσx]

theorem l3 : ∀ (O : Type) [CommRing O] [IsDomain O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), IsPPol A P → ∀ (N : ℕ), 0 < N → IsUnit (N : O) → ∀ (u v : 𝟙_ (Over (Sp O)) ⟶ A), u ^ N = 1 → v ^ N = 1 → ∀ (ζ : Oˣ), IsPrimitiveRoot ζ N → ∀ (m : ℤ) (K : Type) [Field K] (κ : O →+* K), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap κ)) ≫ u) (toUnit (Over.mk (spMap κ)) ≫ v) (unitOn (Units.map κ.toMonoidHom (ζ ^ m))) → ∀ (k : Type) [Field k] (ρ : O →+* k), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap ρ)) ≫ u) (toUnit (Over.mk (spMap ρ)) ≫ v) (unitOn (Units.map ρ.toMonoidHom (ζ ^ m))) := _root_.GlobalTheory.WeilRoot.weilIs_zpow_of_fieldPoint

theorem prim_map {n : ℕ} (hn : n ≠ 0) {R : Type} [CommRing R] [IsDomain R] (β : cycAway n →+* R) :
    IsPrimitiveRoot (β (zetaAway n)) n := by
  have h₁ : IsPrimitiveRoot (zetaAway n) n :=
    IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn) Subtype.val_injective
  have : NeZero (n : R) := ⟨by simpa using ((isUnit_natCast hn).map β).ne_zero⟩
  have h₂ := (h₁.isRoot_cyclotomic (Nat.pos_of_ne_zero hn)).map (f := β)
  rwa [Polynomial.map_cyclotomic, Polynomial.isRoot_cyclotomic_iff] at h₂

theorem level_spreads : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsIntegrallyClosed R₀] (b : cycAway n →+* R₀) (A : Over (Sp R₀)) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → IsPPol A P → TorsRat A n → ∀ (g : ℕ) (K : Type) [Field K] (κ : R₀ →+* K) (c₀ : SiegPre g n (zetaAway n) (spMap (κ.comp b))), c₀.Principal → SameFib c₀.A c₀.P (𝟙 _) A P (spMap κ) → ∃ c : SiegPre g n (zetaAway n) (spMap b), c.Principal ∧ SiegPB c₀ c (spMap κ) ∧ ∃ (a : c.A.left ⟶ A.left) (a₂ : (G2 c.A).left ⟶ (G2 A).left), IsGrpPullback c.A A (𝟙 _) a ∧ IsSquare a a₂ ∧ LBIso c.P (P.pull a₂) := by
  intro n hn3 hnodd R₀ _ _ _ _ b A _ _ P hA hP hT g K _ κ c₀ hc₀ hsf
  have hn0 : n ≠ 0 := by omega
  have hnR : IsUnit (n : R₀) := by simpa using (isUnit_natCast hn0).map b
  have hnΓ : IsUnit (n : Γ(Sp R₀, ⊤)) := by
    have := hnR.map (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom
    rwa [map_natCast] at this

  have hζc : IsPrimitiveRoot (zetaAway n) n :=
    IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn0) Subtype.val_injective
  let ζU : (cycAway n)ˣ := (hζc.isUnit hn0).unit
  have hζU : (ζU : cycAway n) = zetaAway n := rfl
  let ζR : R₀ˣ := Units.map b.toMonoidHom ζU
  have hζR : IsPrimitiveRoot ζR n := IsPrimitiveRoot.coe_units_iff.1 (prim_map hn0 b)

  obtain ⟨φ, φ₂, hφ, hsq, hiso, hdiag⟩ := l1 _ _ c₀.A c₀.P A P (spMap κ) c₀.isLB hP.1.1 hsf
  let E := GlobalTheory.ObjPull.pushEquiv hφ (𝟙_ (Over (Sp K)))
  have hxa : ∀ a, (E (c₀.lev a)) ^ n = 1 := fun a => by rw [← map_pow, c₀.lev_tors, map_one]
  choose σ hσn hσx using fun a => l2 R₀ A n hA hnR hT K _ (E (c₀.lev a)) (hxa a)
  have hcomp : ∀ a, (c₀.lev a).left ≫ φ = spMap κ ≫ (σ a).left := fun a => by
    have e := congrArg (fun w => w.left) (hσx a)
    simp only [Over.comp_left, GlobalTheory.ObjPull.toUnit_left'] at e
    rw [← GlobalTheory.ObjPull.pushEquiv_left hφ, ← e]
    exact congrArg (· ≫ (σ a).left) (Category.id_comp _)
  haveI : PreconnectedSpace (𝟙_ (Over (Sp R₀))).left := inferInstanceAs (PreconnectedSpace (Sp R₀))
  have inj : ∀ (T : Over (Sp R₀)) [Nonempty T.left] (s s' : 𝟙_ (Over (Sp R₀)) ⟶ A), s ^ n = 1 → s' ^ n = 1 →
      toUnit T ≫ s = toUnit T ≫ s' → s = s' := fun T _ s s' hs hs' h =>
    eq_of_comp_eq A hA hnΓ (𝟙_ _) s s' hs hs' T (toUnit T) h
  haveI : Nonempty (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap κ)).left := inferInstanceAs (Nonempty (Sp K))
  have hadd : ∀ a a', σ (a + a') = σ a * σ a' := fun a a' =>
    inj _ _ _ (hσn _) (by rw [mul_pow, hσn, hσn, _root_.mul_one])
      (by rw [MonObj.comp_mul, hσx, hσx, hσx, c₀.lev_add, map_mul])
  have one_iff : ∀ (T : Over (Sp R₀)) [Nonempty T.left] a, toUnit T ≫ σ a = 1 ↔ σ a = 1 := fun T _ a =>
    ⟨fun h => inj T (σ a) 1 (hσn a) (one_pow n) (h.trans (MonObj.comp_one _).symm),
      fun h => by rw [h, MonObj.comp_one]⟩
  let c : SiegPre g n (zetaAway n) (spMap b) :=
    { A := A
      ab := hA
      P := P
      isLB := hP.1.1
      rig₁ := hP.1.2.1
      rig₂ := hP.1.2.2.1
      symm := hP.1.2.2.2
      lev := σ
      lev_add := hadd
      lev_tors := hσn
      geom := ?_ }
  refine ⟨c, ⟨hP.2.1, hP.2.2⟩, ⟨φ, φ₂, hφ, hsq, hiso, hcomp⟩,
    ⟨𝟙 _, 𝟙 _, isGrpPullback_self A, ⟨(Category.id_comp _).trans (Category.comp_id _).symm,
      (Category.id_comp _).trans (Category.comp_id _).symm⟩, GlobalTheory.ThetaAffineGlue.lbIso_pull_id hP.1.1⟩⟩
  intro k _ _ x β z hxβ hz
  obtain ⟨ρ, rfl⟩ : ∃ ρ : R₀ →+* k, spMap ρ = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  have hβ : β = ρ.comp b := by
    have e : spMap (ρ.comp b) = spMap β := by rw [← hxβ]; exact Spec.map_comp _ _
    exact (congrArg CommRingCat.Hom.hom (Spec.map_injective e)).symm
  have hzU : z = Units.map ρ.toMonoidHom ζR := Units.ext (by rw [hz, hβ]; rfl)
  subst hzU
  let iK : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  let x₀ : Sp (AlgebraicClosure K) ⟶ Sp K := spMap iK
  obtain ⟨g1, g2, g3⟩ := c₀.geom (AlgebraicClosure K) x₀ ((iK.comp κ).comp b)
    (Units.map ((iK.comp κ).comp b).toMonoidHom ζU) (by rw [← Spec.map_comp]; rfl) rfl
  let T₀ : Over (Sp R₀) := Over.mk ((Over.mk x₀).hom ≫ spMap κ)
  haveI : Nonempty T₀.left := inferInstanceAs (Nonempty (Sp (AlgebraicClosure K)))
  haveI : Nonempty (Over.mk (spMap ρ)).left := inferInstanceAs (Nonempty (Sp k))
  have push : ∀ a, GlobalTheory.ObjPull.pushEquiv hφ (Over.mk x₀) (toUnit _ ≫ c₀.lev a) = toUnit T₀ ≫ σ a := fun a => by
    apply Over.OverMorphism.ext
    rw [GlobalTheory.ObjPull.pushEquiv_left, Over.comp_left, Over.comp_left, Category.assoc, hcomp,
      GlobalTheory.ObjPull.toUnit_left', GlobalTheory.ObjPull.toUnit_left']
    exact (Category.assoc _ _ _).symm
  refine ⟨fun a => ?_, fun gg hg => ?_, fun a a' => ?_⟩
  · rw [one_iff, ← one_iff T₀, ← push, map_eq_one_iff _ (GlobalTheory.ObjPull.pushEquiv hφ _).injective]
    exact g1 a
  · obtain ⟨τ, hτn, hτ⟩ := l2 R₀ A n hA hnR hT k (spMap ρ) gg hg
    obtain ⟨a, ha⟩ := g2 ((GlobalTheory.ObjPull.pushEquiv hφ (Over.mk x₀)).symm (toUnit T₀ ≫ τ))
      (by rw [← map_pow, ← MonObj.comp_pow, hτn, MonObj.comp_one, map_one])
    refine ⟨a, ?_⟩
    have e : σ a = τ := inj T₀ _ _ (hσn a) hτn (by rw [← push, ha, MulEquiv.apply_symm_apply])
    rw [e, hτ]
  · have H' := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm (Sp R₀) (Sp K) A c₀.A (spMap κ) φ
      (P.pull (lift (𝟙 A) (𝟙 A)).left) (c₀.P.pull (lift (𝟙 c₀.A) (𝟙 c₀.A)).left) (pull_isLB hP.1.1 _)
      (pull_isLB c₀.isLB _) hφ hdiag (Over.mk x₀) (n : ℤ) _ _ (toUnit T₀ ≫ σ a) (toUnit T₀ ≫ σ a') _
      (by rw [← push]; rfl) (by rw [← push]; rfl)).1 (g3 a a')
    have ht : (Over.mk x₀).hom ≫ spMap κ = spMap (iK.comp κ) := by
      show x₀ ≫ spMap κ = _
      rw [← Spec.map_comp]; rfl
    have hu : (Units.map ((iK.comp κ).comp b).toMonoidHom ζU) ^ (2 * omegaStd a a') =
        Units.map (iK.comp κ).toMonoidHom (ζR ^ (2 * omegaStd a a')) := by
      rw [map_zpow]; rfl
    rw [hu] at H'
    simp only [T₀] at H'
    rw [ht] at H'
    have H'' := l3 R₀ A hA P hP n (by omega) hnR (σ a) (σ a') (hσn a) (hσn a') ζR hζR (2 * omegaStd a a')
      (AlgebraicClosure K) (iK.comp κ) H' k ρ
    rw [← map_zpow]
    exact H''

end GlobalTheory.LevSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfBaseChangesArtinFibreProduct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PinchHom

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {β : G'.left ⟶ G.left}

theorem sq_fst (hp : IsPullback β G'.hom G.hom f) :
    (lift (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G'))).left ≫ (fst G G).left = (fst G' G').left ≫ β := by
  rw [← Over.comp_left, lift_fst]; rfl

theorem sq_snd (hp : IsPullback β G'.hom G.hom f) :
    (lift (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G'))).left ≫ (snd G G).left = (snd G' G').left ≫ β := by
  rw [← Over.comp_left, lift_snd]; rfl

theorem sq_hom_ext (G : Over S) {X : Scheme.{0}} {a b : X ⟶ (G ⊗ G).left}
    (h₁ : a ≫ (fst G G).left = b ≫ (fst G G).left) (h₂ : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b :=
  GlobalTheory.Mum.PowCart.square_over_hom_ext G fun i => by fin_cases i; exacts [h₁, h₂]

theorem sq_mul [GrpObj G] [GrpObj G'] (hp : IsGrpPullback G' G f β) :
    (lift (pushPt hp.1.w (fst G' G')) (pushPt hp.1.w (snd G' G'))).left ≫ (MonObj.mul : G ⊗ G ⟶ G).left =
      (MonObj.mul : G' ⊗ G' ⟶ G').left ≫ β := by
  have h := hp.2 (G' ⊗ G') (fst G' G') (snd G' G') (pushPt hp.1.w (fst G' G')) (pushPt hp.1.w (snd G' G')) rfl rfl
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Over.comp_left] at h
  exact h

theorem main : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A' A : Over (Spec P)) [GrpObj A'] [GrpObj A] (A₁ : Over (Spec R₁)) (A₂ : Over (Spec R₂)) (A₀ : Over (Spec R₀)) [GrpObj A₁] [GrpObj A₂] [GrpObj A₀] (j₁ : A₁.left ⟶ A'.left) (j₂ : A₂.left ⟶ A'.left) (k₁ : A₁.left ⟶ A.left) (k₂ : A₂.left ⟶ A.left) (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₀.left ⟶ A₂.left) (φ : A'.left ⟶ A.left), Flat A'.hom → IsGrpPullback A₁ A' (Spec.map f₁) j₁ → IsGrpPullback A₂ A' (Spec.map f₂) j₂ → IsGrpPullback A₁ A (Spec.map f₁) k₁ → IsGrpPullback A₂ A (Spec.map f₂) k₂ → IsGrpPullback A₀ A₁ (Spec.map g₁) i₁ → IsGrpPullback A₀ A₂ (Spec.map g₂) i₂ → i₁ ≫ j₁ = i₂ ≫ j₂ → IsPullback φ A'.hom A.hom (𝟙 _) → j₁ ≫ φ = k₁ → j₂ ≫ φ = k₂ → IsGrpPullback A' A (𝟙 _) φ := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ A' A _ _ A₁ A₂ A₀ _ _ _ j₁ j₂ k₁ k₂ i₁ i₂ φ hfl hj₁ hj₂ hk₁ hk₂
    hi₁ hi₂ hij hφ hjk₁ hjk₂
  have hY : Flat (A' ⊗ A').hom := by
    haveI := hfl
    exact GlobalTheory.ExtUnique.flat_tensorObj A' A'
  have hw : φ ≫ A.hom = A'.hom := by simpa using hφ.w
  let Φ : A' ⟶ A := Over.homMk φ hw
  let L : A' ⊗ A' ⟶ A ⊗ A := lift (fst A' A' ≫ Φ) (snd A' A' ≫ Φ)

  have hcomp : (lift (pushPt hi₁.1.w (fst A₀ A₀)) (pushPt hi₁.1.w (snd A₀ A₀))).left ≫
      (lift (pushPt hj₁.1.w (fst A₁ A₁)) (pushPt hj₁.1.w (snd A₁ A₁))).left =
      (lift (pushPt hi₂.1.w (fst A₀ A₀)) (pushPt hi₂.1.w (snd A₀ A₀))).left ≫
      (lift (pushPt hj₂.1.w (fst A₂ A₂)) (pushPt hj₂.1.w (snd A₂ A₂))).left := by
    apply sq_hom_ext A'
    · rw [Category.assoc, sq_fst hj₁.1, reassoc_of% (sq_fst hi₁.1), Category.assoc, sq_fst hj₂.1,
        reassoc_of% (sq_fst hi₂.1), hij]
    · rw [Category.assoc, sq_snd hj₁.1, reassoc_of% (sq_snd hi₁.1), Category.assoc, sq_snd hj₂.1,
        reassoc_of% (sq_snd hi₂.1), hij]
  have po := _root_.GlobalTheory.FlatPinch.main P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ (A' ⊗ A') (A₁ ⊗ A₁) (A₂ ⊗ A₂) (A₀ ⊗ A₀) _ _ _ _
    hY (GlobalTheory.Mum.PowCart.isPullback_two hj₁.1) (GlobalTheory.Mum.PowCart.isPullback_two hj₂.1)
    (GlobalTheory.Mum.PowCart.isPullback_two hi₁.1) hcomp (GlobalTheory.Mum.PowCart.isPullback_two hi₂.1).w

  have hL : ∀ {R : CommRingCat.{0}} {g : P ⟶ R} {B : Over (Spec R)} [GrpObj B] {j k : B.left ⟶ _}
      (hj : IsGrpPullback B A' (Spec.map g) j) (hk : IsGrpPullback B A (Spec.map g) k), j ≫ φ = k →
      (lift (pushPt hj.1.w (fst B B)) (pushPt hj.1.w (snd B B))).left ≫ (MonObj.mul : A' ⊗ A' ⟶ A').left ≫ φ =
      (lift (pushPt hj.1.w (fst B B)) (pushPt hj.1.w (snd B B))).left ≫ L.left ≫ (MonObj.mul : A ⊗ A ⟶ A).left := by
    intro R g B _ j k hj hk hjk
    have e : (lift (pushPt hj.1.w (fst B B)) (pushPt hj.1.w (snd B B))).left ≫ L.left =
        (lift (pushPt hk.1.w (fst B B)) (pushPt hk.1.w (snd B B))).left := by
      apply sq_hom_ext A
      · rw [Category.assoc, ← Over.comp_left _ _ _ L, lift_fst, sq_fst hk.1, Over.comp_left, ← Category.assoc,
          sq_fst hj.1, Category.assoc, ← hjk]
        rfl
      · rw [Category.assoc, ← Over.comp_left _ _ _ L, lift_snd, sq_snd hk.1, Over.comp_left, ← Category.assoc,
          sq_snd hj.1, Category.assoc, ← hjk]
        rfl
    rw [← Category.assoc, sq_mul hj, ← Category.assoc, e, sq_mul hk, Category.assoc, hjk]
  have hE : (MonObj.mul : A' ⊗ A' ⟶ A').left ≫ φ = L.left ≫ (MonObj.mul : A ⊗ A ⟶ A).left :=
    po.hom_ext (hL hj₁ hk₁ hjk₁) (hL hj₂ hk₂ hjk₂)
  have hE' : (MonObj.mul : A' ⊗ A' ⟶ A') ≫ Φ = L ≫ MonObj.mul := Over.OverMorphism.ext hE
  have hxy : ∀ (T : Over (Spec P)) (x y : T ⟶ A'), (x * y) ≫ Φ = (x ≫ Φ) * (y ≫ Φ) := by
    intro T x y
    rw [Hom.mul_def, Hom.mul_def, Category.assoc, hE', ← Category.assoc]
    congr 1
    simp [L]
  refine ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩
  let k : Over.mk (T.hom ≫ 𝟙 (Spec P)) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = k ≫ x ≫ Φ := Over.OverMorphism.ext (by simp [k, Φ, hx])
  have ey : y₀ = k ≫ y ≫ Φ := Over.OverMorphism.ext (by simp [k, Φ, hy])
  rw [ex, ey, ← MonObj.comp_mul, ← hxy]
  simp [k, Φ]

end GlobalTheory.PinchHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauParamsSymm
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

namespace GlobalTheory.MumFam

open InhTate

end GlobalTheory.MumFam

namespace GlobalTheory.MumFam

theorem monomial_eq_of_mul_unit {W : Type} [CommRing W] [Nontrivial W] {σ : Type} {P M : σ →₀ ℕ}
    {x x' : MvPowerSeries σ W} (hx : IsUnit x) (hx' : IsUnit x')
    (he : MvPowerSeries.monomial P (1 : W) * x = MvPowerSeries.monomial M 1 * x') : P = M := by
  have h1 : ∀ (P M : σ →₀ ℕ) (x x' : MvPowerSeries σ W), IsUnit x' →
      MvPowerSeries.monomial P (1 : W) * x = MvPowerSeries.monomial M 1 * x' → P ≤ M := by
    intro P M x x' hx' he
    have hc := congrArg (MvPowerSeries.coeff M) he
    rw [MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul, if_pos le_rfl, tsub_self,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at hc
    by_contra hPM
    rw [if_neg hPM, _root_.one_mul] at hc
    exact (hx'.map (MvPowerSeries.constantCoeff (σ := σ) (R := W))).ne_zero hc.symm
  exact le_antisymm (h1 _ _ _ _ hx' he) (h1 _ _ _ _ hx he.symm)

end GlobalTheory.MumFam

namespace GlobalTheory.MumFam

end GlobalTheory.MumFam

namespace GlobalTheory.MumFam

end GlobalTheory.MumFam
end
end

