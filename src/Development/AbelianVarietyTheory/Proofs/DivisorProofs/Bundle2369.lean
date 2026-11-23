module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2262
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2304
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2155
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.H2StructureBaseChangeExtension
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

open GlobalTheory.Obs.BaseChg in
theorem GlobalTheory.Obs.extCoef_two_equiv : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0), ∃ e : ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → (GlobalTheory.CatCoh.H2 (OAff s₁) ≃+ GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))), ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (Y₀ Y₁ : Scheme.{0}) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)), f₁ ≫ pr = pr' ≫ f₀ → ∀ c c', IsExtendedPullbackDegTwo R₁ h₀ (e X₀ X₁ s₀ s₁ pr hp c) (e Y₀ Y₁ t₀ t₁ pr' hp' c') → IsPullbackH2Structure h₁ c c' := by
  intro R₀ R₁ _ _ _ q hq
  have hres : ∀ {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
      (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))),
      Function.Bijective (CoefMap.restrict (OAff s₁) (preF hp)).pull2 := fun {X₀ X₁ s₀ s₁ pr} hp ↦
    GlobalTheory.T.restrict_structureSheaf_affineBasis_pull2_bijective R₁ X₁ s₁ _ (preF hp) (preF_cover hp (GlobalTheory.T.exists_opens_preimage_eq_of_sqZero_augmentation R₀ R₁ q hq X₀ X₁ s₀ s₁ pr hp))
      (preF_dir hp (GlobalTheory.T.exists_opens_preimage_eq_of_sqZero_augmentation R₀ R₁ q hq X₀ X₁ s₀ s₁ pr hp))
  have hfwd : ∀ {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
      (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))), Function.Bijective (fwd hp).pull2 :=
    fun {X₀ X₁ s₀ s₁ pr} hp ↦ ofNat_pull2_bijective _ _ _ (fun U ↦ _root_.GlobalTheory.Obs.BaseChg.beta_bijective R₀ R₁ X₀ X₁ s₀ s₁ pr hp U.unop)
  refine ⟨fun X₀ X₁ s₀ s₁ pr hp ↦
    (AddEquiv.ofBijective (CoefMap.restrict (OAff s₁) (preF hp)).pull2.toAddMonoidHom (hres hp)).trans
      (AddEquiv.ofBijective (fwd hp).pull2.toAddMonoidHom (hfwd hp)).symm, ?_⟩
  intro X₀ X₁ s₀ s₁ pr hp Y₀ Y₁ t₀ t₁ pr' hp' f₀ f₁ h₀ h₁ hf c c' hE
  set d := ((AddEquiv.ofBijective (CoefMap.restrict (OAff s₁) (preF hp)).pull2.toAddMonoidHom (hres hp)).trans
      (AddEquiv.ofBijective (fwd hp).pull2.toAddMonoidHom (hfwd hp)).symm) c with hd0
  set d' := ((AddEquiv.ofBijective (CoefMap.restrict (OAff t₁) (preF hp')).pull2.toAddMonoidHom (hres hp')).trans
      (AddEquiv.ofBijective (fwd hp').pull2.toAddMonoidHom (hfwd hp')).symm) c' with hd0'
  have hd : (fwd hp).pull2 d = (CoefMap.restrict (OAff s₁) (preF hp)).pull2 c :=
    (AddEquiv.ofBijective (fwd hp).pull2.toAddMonoidHom (hfwd hp)).apply_symm_apply _
  have hd' : (fwd hp').pull2 d' = (CoefMap.restrict (OAff t₁) (preF hp')).pull2 c' :=
    (AddEquiv.ofBijective (fwd hp').pull2.toAddMonoidHom (hfwd hp')).apply_symm_apply _
  clear_value d d'
  have A : (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)).pull2 ((pairPull h₁).pull2 c) =
      (kMap hp hp' hf).pull2 ((extMap R₁ (pairPull h₀)).pull2 d) := by
    rw [← CoefMap.pullCohomologyTwo_comp, ← CoefMap.pullCohomologyTwo_comp]
    rw [CoefMap.pullCohomologyTwo_eq_of_natTrans ((pairPull h₁).comp (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)))
      ((CoefMap.restrict (OAff s₁) (preF hp)).comp (zMap hp hp' hf h₁)) { app := fun p ↦ 𝟙 _ }
      (fun p b ↦ by erw [mp_id]; rfl) c]
    rw [CoefMap.pullCohomologyTwo_comp, ← hd, ← CoefMap.pullCohomologyTwo_comp]
    refine CoefMap.pullCohomologyTwo_eq_of_natTrans ((fwd hp).comp (zMap hp hp' hf h₁))
      ((extMap R₁ (pairPull h₀)).comp (kMap hp hp' hf)) { app := fun p ↦ 𝟙 _ } (fun p b ↦ ?_) d
    erw [mp_id]
    change beta hp' p.unop.1.1 (extHom R₁ (coefHom (pairPull h₀) p) b) =
      GlobalTheory.CechDR.secPull s₁ t₁ (preP hp hp' hf p.unop) (beta hp p.unop.1.2 b)
    revert b
    change ∀ b : R₁ ⊗[R₀] Sec s₀ p.unop.1.2.1, _
    intro b
    induction b using TensorProduct.induction_on with
    | zero =>
      exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans ((congrArg _ (map_zero _)).trans (map_zero _)).symm
    | tmul r a =>
      change beta hp' p.unop.1.1 (r ⊗ₜ[R₀] (coefHom (pairPull h₀) p a)) = _
      rw [beta_tmul hp p.unop.1.2 r a]
      erw [beta_tmul hp' p.unop.1.1 r]
      rw [map_mul]
      have hr : GlobalTheory.CechDR.secPull s₁ t₁ (preP hp hp' hf p.unop) (algebraMap R₁ _ r) = algebraMap R₁ _ r := by
        have := semiHom_secPull h₁ (preP hp hp' hf p.unop) r 1
        rw [map_one, RingHom.id_apply, ← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one] at this
        exact this
      have e1 := congrArg (fun φ ↦ φ.hom a) (Scheme.Hom.appLE_comp_appLE pr' f₀ p.unop.1.2.1 p.unop.1.1.1
        (pr' ⁻¹ᵁ p.unop.1.1.1) p.unop.2 le_rfl)
      have e2 := congrArg (fun φ ↦ φ.hom a) (Scheme.Hom.appLE_comp_appLE f₁ pr p.unop.1.2.1
        (pr ⁻¹ᵁ p.unop.1.2.1) (pr' ⁻¹ᵁ p.unop.1.1.1) le_rfl (preP hp hp' hf p.unop).2)
      have key : ∀ (g g' : Y₁ ⟶ X₀) (_ : g = g') (e e'),
          (g.appLE p.unop.1.2.1 (pr' ⁻¹ᵁ p.unop.1.1.1) e).hom a = (g'.appLE p.unop.1.2.1 (pr' ⁻¹ᵁ p.unop.1.1.1) e').hom a := by
        rintro g _ rfl _ _; rfl
      rw [hr]
      congr 1
      exact e1.trans ((key _ _ hf.symm _ _).trans e2.symm)
    | add x y hx hy =>
      exact ((congrArg _ (map_add _ x y)).trans ((map_add _ _ _).trans (congrArg₂ (· + ·) hx hy))).trans
        ((congrArg _ (map_add _ x y)).trans (map_add _ _ _)).symm
  have B : (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)).pull2 ((pairRes f₁ t₁).pull2 c') =
      (kMap hp hp' hf).pull2 ((extMap R₁ (pairRes f₀ t₀)).pull2 d') := by
    rw [← CoefMap.pullCohomologyTwo_comp, ← CoefMap.pullCohomologyTwo_comp]
    rw [CoefMap.pullCohomologyTwo_eq_of_natTrans ((pairRes f₁ t₁).comp (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)))
      ((CoefMap.restrict (OAff t₁) (preF hp')).comp (zRes hp hp' hf)) { app := fun p ↦ 𝟙 _ }
      (fun p b ↦ by erw [mp_id]; rfl) c']
    rw [CoefMap.pullCohomologyTwo_comp, ← hd', ← CoefMap.pullCohomologyTwo_comp]
    refine CoefMap.pullCohomologyTwo_eq_of_natTrans ((fwd hp').comp (zRes hp hp' hf))
      ((extMap R₁ (pairRes f₀ t₀)).comp (kMap hp hp' hf)) { app := fun p ↦ 𝟙 _ } (fun p b ↦ ?_) d'
    erw [mp_id]
    change beta hp' p.unop.1.1 (extHom R₁ (coefHom (pairRes f₀ t₀) p) b) = beta hp' p.unop.1.1 b
    congr 1
    revert b
    change ∀ b : R₁ ⊗[R₀] Sec t₀ p.unop.1.1.1, _
    intro b
    induction b using TensorProduct.induction_on with
    | zero => exact map_zero _
    | tmul r a => rfl
    | add x y hx hy => exact (map_add _ x y).trans (congrArg₂ (· + ·) hx hy)
  have hinj : Function.Injective (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)).pull2 := by
    intro x y hxy
    obtain ⟨x0, rfl⟩ := (GlobalTheory.AbCoh.pairRes_pull2_bijective f₁ t₁).2 x
    obtain ⟨y0, rfl⟩ := (GlobalTheory.AbCoh.pairRes_pull2_bijective f₁ t₁).2 y
    have key : ∀ z, (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)).pull2 ((pairRes f₁ t₁).pull2 z) =
        (CoefMap.restrict (OAff t₁) (preFP hp hp' hf ⋙ pairFst f₁)).pull2 z := fun z ↦ by
      rw [← CoefMap.pullCohomologyTwo_comp]
      exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app := fun p ↦ 𝟙 _ } (fun p b ↦ mp_id _ _ b) z
    rw [key, key] at hxy
    have hW' := GlobalTheory.T.exists_opens_preimage_eq_of_sqZero_augmentation R₀ R₁ q hq Y₀ Y₁ t₀ t₁ pr' hp'
    rw [(GlobalTheory.T.restrict_structureSheaf_affineBasis_pull2_bijective R₁ Y₁ t₁ _ (preFP hp hp' hf ⋙ pairFst f₁) (preFP_cover hp hp' hf hW')
      (preFP_directed hp hp' hf hW')).1 hxy]
  apply hinj
  rw [A, B]
  exact congrArg _ hE
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieMultiplicitySquareZeroLift
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTLiftLie

theorem exists_factor_of_sq_zero {C C₀ k : Type} [CommRing C] [CommRing C₀] [Field k] (π : C →+* C₀)
    (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0) (x : Sp k ⟶ Sp C) :
    ∃ ψ : C₀ →+* k, x = spMap ψ ≫ spMap π := by
  let φ : C →+* k := (Spec.preimage x).hom
  have hx : x = spMap φ := by
    show x = Spec.map (CommRingCat.ofHom (Spec.preimage x).hom)
    simp
  have hker : RingHom.ker π ≤ RingHom.ker φ := by
    intro a ha
    have h2 : a * a ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul ha ha
    rw [hsq] at h2
    have h0 : a * a = 0 := by simpa using h2
    have : φ a * φ a = 0 := by rw [← map_mul, h0, map_zero]
    exact RingHom.mem_ker.2 (mul_self_eq_zero.1 this)
  have hc : (RingHom.liftOfSurjective π hπ ⟨φ, hker⟩).comp π = φ :=
    RingHom.liftOfRightInverse_comp _ _ _ _
  generalize RingHom.liftOfSurjective π hπ ⟨φ, hker⟩ = ψ at hc
  refine ⟨ψ, ?_⟩
  rw [hx, ← hc]
  show Spec.map (CommRingCat.ofHom (ψ.comp π)) = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom π)
  rw [← Spec.map_comp]
  rfl

theorem lieMult_of_sqZeroLift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i) (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp C) (β : R →+* k), x ≫ spMap tR = spMap β → ∀ j, LieMult (act.toF D) x (β.comp (b.t j)) D.m := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ A _ _ i h act hact k _ _ x β hx j
  obtain ⟨ψ, rfl⟩ := exists_factor_of_sq_zero π hπ hsq x
  have hact' : ∀ c, ((o₀.act.toF D).act c).left ≫ i = i ≫ ((act.toF D).act c).left :=
    fun c => hact _
  refine (GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) (Sp C) (Sp C₀) A o₀.A (spMap π) i (act.toF D) (o₀.act.toF D)
    h hact' k (spMap ψ) (β.comp (b.t j)) D.m).1 ?_
  exact o₀.lieRank k (spMap ψ) β (by rw [← hx, Category.assoc]) j

end GlobalTheory.HTLiftLie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieSpreadFromIdentityPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTLieSpread

theorem prod_ofFn_eq {G : Type} [Monoid G] {V : Type} [AddCommMonoid V] (T : V → G)
    (h0 : T 0 = 1) (hadd : ∀ c c', T (c + c') = T c * T c') :
    ∀ {a : ℕ} (w : Fin a → V), (List.ofFn (fun i => T (w i))).prod = T (∑ i, w i)
  | 0, w => by simp [h0]
  | a + 1, w => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ, hadd, prod_ofFn_eq T h0 hadd (fun i => w i.succ)]

theorem mat_ext {n : ℕ} {C : Type} [CommRing C] {A B : Matrix (Fin n) (Fin n) C}
    (h : ∀ v, A.mulVec v = B.mulVec v) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v)

theorem isUnit_two_rho_sub {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) : IsUnit (2 * b.ρ - (D.tr : R)) := by
  have hsq : (2 * b.ρ - (D.tr : R)) ^ 2 = ((D.tr ^ 2 - 4 * D.nm : ℤ) : R) := by
    have := b.ρ_root; push_cast; linear_combination 4 * this
  have hd : D.tr ^ 2 - 4 * D.nm = -(((D.tr ^ 2 - 4 * D.nm).natAbs : ℕ) : ℤ) := by
    have := D.disc_neg; omega
  have hcop : ((D.tr ^ 2 - 4 * D.nm).natAbs).Coprime p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out)]
    intro h; exact D.disc_p (Int.natCast_dvd.mpr h)
  have hu := b.unit _ hcop
  rw [← isUnit_pow_iff (n := 2) two_ne_zero, hsq, hd]
  rw [Int.cast_neg, Int.cast_natCast]
  exact hu.neg

def TangentCoordinatesSmoothCommGroupLocalRing : Prop :=
  ∀ (W : Type) [CommRing W] [IsLocalRing W] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∃ (n : ℕ) (M : (G ⟶ G) → Matrix (Fin n) (Fin n) W), ∀ (R' : Type) [CommRing R'] (β : W →+* R'),
      ∃ T : (Fin n → R') → (GlobalTheory.UPel.HT.epsPtR (spMap β) ⟶ G), Function.Injective T ∧
        (∀ v : GlobalTheory.UPel.HT.epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left =
          (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) ∧
        (∀ c c', T (c + c') = T c * T c') ∧
        (∀ (s : R') c, (T (s • c)).left = spMap (epsScaleR s) ≫ (T c).left) ∧
        ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map β).mulVec c)

theorem spread_of_coord (hcoord : TangentCoordinatesSmoothCommGroupLocalRing) : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] (tR : R →+* C) (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A], Smooth A.hom → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), GlobalTheory.UPel.HT.LieAt b act tR (spMap (RingHom.id C)) → ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp C), x ≫ spMap tR = spMap β → GlobalTheory.UPel.HT.LieAt b act β x := by
  intro p _ D R _ b C _ _ tR A _ _ hsm act hlie R' _ β x hx
  obtain ⟨g0, rfl⟩ : ∃ g0 : C →+* R', spMap g0 = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  have hg : g0.comp tR = β := by
    have h1 : Spec.map (CommRingCat.ofHom (g0.comp tR)) = Spec.map (CommRingCat.ofHom β) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp]; exact hx
    have h2 := Spec.map_injective h1
    simpa using congrArg CommRingCat.Hom.hom h2
  have hgapp : ∀ r, g0 (tR r) = β r := fun r => by rw [← hg]; rfl
  obtain ⟨n, M, hM⟩ := hcoord C A hsm
  obtain ⟨T1, T1inj, T1rng, T1add, T1sm, T1u⟩ := hM C (RingHom.id C)
  obtain ⟨T0, T0inj, T0rng, T0add, T0sm, T0u⟩ := hM R' g0
  have T1zero : T1 0 = 1 := by
    have h := T1add 0 0; rw [add_zero] at h; exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  have T0zero : T0 0 = 1 := by
    have h := T0add 0 0; rw [add_zero] at h; exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  have hid : ∀ u : A ⟶ A, (M u).map (RingHom.id C) = M u := fun u => by ext; simp
  let fa : 𝓞 D.F → Matrix (Fin n) (Fin n) C := fun c => M (act.act (algebraMap (𝓞 D.F) D.O c))
  have key : ∀ (c : 𝓞 D.F) v, T1 v ≫ act.act (algebraMap (𝓞 D.F) D.O c) = T1 ((fa c).mulVec v) := fun c v => by
    rw [T1u _ (act.hom _) v, hid]
  have f1 : fa 1 = 1 := mat_ext fun v => T1inj (by
    rw [← key, map_one, act.one, Category.comp_id, Matrix.one_mulVec])
  have fmul : ∀ c d, fa (c * d) = fa c * fa d := fun c d => mat_ext fun v => T1inj (by
    rw [← key, map_mul, act.mul, ← Category.assoc, key, key, Matrix.mulVec_mulVec])
  have fadd : ∀ c d, fa (c + d) = fa c + fa d := fun c d => mat_ext fun v => T1inj (by
    rw [← key, map_add (f := _), act.add, MonObj.comp_mul, key, key, ← T1add, Matrix.add_mulVec])
  have f0 : fa 0 = 0 := by
    have h := fadd 0 0; rw [add_zero] at h; exact add_left_cancel (h.symm.trans (add_zero _).symm)
  let f : 𝓞 D.F →+* Matrix (Fin n) (Fin n) C :=
    { toFun := fa, map_one' := f1, map_mul' := fmul, map_zero' := f0, map_add' := fadd }
  have keyf : ∀ (c : 𝓞 D.F) v, T1 v ≫ act.act (algebraMap (𝓞 D.F) D.O c) = T1 ((f c).mulVec v) := key
  have keyg : ∀ (c : 𝓞 D.F) u, T0 u ≫ act.act (algebraMap (𝓞 D.F) D.O c) = T0 (((f c).map g0).mulVec u) :=
    fun c u => T0u _ (act.hom _) u
  have hω : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hρ : (tR b.ρ) ^ 2 - (D.tr : C) * tR b.ρ + (D.nm : C) = 0 := by
    have := congrArg tR b.ρ_root; simpa using this
  have hunit : IsUnit (2 * tR b.ρ - (D.tr : C)) := by
    simpa [map_ofNat] using (isUnit_two_rho_sub b).map tR
  let t : Fin D.a → (𝓞 D.F →+* C) := fun i => tR.comp (b.t i)
  have ht : ∀ i, t i D.ω = tR b.ρ := fun i => by simp [t, b.t_ω]
  have hyp : ∀ v : Fin n → C, (f D.ω).mulVec v = tR b.ρ • v → ∃ w : Fin D.a → Fin n → C,
      (∀ i (c : 𝓞 D.F), (f c).mulVec (w i) = t i c • w i) ∧ v = ∑ i, w i := by
    intro v hv
    obtain ⟨w, hw, hvw⟩ := hlie (T1 v) ⟨(T1rng _).2 ⟨v, rfl⟩, by rw [keyf, hv]; exact T1sm _ _⟩
    choose w' hw' using fun i => (T1rng (w i)).1 (hw i 0).1
    refine ⟨w', fun i c => T1inj ?_, T1inj ?_⟩
    · rw [← keyf, hw' i]
      apply Over.OverMorphism.ext
      rw [T1sm, hw' i]
      exact (hw i c).2
    · rw [hvw, ← prod_ofFn_eq T1 T1zero T1add]
      simp only [hw']
  have L := GlobalTheory.eigen_decomp_base_change (𝓞 D.F) C n D.a D.ω D.tr D.nm hω f (tR b.ρ) hρ hunit t ht hyp R' g0
  intro v hv
  obtain ⟨v', rfl⟩ := (T0rng v).1 hv.1
  obtain ⟨w, hw, hvw⟩ := L v' (T0inj (by
    apply Over.OverMorphism.ext
    rw [← keyg, T0sm, hgapp]
    exact hv.2))
  refine ⟨fun i => T0 (w i), fun i c => ⟨(T0rng _).2 ⟨_, rfl⟩, ?_⟩, ?_⟩
  · rw [keyg, hw i c, T0sm]
    rw [show g0 (t i c) = β (b.t i c) from hgapp _]
  · rw [hvw, prod_ofFn_eq T0 T0zero T0add]

theorem lieAt_spread : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] (tR : R →+* C) (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A], Smooth A.hom → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), GlobalTheory.UPel.HT.LieAt b act tR (spMap (RingHom.id C)) → ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp C), x ≫ spMap tR = spMap β → GlobalTheory.UPel.HT.LieAt b act β x :=
  spread_of_coord GlobalTheory.T.exists_tangent_coords_base_change_smooth_comm_group

end GlobalTheory.HTLieSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPrimeToPLevelLiftSquareZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped CategoryTheory.Obj

namespace GlobalTheory.HTLevelLift

theorem existsUnique_torsion_lift_thick (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀)
    (hπ : Function.Surjective π) (hnil : IsNilpotent (RingHom.ker π)) (n : ℕ) (hn : IsUnit (n : C))
    (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀] (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A]
    (i : A₀.left ⟶ A.left) (hA : IsAbelianScheme A) (hpb : IsGrpPullback A₀ A (spMap π) i)
    (s₀ : 𝟙_ (Over (Sp C₀)) ⟶ A₀) (hs₀ : s₀ ^ n = 1) :
    ∃! s : 𝟙_ (Over (Sp C)) ⟶ A, s ^ n = 1 ∧ s₀.left ≫ i = spMap π ≫ s.left := by
  haveI : Smooth A.hom := hA.smooth
  have hn' : IsUnit (n : Γ(Sp C, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
  haveI := GlobalTheory.GrpTangent.etale_id_pow A hn'
  let T' : Over (Sp C₀) := 𝟙_ (Over (Sp C₀))
  let T : Over (Sp C) := Over.mk (T'.hom ≫ spMap π)
  have hwi : i ≫ A.hom = A₀.hom ≫ spMap π := hpb.1.w
  have hpt : ∀ x : T' ⟶ A₀, (x.left ≫ i) ≫ A.hom = T.hom := by
    intro x
    rw [Category.assoc, hwi, ← Category.assoc, Over.w x]
    rfl
  let pt : (T' ⟶ A₀) → (T ⟶ A) := fun x => Over.homMk (x.left ≫ i) (hpt x)
  have hone : pt 1 = 1 := by
    have h := hpb.2 T' 1 1 (pt 1) (pt 1) rfl rfl
    rw [_root_.mul_one] at h
    have h2 : pt 1 * pt 1 = pt 1 := Over.OverMorphism.ext h
    exact mul_eq_left.mp h2
  have hpow : ∀ m : ℕ, (pt s₀) ^ m = pt (s₀ ^ m) := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ m ih =>
      rw [pow_succ, pow_succ]
      exact Over.OverMorphism.ext (hpb.2 T' (s₀ ^ m) s₀ ((pt s₀) ^ m) (pt s₀) (by rw [ih]; rfl) rfl)
  have hx : (pt s₀) ^ n = 1 := by rw [hpow, hs₀, hone]
  let f : A.left ⟶ A.left := (𝟙 A ^ n).left
  have hf : ∀ {Y : Over (Sp C)} (y : Y ⟶ A), y.left ≫ f = (y ^ n).left := by
    intro Y y
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have hone' : ∀ {Y : Over (Sp C)}, ((1 : Y ⟶ A)).left = Y.hom ≫ (η[A] : 𝟙_ (Over (Sp C)) ⟶ A).left := by
    intro Y
    rw [Hom.one_def, Over.comp_left]
    congr 1
  have hw : (s₀.left ≫ i) ≫ f = Spec.map (CommRingCat.ofHom π) ≫ (η[A] : 𝟙_ (Over (Sp C)) ⟶ A).left := by
    have := hf (pt s₀)
    rw [hx, hone'] at this
    simpa [pt, T, T'] using this
  obtain ⟨l, ⟨hl1, hl2⟩, huniq⟩ :=
    GlobalTheory.existsUnique_lift_of_etale_of_surjective f (CommRingCat.ofHom π) hπ hnil (s₀.left ≫ i) _ hw
  have hls : l ≫ A.hom = (𝟙_ (Over (Sp C))).hom := by
    have e : f ≫ A.hom = A.hom := Over.w (𝟙 A ^ n)
    rw [← e, ← Category.assoc, hl2]
    exact Over.w (η[A] : 𝟙_ (Over (Sp C)) ⟶ A)
  let s : 𝟙_ (Over (Sp C)) ⟶ A := Over.homMk l hls
  have hsn : ∀ s' : 𝟙_ (Over (Sp C)) ⟶ A, s' ^ n = 1 ↔ s'.left ≫ f = (η[A] : 𝟙_ (Over (Sp C)) ⟶ A).left := by
    intro s'
    have e1 : ((1 : 𝟙_ (Over (Sp C)) ⟶ A)).left = (η[A] : 𝟙_ (Over (Sp C)) ⟶ A).left := by
      rw [hone']; exact Category.id_comp _
    rw [hf]
    constructor
    · intro h; rw [h, e1]
    · intro h
      apply Over.OverMorphism.ext
      rw [h, e1]
  refine ⟨s, ⟨(hsn s).2 hl2, hl1.symm⟩, ?_⟩
  rintro s' ⟨h1, h2⟩
  exact Over.OverMorphism.ext (huniq s'.left ⟨h2.symm, (hsn s').1 h1⟩)

theorem map_nsmul_pow {La Q : Type} [AddCommGroup La] [Group Q] (f : La → Q) (hf : ∀ x y, f (x + y) = f x * f y)
    (n : ℕ) (x : La) : f (n • x) = f x ^ n := by
  induction n with
  | zero =>
    have h := hf 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact mul_eq_left.mp h.symm
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

theorem level_lift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i), IsAbelianScheme A → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → N.Coprime p → ∀ (P : LB (G2 A).left) (φ₂ : (G2 o₀.A).left ⟶ (G2 A).left), P.IsLB → IsSquare i φ₂ → LBIso o₀.P (P.pull φ₂) → ∃ eta : D.La → (𝟙_ (Over (Sp C)) ⟶ A), (∀ x y, eta (x + y) = eta x * eta y) ∧ (∀ (c : D.O) x, eta (c • x) = eta x ≫ act.act c) ∧ (∀ x, eta (N • x) = 1) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp C) (β : R →+* k), x ≫ spMap tR = spMap β → ∃ I : GlobalTheory.UPel.HT.TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta y = I.ev N y) ∧ ∀ y, (o₀.eta y).left ≫ i = spMap π ≫ (eta y).left := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ A _ _ i h hA act hact hN P φ₂ hP hsqr hLB
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, hsq⟩
  have hNu : IsUnit (N : C) := by simpa using (b.unit N hN).map tR
  have hlift := fun y => existsUnique_torsion_lift_thick C C₀ π hπ hnil N hNu o₀.A A i hA h (o₀.eta y)
      (by rw [← map_nsmul_pow o₀.eta o₀.eta_add, o₀.eta_ker])
  choose eta hspec huniq using hlift
  let TT : Over (Sp C) := Over.mk ((𝟙_ (Over (Sp C₀))).hom ≫ spMap π)
  let u : TT ⟶ 𝟙_ (Over (Sp C)) := toUnit TT
  have hu : u.left = spMap π := by simpa [TT] using Over.w u
  have hcomp : ∀ s : 𝟙_ (Over (Sp C)) ⟶ A, (u ≫ s).left = spMap π ≫ s.left := fun s => by
    rw [Over.comp_left, hu]
  have hadd : ∀ x y, eta (x + y) = eta x * eta y := by
    intro x y
    refine (huniq (x + y) _ ⟨by rw [mul_pow, (hspec x).1, (hspec y).1, _root_.one_mul], ?_⟩).symm
    have e := h.2 (𝟙_ (Over (Sp C₀))) (o₀.eta x) (o₀.eta y) (u ≫ eta x) (u ≫ eta y)
      (by rw [hcomp, (hspec x).2]) (by rw [hcomp, (hspec y).2])
    rw [o₀.eta_add, ← e, ← MonObj.comp_mul, hcomp]
  refine ⟨eta, hadd, ?_, ?_, ?_, fun y => (hspec y).2⟩
  · intro c x
    haveI := act.hom c
    haveI := o₀.act.hom c
    refine (huniq (c • x) _ ⟨by rw [← MonObj.pow_comp, (hspec x).1, MonObj.one_comp], ?_⟩).symm
    rw [o₀.eta_lin, Over.comp_left, Category.assoc, hact, ← Category.assoc, (hspec x).2, Over.comp_left,
      Category.assoc]
  · intro x
    rw [map_nsmul_pow eta hadd, (hspec x).1]
  · intro k _ _ x β hxβ
    obtain ⟨φ, hφx⟩ := Spec.map_surjective x
    have hker : RingHom.ker π ≤ RingHom.ker φ.hom := by
      intro a ha
      have h2 : a * a ∈ RingHom.ker π ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha ha
      rw [hsq] at h2
      have h3 : φ.hom (a * a) = 0 := by
        rw [show a * a = 0 from h2, map_zero]
      rw [RingHom.mem_ker]
      rw [map_mul] at h3
      exact mul_self_eq_zero.mp h3
    let φ₀ : C₀ →+* k := π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ) ⟨φ.hom, hker⟩
    have hφ : φ₀.comp π = φ.hom := RingHom.liftOfRightInverse_comp _ _ _ _
    have hx : x = spMap φ₀ ≫ spMap π := by
      rw [← hφx]
      show Spec.map φ = Spec.map (CommRingCat.ofHom φ₀) ≫ Spec.map (CommRingCat.ofHom π)
      rw [← Spec.map_comp]
      congr 1
      ext a
      simp [← hφ]
    subst hx
    obtain ⟨I₀, hI₀⟩ := o₀.geom k (spMap φ₀) β (by rw [← Category.assoc]; exact hxβ)
    obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk (spMap φ₀)) (spMap φ₀ ≫ spMap π) rfl
    have hd : (lift (𝟙 o₀.A) (𝟙 o₀.A)).left ≫ φ₂ = i ≫ (lift (𝟙 A) (𝟙 A)).left :=
      GlobalTheory.AxisTrivExt.lift_match hsqr.1 hsqr.2 (𝟙 o₀.A) (𝟙 o₀.A) (𝟙 A) (𝟙 A) (by simp) (by simp)
    have a3 : LBIso (o₀.P.pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left)
        ((P.pull φ₂).pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left) :=
      GenSpread.lbIso_pullback hLB _
    have b1 : LBIso (P.pull (i ≫ (lift (𝟙 A) (𝟙 A)).left)) ((P.pull φ₂).pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left) :=
      GenSpread.lbIso_pull_pull hP _ hd.symm
    have b2 : LBIso (P.pull (i ≫ (lift (𝟙 A) (𝟙 A)).left)) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull i) :=
      GenSpread.lbIso_pull_pull hP i rfl
    have iD : LBIso (o₀.P.pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull i) :=
      LBIso.trans (pull_isLB o₀.isLB _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _)
        (LBIso.trans (pull_isLB o₀.isLB _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) a3 b1.symm) b2
    have lin : ∀ (c : D.O) (g : Over.mk (spMap φ₀) ⟶ o₀.A), e (g ≫ o₀.act.act c) = e g ≫ act.act c := fun c g =>
      Over.OverMorphism.ext (by rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
    refine ⟨{ ζ := I₀.ζ
              ζ_prim := I₀.ζ_prim
              ζ_pow := I₀.ζ_pow
              ev := fun n y => e (I₀.ev n y)
              add := fun n y y' => by simp only [I₀.add, map_mul]
              lin := fun n c y => by simp only [I₀.lin, lin]
              ker := fun n hn hp y => by
                rw [← I₀.ker n hn hp y]
                exact ⟨fun E => e.injective (E.trans (map_one e).symm), fun E => by rw [E, map_one]⟩
              onto := fun n hn hp q => by
                obtain ⟨q, rfl⟩ := e.surjective q
                rw [← map_pow]
                refine Iff.trans ?_ ((I₀.onto n hn hp q).trans ?_)
                · exact ⟨fun E => e.injective (E.trans (map_one e).symm), fun E => by rw [E, map_one]⟩
                · exact ⟨fun ⟨y, hy⟩ => ⟨y, by rw [hy]⟩, fun ⟨y, hy⟩ => ⟨y, e.injective hy⟩⟩
              tower := fun n m hn hm hp y => by rw [← map_pow, I₀.tower n m hn hm hp y]
              isom := fun n hn hp y y' =>
                (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ A o₀.A (spMap π) i _ _ (pull_isLB hP _)
                  (pull_isLB o₀.isLB _) h iD (Over.mk (spMap φ₀)) n _ _ (e (I₀.ev n y)) (e (I₀.ev n y')) _
                  (he _) (he _)).1 (I₀.isom n hn hp y y') }, fun y => ?_⟩
    show toUnit _ ≫ eta y = e (I₀.ev N y)
    rw [← hI₀ y]
    have e₁ : (toUnit (Over.mk (spMap φ₀))).left = spMap φ₀ := by simpa using Over.w (toUnit (Over.mk (spMap φ₀)))
    have e₂ : (toUnit (Over.mk (spMap φ₀ ≫ spMap π))).left = spMap φ₀ ≫ spMap π := by
      simpa using Over.w (toUnit (Over.mk (spMap φ₀ ≫ spMap π)))
    apply Over.OverMorphism.ext
    rw [he, Over.comp_left, Over.comp_left, Category.assoc, (hspec y).2, e₁, e₂, Category.assoc]

end GlobalTheory.HTLevelLift
end

