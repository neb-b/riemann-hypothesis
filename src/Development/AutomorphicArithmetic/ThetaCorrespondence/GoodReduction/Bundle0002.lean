module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2706
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1454
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1528
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.TwistedSectionsExtend
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1420
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.CMGood
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Lit

theorem cmPotentialGoodReduction_of_nos (hN : GlobalTheory.Published.NeronOggShafarevichSt) :
    GlobalTheory.Published.CMPotentialGoodReductionSt := by
  intro R K _ _ _ _ _ _ _ A _ hA F _ _ hF
  have : IsCommMonObj A := hA.comm
  obtain ⟨V, hV⟩ := exists_isAbove R K (SeparableClosure K)
  obtain ⟨l, hl, hlk⟩ := GlobalTheory.Proof.exists_prime_natCast_ne_zero (ResidueField R)
  have hlK : (l : K) ≠ 0 := by
    intro h
    apply hlk
    have h1 : (l : R) = 0 := IsFractionRing.injective R K (by rw [map_natCast, map_zero, h])
    rw [← map_natCast (residue R), h1, map_zero]
  have hc := _root_.GlobalTheory.CMComm.galTate_commute_of_hasCMBy K (SeparableClosure K) A hA F hF l hlK
  have he := _root_.GlobalTheory.InertiaTate.exists_exponent_inertia_galTate R K (SeparableClosure K) V hV A hA l hlk hc
  obtain ⟨⟨d, hd, -⟩, -⟩ := hF
  have hcard := _root_.GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K (SeparableClosure K) A hA d hd (l ^ 2)
    (by rw [Nat.cast_pow]; exact pow_ne_zero _ hlK)
  have hfin : Finite {x : ptOver K (SeparableClosure K) ⟶ A // x ^ (l ^ 2) = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (pow_ne_zero _ hl.out.ne_zero))
  exact (GlobalTheory.potentialGoodReduction_of_neronOggShafarevich hN R K (SeparableClosure K) V hV A hA l hlk).2
    (_root_.GlobalTheory.Proof.FiniteInertiaImage.finite_image_galTate K (SeparableClosure K) A l _ hfin hc he)

end UpperTheory.Lit
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.ExistsVeryAmpleFamiliesStableMatrix
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace UpperTheory.Lit.Nos.C2
open GlobalTheory

theorem appTop_cst' {X Y : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (β : Y ⟶ X)
    (f : X ⟶ Sp R) (f' : Y ⟶ Sp R') (c : R →+* R') (h : β ≫ f = f' ≫ spMap c) (r : R) :
    β.appTop (GlobalTheory.AbLaw.cst f ⊤ r) = GlobalTheory.AbLaw.cst f' ⊤ (c r) := by
  simp only [GlobalTheory.AbLaw.cst, RingHom.comp_apply, GlobalTheory.AbLaw.rs_self]
  have h1 := congrArg (fun φ : Y ⟶ Sp R => φ.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) h
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h1
  rw [h1]
  congr 1
  have h2 := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom c))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  exact h2.symm

theorem secPull_add' {X Y : Scheme.{0}} {L : LB X} (s t : L.Sec) (φ : Y ⟶ X) :
    Cartier.secPull (s + t) φ = Cartier.secPull s φ + Cartier.secPull t φ :=
  GlobalTheory.LB.f_injective (funext fun i => by simp only [Cartier.secPull, GlobalTheory.LB.add_f, map_add (f := _)])

theorem secPull_smul' {X Y : Scheme.{0}} {L : LB X} (c : Γ(X, ⊤)) (s : L.Sec) (φ : Y ⟶ X) :
    Cartier.secPull (c • s) φ = φ.appTop c • Cartier.secPull s φ :=
  GlobalTheory.LB.f_injective (funext fun i => by
    simp only [Cartier.secPull, GlobalTheory.LB.smul_f, map_mul, Cartier.app_resG, Cartier.resG_resG]
    rfl)

theorem secPull_sum_smul' {X Y : Scheme.{0}} {L : LB X} {J : Type} (S : Finset J) (c : J → Γ(X, ⊤))
    (s : J → L.Sec) (φ : Y ⟶ X) :
    Cartier.secPull (∑ i ∈ S, c i • s i) φ = ∑ i ∈ S, φ.appTop (c i) • Cartier.secPull (s i) φ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact GlobalTheory.LB.f_injective (funext fun i => by simp [Cartier.secPull, GlobalTheory.LB.zero_f])
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, secPull_add', secPull_smul', ih]

theorem secMaps_sum_smul' {X : Scheme.{0}} {A B : LB X} (w : LB.Iso A B) {J : Type} (S : Finset J)
    (c : J → Γ(X, ⊤)) (a : J → A.Sec) (b : J → B.Sec) (h : ∀ i, Cartier.SecMaps w (a i) (b i)) :
    Cartier.SecMaps w (∑ i ∈ S, c i • a i) (∑ i ∈ S, c i • b i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro p
    simp [GlobalTheory.LB.zero_f]
  | insert x S hx ih =>
    intro p
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    simp only [GlobalTheory.LB.add_f, GlobalTheory.LB.smul_f, map_add (f := _), map_mul, ih p, h x p, Cartier.resG_resG]
    ring

theorem exists_veryAmple_families_stable_matrix : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → ∀ D : Set (K' ≃ₐ[K] K'), (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y) → (∀ x : W, (∀ σ ∈ D, ∀ y : W, σ (algebraMap W K' x) = algebraMap W K' y → y - x ∈ maximalIdeal W) → ∃ r : R, x - algebraMap R W r ∈ maximalIdeal W) → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, IsMonHom e.hom → (∀ σ ∈ D, ∃ (τ : W →+* W) (φ : G.left ⟶ G.left), (∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x)) ∧ φ ≫ G.hom = G.hom ≫ spMap τ ∧ pullback.fst G.hom (spMap (algebraMap W K')) ≫ φ = (e.hom.left ≫ pullback.map A.hom (spMap (algebraMap K K')) A.hom (spMap (algebraMap K K')) (𝟙 _) (spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext x; exact (σ.commutes x).symm) ≫ e.inv.left) ≫ pullback.fst G.hom (spMap (algebraMap W K'))) → ∃ (N : ℕ) (H : LB A.left) (s : Fin (N + 1) → H.Sec) (M : LB G.left) (t : Fin (N + 1) → M.Sec) (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) (H.pull (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))) (g : Matrix (Fin (N + 1)) (Fin (N + 1)) K'), H.IsLB ∧ M.IsLB ∧ GlobalTheory.AbLaw.VeryAmpleBy A.hom H s ∧ GlobalTheory.AbLaw.VeryAmpleBy G.hom M t ∧ IsUnit g.det ∧ (∀ j, GlobalTheory.Cartier.SecMaps w (GlobalTheory.Cartier.secPull (t j) (pullback.fst G.hom (spMap (algebraMap W K')))) (∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (g j k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))) ∧ ∀ σ ∈ D, ∃ h : Matrix (Fin (N + 1)) (Fin (N + 1)) W, g.map σ = h.map (algebraMap W K') * g := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm D hD1 hD2 hres A _ _ hA G _ hG e he hφ
  obtain ⟨H₀, hH₀, m₀, s₀, hs₀⟩ := GlobalTheory.ProjField.isProjBy_of_isAbelianScheme K A hA
  obtain ⟨M₀, w₀, hM₀, hw₀⟩ := _root_.GlobalTheory.exists_lineBundle_extension_of_genericFibre_dvr W K' G hG (H₀.pull (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))) (pull_isLB hH₀ _)
  obtain ⟨n, hn, m₂, t₀, ht₀⟩ := _root_.GlobalTheory.ModelAmple.veryAmpleBy_pw_of_generic K W K' A hA G hG e H₀ m₀ s₀ M₀ w₀ hH₀ hs₀ hM₀ hw₀
  obtain ⟨m₁, s₁, hs₁⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw K A.left A.hom H₀ m₀ s₀ hH₀ hs₀ n hn
  obtain ⟨w, hw⟩ := _root_.GlobalTheory.PullPow.exists_isGen_iso_pw M₀ H₀ _ _ w₀ hM₀ hH₀ hw₀ n
  have hH := GlobalTheory.AbLaw.isLB_pw hH₀ n
  have hM := GlobalTheory.AbLaw.isLB_pw hM₀ n
  obtain ⟨N, t, ht, htb⟩ := _root_.GlobalTheory.exists_veryAmpleBy_basis_of_dvr W G hG _ m₂ t₀ hM ht₀
  obtain ⟨s, g, hs, hg, hgw, huniq⟩ := _root_.GlobalTheory.BasisMatch.exists_basis_match K W K' A hA G hG e _ m₁ s₁ _ w N t hH hs₁ hM hw htb
  refine ⟨N, _, s, _, t, w, g, hH, hM, hs, ht, hg, hgw, ?_⟩
  intro σ hσ
  have key : ∀ j, ∃ c : Fin (N + 1) → W, ∀ k, σ (g j k) = ∑ l, algebraMap W K' (c l) * g l k := by
    intro j
    obtain ⟨u', hu'⟩ := UpperTheory.Lit.Nos.C1.twisted_sections_extend K W K' D hD1 hD2 A hA G hG e he hφ _ _ w hH hM hw σ hσ (N + 1) s (t j) (g j) (hgw j)
    obtain ⟨c, hc, -⟩ := htb u'
    refine ⟨c, fun k => ?_⟩
    have h2 : Cartier.SecMaps w (Cartier.secPull u' (pullback.fst G.hom (spMap (algebraMap W K')))) (∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (∑ l, algebraMap W K' (c l) * g l k) • Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))) := by
      have e2 : ∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (∑ l, algebraMap W K' (c l) * g l k) • Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) = ∑ l, (pullback.fst G.hom (spMap (algebraMap W K'))).appTop (GlobalTheory.AbLaw.cst G.hom ⊤ (c l)) • ∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (g l k) • Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [appTop_cst' (pullback.fst G.hom (spMap (algebraMap W K'))) G.hom (pullback.snd G.hom (spMap (algebraMap W K'))) (algebraMap W K') pullback.condition, Finset.smul_sum, smul_smul, map_sum, map_mul, Finset.sum_smul]
        exact Finset.sum_comm
      rw [e2, hc, secPull_sum_smul']
      exact secMaps_sum_smul' w _ _ _ _ hgw
    have h3 := Cartier.SecMaps.eq (pull_isLB hM _) hu' h2
    exact congrFun (huniq _ _ h3) k
  choose c hc using key
  refine ⟨Matrix.of c, ?_⟩
  ext j k
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, hc]

end UpperTheory.Lit.Nos.C2
end
end

