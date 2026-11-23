module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2063
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2341
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenGeneratingSectionAllFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem exists_basicOpen_genSec_fibres : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB →
    ∀ (g : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S), PolFib G L g x →
    ∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧
      ∃ θ : SecAt G L (spMap (algebraMap R (Localization.Away r)) ≫ x),
        ∀ (K : Type) [Field K] (i : Localization.Away r →+* K), IsGenSec G L _ (SecAt.pull G L θ i) := by
  intro S G _ L hL g R _ _ x hx p
  obtain ⟨P, α, -, hp, w, hw⟩ := hx
  have hS : SecBaseChangeAnySt := GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny
  obtain ⟨V, hpV, hV⟩ := GlobalTheory.EmbLocal.exists_isGenSec_near hS P p
  obtain ⟨_, ⟨r, rfl⟩, hpr, hrV⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := p) (u := ((V : Set (Sp R)) : Set (PrimeSpectrum R))) hpV V.isOpen
  let j := algebraMap R (Localization.Away r)
  have hrange : Set.range (spMap j) ⊆ (V : Set (Sp R)) := by
    intro y hy
    apply hrV
    obtain ⟨z, rfl⟩ := hy
    have hz : PrimeSpectrum.comap j z ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact ⟨z, rfl⟩
    exact hz
  obtain ⟨th, hth⟩ := hV (Localization.Away r) (spMap j) hrange
  have hτ : (𝟙 (Sp (Localization.Away r)) : (Over.mk (spMap j)).left ⟶ (Over.mk (spMap j ≫ x)).left) ≫
      (Over.mk (spMap j ≫ x)).hom = (Over.mk (spMap j)).hom ≫ x := Category.id_comp _
  obtain ⟨θ, hθ⟩ := GlobalTheory.ThetaPtMove.exists_secRel_up hp (T := Over.mk (spMap j)) (T₀ := Over.mk (spMap j ≫ x))
    (𝟙 _) hτ hw hL P.isLB (a := ((1 : ℕ) : ℤ)) th
  refine ⟨r, hpr, θ, fun K _ i => ?_⟩
  have hτ' : (𝟙 (Sp K) : (Over.mk (spMap i ≫ spMap j)).left ⟶ (Over.mk (spMap i ≫ spMap j ≫ x)).left) ≫
      (Over.mk (spMap i ≫ spMap j ≫ x)).hom = (Over.mk (spMap i ≫ spMap j)).hom ≫ x := by
    simp [Category.assoc]
  let ξ : Over.mk (spMap i ≫ spMap j) ⟶ Over.mk (spMap j) := Over.homMk (spMap i) rfl
  let ξ₀ : Over.mk (spMap i ≫ spMap j ≫ x) ⟶ Over.mk (spMap j ≫ x) := Over.homMk (spMap i) rfl
  have hξ : (𝟙 (Sp K) : (Over.mk (spMap i ≫ spMap j)).left ⟶ (Over.mk (spMap i ≫ spMap j ≫ x)).left) ≫ ξ₀.left =
      ξ.left ≫ (𝟙 (Sp (Localization.Away r)) : (Over.mk (spMap j)).left ⟶ (Over.mk (spMap j ≫ x)).left) :=
    (Category.id_comp _).trans (Category.comp_id _).symm
  have hrel : GlobalTheory.ThetaPtMove.SecRel hp _ hτ' w (VVRank.pullS P.A ((1 : ℕ) : ℤ) ξ th)
      (VVRank.pullS G ((1 : ℕ) : ℤ) ξ₀ θ) :=
    GlobalTheory.Ex.OneGen.SecRel.pullS hp _ hτ hθ (T' := Over.mk (spMap i ≫ spMap j))
      (T₀' := Over.mk (spMap i ≫ spMap j ≫ x)) _ hτ' ξ ξ₀ hξ
  have : IsAffine (Over.mk (spMap j)).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk (spMap i ≫ spMap j)).left := inferInstanceAs (IsAffine (Spec _))
  have hg : IsGenSec P.A P.L 1 (VVRank.pullS P.A 1 ξ th) :=
    GlobalTheory.EmbPull.isGenSec_pullS P hS ξ hth
  have hg' : IsGenSec P.A P.L ((1 : ℕ) : ℤ) (VVRank.pullS P.A ((1 : ℕ) : ℤ) ξ th) := hg
  have : IsIso (C := Scheme.{0}) (X := (Over.mk (spMap i ≫ spMap j)).left)
      (Y := (Over.mk (spMap i ≫ spMap j ≫ x)).left) (𝟙 (Sp K)) := IsIso.id _
  have h2 : IsGenSec G L ((1 : ℕ) : ℤ) (VVRank.pullS G ((1 : ℕ) : ℤ) ξ₀ θ) :=
    GlobalTheory.ThetaPtUp.isGenSec_up hp _ hτ' hw hL P.isLB hrel hg'
  exact h2

end GlobalTheory.UMin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenIntegralOfIntegralAtPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem chart_res_res {Y : Scheme.{0}} {U V W : Y.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom x) =
      (Y.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem chart_res_app {X Y : Scheme.{0}} (α : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    (Y.presheaf.map (homOfLE (α.preimage_mono h)).op).hom ((α.app U).hom x) =
      (α.app V).hom ((X.presheaf.map (homOfLE h).op).hom x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]; rfl

theorem isIntegralElem_of_square {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : C →+* D) (a : A →+* C) (b : B →+* D) (h : g.comp a = b.comp f) {x : B}
    (hx : f.IsIntegralElem x) : g.IsIntegralElem (b x) := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.map a, hp.map a, ?_⟩
  rw [Polynomial.eval₂_map, h, ← Polynomial.hom_eval₂, hpx, map_zero]

theorem intAt_chart {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (ζ : X) :
    IntAt L α s ζ → ∀ (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → ζ ∈ W →
      ∃ c : Γ(X, W), ζ ∈ X.basicOpen c ∧ (α.app (X.basicOpen c)).hom.IsIntegralElem
        ((Y.presheaf.map (homOfLE (α.preimage_mono (X.basicOpen_le c))).op).hom (chartVal L α s j W hW)) := by
  intro hint j W hW hWa hζW
  obtain ⟨j', W', hW', hζW', hW'a, hint'⟩ := hint
  obtain ⟨c, hcle, hζc⟩ := hWa.exists_basicOpen_le (V := W ⊓ W') ⟨ζ, hζW, hζW'⟩ hζW
  refine ⟨c, hζc, ?_⟩
  have hBW : X.basicOpen c ≤ W := hcle.trans inf_le_left
  have hBW' : X.basicOpen c ≤ W' := hcle.trans inf_le_right
  have hBV : α ⁻¹ᵁ X.basicOpen c ≤ LB.wchart L (K := Fin 1) (fun _ => α) (fun _ => j) ⊓
      LB.wchart L (K := Fin 1) (fun _ => α) (fun _ => j') :=
    le_inf ((α.preimage_mono hBW).trans (locInt_le_chart L α j W hW))
      ((α.preimage_mono hBW').trans (locInt_le_chart L α j' W' hW'))
  have hBjj : X.basicOpen c ≤ L.U j ⊓ L.U j' := le_inf (hBW.trans hW) (hBW'.trans hW')
  have key := congrArg (Y.presheaf.map (homOfLE hBV).op).hom (s.compat (fun _ => j) (fun _ => j'))
  erw [chart_res_res, map_mul, chart_res_res] at key
  have ht : (Y.presheaf.map (homOfLE hBV).op).hom
      ((LB.LinComb L (K := Fin 1) (fun _ => α) (fun _ => (k : ℤ))).g (fun _ => j) (fun _ => j')).val =
      (α.app (X.basicOpen c)).hom (((X.presheaf.map (homOfLE hBjj).op).hom (L.g j j' : Γ(X, L.U j ⊓ L.U j'))) ^ k) := by
    simp only [LB.LinComb, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val, res, pullU, Units.coe_map, map_pow]
    congr 1
    erw [Units.coe_map, Units.coe_map]
    erw [chart_res_res, ← chart_res_app α hBjj]
    rfl
  have hj' : (α.app (X.basicOpen c)).hom.IsIntegralElem
      ((Y.presheaf.map (homOfLE (α.preimage_mono hBW')).op).hom (chartVal L α s j' W' hW')) :=
    isIntegralElem_of_square (α.app W').hom (α.app (X.basicOpen c)).hom (X.presheaf.map (homOfLE hBW').op).hom
      (Y.presheaf.map (homOfLE (α.preimage_mono hBW')).op).hom (RingHom.ext fun x => (chart_res_app α hBW' x).symm) hint'
  rw [chartVal] at hj' ⊢
  erw [chart_res_res] at hj' ⊢
  erw [key, ht]
  exact RingHom.IsIntegralElem.mul _ (RingHom.isIntegralElem_map _) hj'

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBiextensionGeneratorBezoutCombination
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.LamComb

section Generators

variable {X Y Z : Scheme.{0}} {L : LB X} {J K : Type} [Fintype J] [Fintype K]

omit [Fintype J] in
theorem wchart_le (φ : J → K → (Y ⟶ X)) [Fintype J] (jj : J × K → L.ι) (i : J) :
    LB.wchart L (fun q : J × K => φ q.1 q.2) jj ≤ LB.wchart L (φ i) (fun k => jj (i, k)) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)

def prodGen (φ : J → K → (Y ⟶ X)) (ε : J → K → ℤ) (δ : J → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) :
    LB.Gen (LB.LinComb L (fun q : J × K => φ q.1 q.2) (fun q => δ q.1 * ε q.1 q.2)) where
  s := fun jj => ∏ i, res (wchart_le φ jj i) ((t i).s (fun k => jj (i, k))) ^ δ i

theorem gm_prodGen (φ : J → K → (Y ⟶ X)) (ε : J → K → ℤ) (δ : J → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i)))
    (r : Z ⟶ Y) (z : Z) (jj : J × K → L.ι) (h : r z ∈ LB.wchart L (fun q : J × K => φ q.1 q.2) jj) :
    gm r z (LB.wchart L (fun q : J × K => φ q.1 q.2) jj) ((prodGen φ ε δ t).s jj) =
      ∏ i, gm r z (LB.wchart L (φ i) (fun k => jj (i, k))) ((t i).s (fun k => jj (i, k))) ^ δ i :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
    (map_zpow _ _ _).trans (congrArg (· ^ δ i) (gm_res r z _ h _)))

theorem isGen_prodGen (φ : J → K → (Y ⟶ X)) (ε : J → K → ℤ) (δ : J → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i)))
    (ht : ∀ i, (t i).IsGen) : (prodGen φ ε δ t).IsGen := by
  intro jj jj'
  refine unit_ext fun y hy => ?_
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun q : J × K => φ q.1 q.2) jj ⊓
    LB.wchart L (fun q : J × K => φ q.1 q.2) jj' := hy
  refine (gm_res (𝟙 Y) y _ hm _).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y jj jj' hm.1 hm.2) (gm_res (𝟙 Y) y _ hm _))).symm)
  refine (gm_prodGen φ ε δ t (𝟙 Y) y jj hm.1).trans
    (Eq.trans ?_ (congrArg _ (gm_prodGen φ ε δ t (𝟙 Y) y jj' hm.2)).symm)
  rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gen_trans (ht i) (𝟙 Y) y (wchart_le φ jj i hm.1) (wchart_le φ jj' i hm.2), mul_zpow]
  congr 1
  rw [trF, ← Finset.prod_zpow]
  exact Finset.prod_congr rfl fun k _ => by rw [← zpow_mul, mul_comm]

theorem val_prodGen (φ : J → K → (Y ⟶ X)) (ε : J → K → ℤ) (δ : J → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i)))
    (r : Z ⟶ Y) {z : Z} {I : (Z ⟶ X) → L.ι} (hI : Good L z I) :
    val (prodGen φ ε δ t) r z I = ∏ i, val (t i) r z I ^ δ i :=
  gm_prodGen φ ε δ t r z _ (hI.mem _ r)

end Generators

theorem prod_zpow_sum {U J : Type} [CommGroup U] (s : Finset J) (a : U) (f : J → ℤ) :
    ∏ j ∈ s, a ^ f j = a ^ ∑ j ∈ s, f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]

theorem exists_gen_lam_comb : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ {r : ℕ}
    (e c : Fin r → ℤ), ∑ j, e j * c j = 1 →
    ∃ u : LB.Gen (LB.LinComb D.P.L
        (Sum.elim (fun q : Fin r × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ c q.1) q.2)
          (fun I : ULift (Finset (Fin 2)) => (psum D.P.A (x2 D.P.A) I.down).left))
        (Sum.elim (fun q => e q.1 * Oε q.2) (fun I => -((-1) ^ (2 - I.down.card))))), u.IsGen ∧
      ∀ (a b : D.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        val (D.tau a b) (𝟙 _) z J = val u (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J *
          ∏ j, val (D.tau a (c j • b)) (𝟙 _) z J ^ e j := by
  intro R _ _ D hD r e c hec
  choose g hg hv using fun j => _root_.GlobalTheory.Mum.exists_lamGen_zpow D hD (c j)
  have hF : FormEq (fun q : Fin r × (Fin 4 ⊕ Fin 4) => Sum.elim
        (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ c q.1))
        (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A)) q.2)
      (fun q => e q.1 * Sum.elim Oε (fun l => -c q.1 * Oε l) q.2)
      (Sum.elim (fun q : Fin r × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ c q.1) q.2)
          (fun I : ULift (Finset (Fin 2)) => (psum D.P.A (x2 D.P.A) I.down).left))
      (Sum.elim (fun q => e q.1 * Oε q.2) (fun I => -((-1) ^ (2 - I.down.card)))) := by
    intro U _ h
    simp only [Fintype.prod_prod_type, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_comm]
    have k : ∀ l, ∏ j, h (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A) l) ^ (e j * (-c j * Oε l)) =
        h (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A) l) ^ (-Oε l) := fun l => by
      rw [prod_zpow_sum]
      congr 1
      calc ∑ j, e j * (-c j * Oε l) = (∑ j, e j * c j) * (-Oε l) := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = -Oε l := by rw [hec, _root_.one_mul]
    simp only [k]
    rw [← Equiv.ulift.symm.prod_comp, show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} from by decide,
      Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton,
      Fin.prod_univ_four]
    have q0 : psum D.P.A (x2 D.P.A) ∅ = 1 := rfl
    have q1 : psum D.P.A (x2 D.P.A) {0} = fst D.P.A D.P.A := _root_.mul_one _
    have q2 : psum D.P.A (x2 D.P.A) {1} = snd D.P.A D.P.A := _root_.mul_one _
    have q3 : psum D.P.A (x2 D.P.A) {0, 1} = fst D.P.A D.P.A * snd D.P.A D.P.A :=
      congrArg (fst D.P.A D.P.A * ·) (_root_.mul_one _)
    simp [q0, q1, q2, q3, GlobalTheory.PolDeg.lamPts, Oε]
    generalize h (fst D.P.A D.P.A * snd D.P.A D.P.A).left = A, h (fst D.P.A D.P.A).left = A₁,
      h (snd D.P.A D.P.A).left = A₂, h (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left = A₀
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨u, hu, hval⟩ := exists_gen D.P.isLB hF (prodGen _ _ e g) (isGen_prodGen _ _ e g hg)
  refine ⟨u, hu, fun a b z J hJ => ?_⟩
  rw [hval _ _ z J hJ, val_prodGen _ _ e g _ hJ, ← Finset.prod_mul_distrib]
  have : ∀ j, val (g j) (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J ^ e j *
      val (D.tau a (c j • b)) (𝟙 _) z J ^ e j = val (D.tau a b) (𝟙 _) z J ^ (e j * c j) := fun j => by
    rw [← mul_zpow, mul_comm, hv j a b z J hJ, ← zpow_mul, mul_comm]
  rw [Finset.prod_congr rfl fun j _ => this j, prod_zpow_sum, hec, zpow_one]

end GlobalTheory.Mum.LamComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBigCellPointBasicOpenAffineSpaceCoords
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

noncomputable section

namespace GlobalTheory.LogPole

theorem eq_of_eq_lower_mul_upper {S : Type} [CommRing S] {m : ℕ} {M B L N : Matrix (Fin m) (Fin m) S}
    (hB : ∀ i j, i < j → B i j = 0) (hL : ∀ i j, i < j → L i j = 0)
    (hN : ∀ i j, j < i → N i j = 0) (hN1 : ∀ i, N i i = 1)
    (hM : ∀ i j, j < i → M i j = 0) (hM1 : ∀ i, M i i = 1) (h : M = B * (L * N)) : M = N := by
  set C := B * L with hC
  have hClow : ∀ i j, i < j → C i j = 0 := fun i j hij => by
    rw [hC, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge i l with h1 | h1
    · rw [hB i l h1, zero_mul]
    · rw [hL l j (lt_of_le_of_lt h1 hij), mul_zero]
  have hMC : M = C * N := by rw [h, hC, Matrix.mul_assoc]
  have hNt : N.BlockTriangular id := fun i j hij => hN i j hij
  have hdet : IsUnit N.det := by
    rw [Matrix.det_of_upperTriangular hNt]
    simp [hN1]
  have hCM : C = M * N⁻¹ := by
    rw [hMC, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  letI := N.invertibleOfIsUnitDet hdet
  have hMt : M.BlockTriangular id := fun i j hij => hM i j hij
  have hCup : C.BlockTriangular id := hCM ▸ hMt.mul (Matrix.blockTriangular_inv_of_blockTriangular hNt)
  have hC1 : C = 1 := by
    ext i j
    rcases lt_trichotomy i j with h1 | rfl | h1
    · rw [hClow i j h1, Matrix.one_apply_ne h1.ne]
    · have e := congrFun (congrFun hMC i) i
      rw [Matrix.mul_apply, Finset.sum_eq_single i (fun l _ hl => ?_) (by simp), hN1, mul_one, hM1] at e
      · rw [← e, Matrix.one_apply_eq]
      · rcases lt_or_gt_of_ne hl with h2 | h2
        · rw [hCup (show id l < id i from h2), zero_mul]
        · rw [hN l i h2, mul_zero]
    · rw [hCup (show id j < id i from h1), Matrix.one_apply_ne h1.ne']
  rw [hMC, hC1, Matrix.one_mul]

theorem top_le_basicOpen_of_isUnit {S : Type} [CommRing S] {X : Scheme.{0}} (x : Sp S ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) (hu : IsUnit (ev x U h a)) : ⊤ ≤ x ⁻¹ᵁ X.basicOpen a := by
  have hu' : IsUnit ((x.appLE U ⊤ h).hom a) := by
    have : (x.appLE U ⊤ h).hom a = (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (ev x U h a) := by
      show _ = (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom _)
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
      rfl
    rw [this]
    exact hu.map _
  have e := Scheme.basicOpen_appLE x ⊤ U h a
  rw [Scheme.basicOpen_of_isUnit _ hu', top_inf_eq] at e
  exact e.le

theorem exists_basicOpen_sub {A : Type} [CommRing A] (O : (Sp A).Opens) (p : Sp A) (hp : p ∈ O) :
    ∃ f : A, f ∉ p.asIdeal ∧ ∀ q : Sp A, f ∉ q.asIdeal → q ∈ O := by
  have hO : IsOpen ((O : Set (Sp A)) : Set (PrimeSpectrum A)) := O.isOpen
  obtain ⟨_, ⟨f, rfl⟩, hpf, hfle⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens (R := A)).exists_subset_of_mem_open
    (a := p) hp hO
  exact ⟨f, hpf, fun q hq => hfle hq⟩

theorem exists_away_sub {R : Type} [CommRing R] (c : R) (O : (Sp (Localization.Away c)).Opens)
    (p : Sp (Localization.Away c)) (hp : p ∈ O) :
    ∃ (h : R) (ι : Localization.Away c →+* Localization.Away (c * h)), ¬ IsNilpotent (c * h) ∧
      (∀ x, ι (algebraMap R _ x) = algebraMap R _ x) ∧ ⊤ ≤ spMap ι ⁻¹ᵁ O := by
  obtain ⟨f, hpf, hfle⟩ := exists_basicOpen_sub O p hp
  obtain ⟨⟨h', s⟩, hs⟩ := IsLocalization.mk'_surjective (Submonoid.powers c) f
  have hfs : f * algebraMap R (Localization.Away c) s.1 = algebraMap R _ h' := by
    rw [← hs]; exact IsLocalization.mk'_spec _ h' s
  let ι : Localization.Away c →+* Localization.Away (c * h') := IsLocalization.Away.awayToAwayRight c h'
  have hι : ∀ x, ι (algebraMap R _ x) = algebraMap R (Localization.Away (c * h')) x :=
    fun x => IsLocalization.Away.awayToAwayRight_eq c h' x
  have hgu : IsUnit (algebraMap R (Localization.Away (c * h')) (c * h')) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hιf : IsUnit (ι f) := by
    have e := congrArg ι hfs
    rw [map_mul, hι, hι] at e
    rw [map_mul] at hgu
    have hh' := isUnit_of_mul_isUnit_right hgu
    rw [← e] at hh'
    exact isUnit_of_mul_isUnit_left hh'
  refine ⟨h', ι, ?_, hι, fun q _ => ?_⟩
  · rintro ⟨m, hm⟩
    have hA : (algebraMap R (Localization.Away c) (c * h')) ^ m ∈ p.asIdeal := by
      rw [← map_pow, hm, map_zero]; exact p.asIdeal.zero_mem
    have hA' := p.isPrime.mem_of_pow_mem _ hA
    rw [map_mul, ← hfs] at hA'
    have hCa : IsUnit (algebraMap R (Localization.Away c) c) := IsLocalization.Away.algebraMap_isUnit _
    have hsu : IsUnit (algebraMap R (Localization.Away c) s.1) := IsLocalization.map_units _ s
    rcases p.isPrime.mem_or_mem hA' with h1 | h1
    · exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 hCa)
    · rcases p.isPrime.mem_or_mem h1 with h2 | h2
      · exact hpf h2
      · exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 hsu)
  · have : f ∉ ((spMap ι) q).asIdeal := fun hq => q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hq hιf)
    exact hfle _ this

theorem not_isNilpotent_of_comp_eq {R T : Type} [CommRing R] [CommRing T] (g : R) (hg : ¬ IsNilpotent g)
    (φ : R →+* T) (ψ : T →+* Localization.Away g) (h : ψ.comp φ = algebraMap R _) : ¬ IsNilpotent (φ g) := by
  rintro ⟨m, hm⟩
  have e : algebraMap R (Localization.Away g) (g ^ m) = 0 := by
    rw [map_pow, ← h, RingHom.comp_apply, ← map_pow, hm, map_zero]
  obtain ⟨⟨_, m', rfl⟩, hm'⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ _).1 e
  exact hg ⟨m' + m, by rw [pow_add]; exact hm'⟩

theorem exists_section_of_away {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (W V : Y.Opens) (hWU : W ≤ f ⁻¹ᵁ U)
    {I : Type} (cc : I → Γ(Y, W)) (a : Γ(X, U)) (ha : f ⁻¹ᵁ X.basicOpen a ≤ V)
    (z₁ : Sp (Localization.Away (MvPolynomial.C a : MvPolynomial I Γ(X, U))) ⟶ Y) (hV : ⊤ ≤ z₁ ⁻¹ᵁ V)
    (hU : ⊤ ≤ (z₁ ≫ f) ⁻¹ᵁ U)
    (hbase : ∀ r, ev (z₁ ≫ f) U hU r = algebraMap (MvPolynomial I Γ(X, U)) _ (MvPolynomial.C r))
    (p : Sp (Localization.Away (MvPolynomial.C a : MvPolynomial I Γ(X, U)))) (hp : p ∈ z₁ ⁻¹ᵁ W)
    (hrel : ∀ (S : Type) [CommRing S] (ψ : Localization.Away (MvPolynomial.C a : MvPolynomial I Γ(X, U)) →+* S)
      (hW : ⊤ ≤ (spMap ψ ≫ z₁) ⁻¹ᵁ W) (i : I),
      ev (spMap ψ ≫ z₁) W hW (cc i) = ψ (algebraMap (MvPolynomial I Γ(X, U)) _ (MvPolynomial.X i))) :
    ∃ g : MvPolynomial I Γ(X, U), ¬ IsNilpotent (MvPolynomial.eval₂Hom (f.appLE U W hWU).hom cc g) ∧
      (∀ (S : Type) [CommRing S] (z₀ : Sp S ⟶ Y) (hz₀ : ⊤ ≤ z₀ ⁻¹ᵁ W),
        IsUnit (ev z₀ W hz₀ (MvPolynomial.eval₂Hom (f.appLE U W hWU).hom cc g)) → ⊤ ≤ z₀ ⁻¹ᵁ V) ∧
      ∃ (z : Sp (Localization.Away g) ⟶ Y) (hz : ⊤ ≤ z ⁻¹ᵁ W), ⊤ ≤ z ⁻¹ᵁ V ∧
        (∀ r, ev z W hz ((f.appLE U W hWU).hom r) =
          algebraMap (MvPolynomial I Γ(X, U)) (Localization.Away g) (MvPolynomial.C r)) ∧
        ∀ i, ev z W hz (cc i) = algebraMap (MvPolynomial I Γ(X, U)) (Localization.Away g) (MvPolynomial.X i) := by
  obtain ⟨h', ι, hnil, hι, hz⟩ := exists_away_sub _ (z₁ ⁻¹ᵁ W) p hp
  have hz' : ⊤ ≤ (spMap ι ≫ z₁) ⁻¹ᵁ W := hz
  have hbz : ∀ r, ev (spMap ι ≫ z₁) W hz' ((f.appLE U W hWU).hom r) =
      algebraMap (MvPolynomial I Γ(X, U)) _ (MvPolynomial.C r) := fun r => by
    rw [FlagMod.ev_appLE (spMap ι ≫ z₁) f hWU hz' (FlagMod.le_preimage_map f hWU hz'),
      FlagMod.ev_congr (Category.assoc _ _ _) U _ (FlagMod.le_preimage_comp (spMap ι) hU),
      FlagMod.ev_spMap ι (z₁ ≫ f) U hU, RingHom.comp_apply, hbase, hι]
  have hcz : ∀ i, ev (spMap ι ≫ z₁) W hz' (cc i) =
      algebraMap (MvPolynomial I Γ(X, U)) _ (MvPolynomial.X i) := fun i => by
    rw [hrel _ ι hz' i, hι]
  refine ⟨MvPolynomial.C a * h', ?_, ?_, spMap ι ≫ z₁, hz', FlagMod.le_preimage_comp _ hV, hbz, hcz⟩
  · refine not_isNilpotent_of_comp_eq _ hnil _ (ev (spMap ι ≫ z₁) W hz') ?_
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      exact hbz r
    · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      exact hcz i
  · intro S _ z₀ hz₀ hu
    rw [map_mul, map_mul] at hu
    have hu1 := isUnit_of_mul_isUnit_left hu
    rw [MvPolynomial.eval₂Hom_C, FlagMod.ev_appLE z₀ f hWU hz₀ (FlagMod.le_preimage_map f hWU hz₀)] at hu1
    have hb := top_le_basicOpen_of_isUnit _ _ _ a hu1
    exact fun q _ => ha (hb (Set.mem_univ q))

theorem map_entry_eq_of_lower_mul {R A S : Type} [CommRing R] [CommRing A] [CommRing S] {m : ℕ} (χ : R →+* S)
    (ε : A →+* S) (t : ∀ i j : Fin m, i < j → R) {L N : Matrix (Fin m) (Fin m) A} {b : Matrix (Fin m) (Fin m) S}
    (hL : ∀ i j, i < j → L i j = 0) (hN : ∀ i j, j < i → N i j = 0) (hN1 : ∀ i, N i i = 1)
    (hb : ∀ i j, i < j → b i j = 0)
    (hbe : ∀ i j, χ (if h : i < j then t i j h else if i = j then 1 else 0) = ∑ k, b i k * ε ((L * N) k j))
    (i j : Fin m) (hij : i < j) : ε (N i j) = χ (t i j hij) := by
  have key := eq_of_eq_lower_mul_upper
    (M := Matrix.of fun i j => χ (if h : i < j then t i j h else if i = j then 1 else 0))
    (B := b) (L := L.map ε) (N := N.map ε) hb
    (fun i j hij => by simp [Matrix.map_apply, hL i j hij])
    (fun i j hij => by simp [Matrix.map_apply, hN i j hij])
    (fun i => by simp [Matrix.map_apply, hN1 i])
    (fun i j hij => by simp [Matrix.of_apply, not_lt.2 hij.le, hij.ne'])
    (fun i => by simp [Matrix.of_apply])
    (by
      ext i j
      rw [Matrix.of_apply, hbe i j, ← Matrix.map_mul, Matrix.mul_apply]
      rfl)
  have e := congrFun (congrFun key i) j
  simp only [Matrix.of_apply, Matrix.map_apply, dif_pos hij] at e
  exact e.symm

theorem exists_cell_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), Nonempty W → ∃ g : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1), ¬ IsNilpotent (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N) g) ∧ (∀ (S : Type) [CommRing S] (z₀ : Sp S ⟶ Y₀ TF.X Z) (hz₀ : ⊤ ≤ z₀ ⁻¹ᵁ W), IsUnit (ev z₀ W hz₀ (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N) g)) → ⊤ ≤ z₀ ⁻¹ᵁ U₀ TF.X Z) ∧ ∃ (z : Sp (Localization.Away g) ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W), ⊤ ≤ z ⁻¹ᵁ U₀ TF.X Z ∧ (∀ r, ev z W hz (((toBase TF Z).appLE U.1 W h.2.1).hom r) = algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) (Localization.Away g) (MvPolynomial.C r)) ∧ ∀ i, ev z W hz (cellCoord N i) = algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) (Localization.Away g) (MvPolynomial.X i) := by
  intro E _ _ _ H Dw l Xo c TF Z hF U n e v hv W k L N h hWne
  have h1 := exists_basicOpen_cell_choose E H Dw l Xo c TF Z U W k h.2.1 h.2.2.1 hWne
  refine h1.elim fun a ha => ?_
  have h2 := GlobalTheory.T.exists_bigCellSection_over_basicOpen_interior E H Dw l Xo c TF Z hF U n e v hv W k L N h a ha.1 ha.2
  refine h2.elim fun z₁ hz₁ => hz₁.2.1.elim fun hU hbase => hz₁.2.2.1.elim fun p hp => ?_
  refine exists_section_of_away (toBase TF Z) U.1 W (U₀ TF.X Z) h.2.1 (cellCoord N) a ?_ z₁ hz₁.1 hU hbase p hp ?_
  · intro w hw
    have hcomp : toBase TF Z w = TF.X.π w.1 := Scheme.Hom.comp_apply _ _ _
    have hI : toBase TF Z w ∈ LogKS.interior TF.Y := (ha.1 hw).1.1
    rw [hcomp] at hI
    exact hI
  · intro S _ ψ hW i
    refine (hz₁.2.2.2 S ψ hW i.1).elim fun b hb => ?_
    exact map_entry_eq_of_lower_mul (ψ.comp (algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) _))
      (ev (spMap ψ ≫ z₁) W hW) (fun i' j' hij => MvPolynomial.X ⟨i.1, ⟨(i', j'), hij⟩⟩)
      (h.2.2.2.1 i.1) (h.2.2.2.2.2.1 i.1) (h.2.2.2.2.2.2.1 i.1) hb.1 hb.2 i.2.1.1 i.2.1.2 i.2.2

end GlobalTheory.LogPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatiblePrimitiveRootsThroughStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_primitiveRoots_through : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (A : ℕ) (ω : K), 0 < A → IsPrimitiveRoot ω A → ∃ ζ : ℕ → Kˣ, (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) ∧ (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) ∧ (ζ A : K) = ω := by
  first | exact @GlobalTheory.RootSystem.exists_compatible_roots_through | exact GlobalTheory.RootSystem.exists_compatible_roots_through | (intros; apply GlobalTheory.RootSystem.exists_compatible_roots_through <;> assumption)
end

