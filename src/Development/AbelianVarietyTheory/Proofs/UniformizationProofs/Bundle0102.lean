module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BoxLeOfComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0093
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsFunctional
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifPowAdm

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Comb

variable {K : Type} [CommRing K] {Y Y' : Scheme.{0}}

def cstHom (π : Y ⟶ Spec (CommRingCat.of K)) (W : Y.Opens) : K →+* Γ(Y, W) :=
  (Y.presheaf.map (homOfLE le_top).op).hom.comp
    (π.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

theorem res_cstHom (π : Y ⟶ Spec (CommRingCat.of K)) {W W' : Y.Opens} (h : W' ≤ W) (c : K) :
    (Y.presheaf.map (homOfLE h).op).hom (cstHom π W c) = cstHom π W' c :=
  SecOps.resTop_res h _

def IsComb (π : Y ⟶ Spec (CommRingCat.of K)) {M : LB Y} {Λ : Type} [Fintype Λ] (s : LB.Sec M) (c : Λ → K)
    (t : Λ → LB.Sec M) : Prop :=
  ∀ jj, s.f jj = ∑ l, cstHom π (M.U jj) (c l) * (t l).f jj

variable (π : Y ⟶ Spec (CommRingCat.of K)) {M : LB Y} {Λ Λ' : Type} [Fintype Λ] [Fintype Λ']

theorem exists_isComb (c : Λ → K) (t : Λ → LB.Sec M) : ∃ s, IsComb π s c t :=
  ⟨⟨fun jj => ∑ l, cstHom π (M.U jj) (c l) * (t l).f jj, fun i j => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, (t l).compat, res_cstHom, map_mul, res_cstHom, mul_left_comm]⟩, fun _ => rfl⟩

variable {π}

theorem IsComb.trans {s : LB.Sec M} {c : Λ → K} {t : Λ → LB.Sec M} {d : Λ → Λ' → K} {u : Λ' → LB.Sec M}
    (h : IsComb π s c t) (h' : ∀ l, IsComb π (t l) (d l) u) : IsComb π s (fun a => ∑ l, c l * d l a) u := by
  intro jj
  rw [h jj]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h' _ jj, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
  exact Finset.sum_comm

theorem IsComb.unique {s s' : LB.Sec M} {c : Λ → K} {t : Λ → LB.Sec M}
    (h : IsComb π s c t) (h' : IsComb π s' c t) : s = s' :=
  SecOps.sec_ext fun jj => (h jj).trans (h' jj).symm

end Comb

section Box

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {LG : LB G.left} {LG' : LB G'.left}

end Box

section Exp

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ)

theorem expands_comb {Λ : Type} [Fintype Λ] {c : Λ → FractionRing R} {s : Λ → U.SecK k}
    {E : Λ → Fam D.toPre (FractionRing R) k} {s₀ : U.SecK k} (h : ∀ l, U.Expands k (s l) (E l))
    (h₀ : IsComb (pullback.snd G.hom (jK R)) s₀ c s) : U.Expands k s₀ (∑ l, c l • E l) := by
  have e := (Fintype.equivFin Λ).symm
  rw [← e.sum_comp]
  exact ExpandsFracLinear.main R I D A G U k _ (fun l => c (e l)) (fun l => s (e l)) (fun l => E (e l)) s₀
    (fun l => h _) (fun jj => (h₀ jj).trans (e.sum_comp _).symm)

theorem expands_functional (hR : AdmBase R I) {s : U.SecK k} {E E' : Fam D.toPre (FractionRing R) k}
    (h : U.Expands k s E) (h' : U.Expands k s E') : E = E' := by
  have h₀ : U.Expands k SecOps.secZero (∑ l : Fin 2, (![1, -1] : Fin 2 → FractionRing R) l • ![E, E'] l) :=
    expands_comb U k (s := fun _ => s) (fun l => by fin_cases l; exacts [h, h']) (fun jj => by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_neg, map_one, neg_mul, add_neg_cancel]
      rfl)
  have h₁ := GlobalTheory.ExpZero.main R I D A G U k hR _ _ (fun _ => rfl) h₀
  rw [Fin.sum_univ_two] at h₁
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at h₁
  exact add_neg_eq_zero.1 h₁

theorem expBij_of_basis (hR : AdmBase R I) {Λ : Type} [Fintype Λ]
    (b : Module.Basis Λ (FractionRing R) (Fam D.toPre (FractionRing R) k)) (σ : Λ → U.SecK k)
    (hσ : ∀ l, U.Expands k (σ l) (b l)) (hspan : ∀ s, ∃ c, IsComb (pullback.snd G.hom (jK R)) s c σ) :
    U.ExpBij k := by
  refine ⟨fun s => ?_, fun E => ?_⟩
  · obtain ⟨c, hc⟩ := hspan s
    exact ⟨_, expands_comb U k hσ hc, fun E hE => expands_functional U k hR hE (expands_comb U k hσ hc)⟩
  · obtain ⟨s, hs⟩ := exists_isComb (pullback.snd G.hom (jK R)) (b.equivFun E) σ
    refine ⟨s, ?_, fun t ht => ?_⟩
    · have := expands_comb U k hσ hs
      rwa [b.sum_equivFun] at this
    · obtain ⟨c, hc⟩ := hspan t
      have e := expands_functional U k hR ht (expands_comb U k hσ hc)
      have e' : b.equivFun E = c := by rw [e, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
      exact hc.unique (e' ▸ hs)

end Exp

end GlobalTheory.UnifPowAdm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InducedFrobeniusCompUniqueOrigin
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.IndComp

section Twist

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A] {L : LB A.left}

theorem twist_unique (hL : L.IsLB) {ψ : T ⊗ A ⟶ T ⊗ A} {n : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ ≫ snd _ _).left] ![n, -n])}
    {t u u' : LB.Sec (LPow A L n T)} (h : IsTwistPull A L ψ (ψ ≫ snd _ _) rfl n n α t u)
    (h' : IsTwistPull A L ψ (ψ ≫ snd _ _) rfl n n α t u') : u = u' := by
  have e : ∀ j, u.f j = u'.f j := fun j => sec_ext_val hL (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => n)
    (fun y J hJ => (VVRank.sv_of_isTwistPull A h (𝟙 _) y hJ).trans (VVRank.sv_of_isTwistPull A h' (𝟙 _) y hJ).symm) j
  obtain ⟨a, _⟩ := u
  obtain ⟨b, _⟩ := u'
  obtain rfl : a = b := funext e
  rfl

theorem exists_twist_comp (hL : L.IsLB) (ψ ψ' : T ⊗ A ⟶ T ⊗ A) (n : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ ≫ snd _ _).left] ![n, -n]))
    (α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ' ≫ snd _ _).left] ![n, -n]))
    (hα : α.IsGen) (hα' : α'.IsGen) :
    ∃ β : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, ((ψ ≫ ψ') ≫ snd _ _).left] ![n, -n]), β.IsGen ∧
      ∀ t u v : LB.Sec (LPow A L n T), IsTwistPull A L ψ' (ψ' ≫ snd _ _) rfl n n α' t u →
        IsTwistPull A L ψ (ψ ≫ snd _ _) rfl n n α u v →
        IsTwistPull A L (ψ ≫ ψ') ((ψ ≫ ψ') ≫ snd _ _) rfl n n β t v := by
  obtain ⟨β, hβ, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, ((ψ ≫ ψ') ≫ snd _ _).left]) (ε' := ![n, -n])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, zpow_neg, Over.comp_left, Category.assoc]
      rw [_root_.mul_assoc, inv_mul_cancel_left])
    (LB.mulGen L _ _ _ _ α (LB.pullGen L _ _ α' ψ.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hα (DVR.pullGen_isGen _ _ _ _ hα' _))
  refine ⟨β, hβ, fun t u v hu hv' => VVRank.isTwistPull_of_sv A hL hβ fun y J hJ => ?_⟩
  rw [VVRank.sv_of_isTwistPull A hv' (𝟙 _) y hJ, VVRank.sv_of_isTwistPull A hu _ y hJ, hv _ _ y J hJ, val_mul hJ,
    val_pull hJ, Units.val_mul, _root_.mul_assoc, Over.comp_left _ _ _ ψ ψ', Category.assoc]

theorem exists_twist_id (hL : L.IsLB) (n : ℤ) :
    ∃ β : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (𝟙 (T ⊗ A) ≫ snd _ _).left] ![n, -n]), β.IsGen ∧
      ∀ t : LB.Sec (LPow A L n T), IsTwistPull A L (𝟙 _) (𝟙 _ ≫ snd _ _) rfl n n β t t := by
  obtain ⟨β, hβ, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (𝟙 (T ⊗ A) ≫ snd _ _).left]) (ε' := ![n, -n])
    (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, Category.id_comp,
        mul_inv_cancel]
      exact Fintype.prod_empty _)
    (LB.oneGen L (Y := (T ⊗ A).left))
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  refine ⟨β, hβ, fun t => VVRank.isTwistPull_of_sv A hL hβ fun y J hJ => ?_⟩
  rw [hv _ _ y J hJ, val_one, Units.val_one, _root_.one_mul, Over.id_left, Category.comp_id]

end Twist

theorem indAt_comp_unique : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p p' p'' : QkPt D.toPre F N) (ψ ψ' : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)), IndAt U.toUnifPre F N p ψ → (IndAt U.toUnifPre F N p' ψ' → QkAdd p p' p'' → IndAt U.toUnifPre F N p'' (ψ ≫ ψ')) ∧ (QkPt.Equiv D.toPre F p p' → IndAt U.toUnifPre F N p' ψ) ∧ (4 ≤ N → IndAt U.toUnifPre F N p ψ' → ψ = ψ') ∧ (p'.y = 0 → p'.g.IsZero → IndAt U.toUnifPre F N p' (𝟙 _)) := by
  intro hL R _ _ _ I hR D A G _ _ _ U F _ _ _ N hN p p' p'' ψ ψ' hψ
  have hG := hL.1.globalFns
  obtain ⟨Φ, hrel, -, hrat, hequ, hadd, hone⟩ := PhiProj.phi_projective hL R I hR D F N hN
  refine ⟨fun hψ' hs => ⟨by rw [Category.assoc, hψ'.1, hψ.1], fun w₀ hw₀ => ?_⟩, fun he => ⟨hψ.1, fun w₀ hw₀ => ?_⟩,
    fun h4 hψ' => ?_, fun hy hg => ⟨Category.id_comp _, fun w₀ hw₀ => ?_⟩⟩
  · obtain ⟨α, w, hα, hw, h⟩ := hψ.2 w₀ hw₀
    obtain ⟨α', w', hα', hw', h'⟩ := hψ'.2 w₀ hw₀
    obtain ⟨w'', hw'', hΦ⟩ := hadd p p' p'' w w' hw hw' hs
    obtain ⟨β, hβ, hc⟩ := exists_twist_comp A.isLB ψ ψ' (N : ℤ) α α' hα hα'
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
    refine ⟨β, w'', hβ, hw'', fun t t' s s' ht ht' H => ?_⟩
    obtain ⟨u, hu⟩ := VVRank.exists_isTwistPull A.A (hm := rfl) A.isLB hα' t
    obtain ⟨v, hv⟩ := VVRank.exists_isTwistPull A.A (hm := rfl) A.isLB hα u
    obtain rfl : v = t' := twist_unique A.isLB (hc t u v hu hv) H
    have e₁ := ((hrel p' w' hw').2 _ _).1 (h' t u s _ ht ((he u _).2 rfl) hu)
    have e₂ := ((hrel p w hw).2 _ _).1 (h u v _ s' ((he u _).2 rfl) ht' hv)
    refine ((hrel p'' w'' hw'').2 _ _).2 ?_
    rw [hΦ, LinearMap.comp_apply, ← e₁, e₂]
  · obtain ⟨α, w, hα, hw, h⟩ := hψ.2 w₀ hw₀
    obtain ⟨w', hw', hΦ⟩ := hequ p p' w hw he
    refine ⟨α, w', hα, hw', fun t t' s s' ht ht' H => ((hrel p' w' hw').2 _ _).2 ?_⟩
    rw [hΦ]
    exact ((hrel p w hw).2 _ _).1 (h t t' s s' ht ht' H)
  · obtain ⟨w₀, hw₀⟩ := U.ext
    obtain ⟨α, w, hα, hw, h⟩ := hψ.2 w₀ hw₀
    obtain ⟨α', w', hα', hw', h'⟩ := hψ'.2 w₀ hw₀
    obtain ⟨c, hc, hΦ⟩ := hrat p w w' hw hw'
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
    refine AutUniq.endo_eq_of_sections hL R A F N h4 ψ ψ' hψ.1 hψ'.1 α α' hα hα'
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 c hc)) fun t t₁ t₂ h₁ h₂ j => ?_
    have e₁ := ((hrel p w hw).2 _ _).1 (h t t₁ _ _ ((he t _).2 rfl) ((he t₁ _).2 rfl) h₁)
    have e₂ := ((hrel p w' hw').2 _ _).1 (h' t t₂ _ _ ((he t _).2 rfl) ((he t₂ _).2 rfl) h₂)
    rw [hΦ, LinearMap.smul_apply, ← e₁] at e₂
    exact congrArg (fun x => LB.Sec.f x j) (e.injective (e₂.trans (e.map_smul c t₁).symm))
  · obtain ⟨w, hw⟩ := (CoefBasic.coef_basic R D.toPre F N p'.g).2.1 hg.1
    obtain ⟨β, hβ, hc⟩ := exists_twist_id (T := TFK (R := R) F) A.isLB (N : ℤ)
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
    refine ⟨β, w, hβ, hw.1, fun t t' s s' ht ht' H => ((hrel p' w hw.1).2 _ _).2 ?_⟩
    obtain rfl : t = t' := twist_unique A.isLB (hc t) H
    rw [hone p' w hy hg hw]
    exact ((he _ _).1 ht').symm.trans ((he _ _).1 ht)

end GlobalTheory.UT.IndComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsFiniteOfPullVeryAmpleIsoPow
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PullAmpleFinite

open TopologicalSpace GlobalTheory.MulFinite

theorem sec_gs {Z Y : Scheme.{0}} {M : LB Y} (s : LB.Sec M) (r : Z ⟶ Y) (z : Z) {j j' : M.ι}
    (hj : r z ∈ M.U j) (hj' : r z ∈ M.U j') :
    gs r z (M.U j) (s.f j) = (gm r z (M.U j ⊓ M.U j') (M.g j j')).val * gs r z (M.U j') (s.f j') := by
  have hm : r z ∈ M.U j ⊓ M.U j' := ⟨hj, hj'⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat j j')).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

theorem pow_cancel {R : Type} [CommRing R] (g t : Rˣ) (x : R) (e : ℕ) :
    (g.val * x) ^ e * (1 * (g ^ (e : ℤ))⁻¹ * t).val = x ^ e * t.val := by
  have h : (g ^ e * (1 * (g ^ (e : ℤ))⁻¹ * t)) = t := by
    rw [zpow_natCast, _root_.one_mul, mul_inv_cancel_left]
  have h' : g.val ^ e * (1 * (g ^ (e : ℤ))⁻¹ * t).val = t.val := congrArg Units.val h
  rw [mul_pow, ← h']; ring

theorem exists_fn {X W Z : Scheme.{0}} (H : LB X) (hH : H.IsLB) (L : LB W) (hL : L.IsLB)
    (s : LB.Sec L) (m : W ⟶ X) (e : ℕ) (he : e ≠ 0)
    (α : LB.Iso (pw L e) (H.pull m)) (hα : α.IsGen)
    (r : Z ⟶ W) (j₀ : H.ι) (h₀ : ∀ z, m (r z) ∈ H.U j₀) :
    ∃ a : Γ(Z, ⊤), Z.basicOpen a = r ⁻¹ᵁ nonzeroLocus s := by
  let V : L.ι → Z.Opens := fun j => r ⁻¹ᵁ L.U j
  have l₂ : ∀ j, V j ≤ r ⁻¹ᵁ ((H.pull m).U (fun _ => j₀) ⊓ (pw L e).U j) :=
    fun j z hz => ⟨mem_pull.2 (h₀ z), hz⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(Z, V j), ∀ j z, z ∈ V j → gs (𝟙 Z) z (V j) (u j) =
      gs r z (L.U j) (s.f j) ^ e * (gw α r z j₀ j).val := by
    refine ⟨fun j => (r.appLE _ _ le_rfl).hom (s.f j) ^ e *
      (r.appLE _ _ (l₂ j)).hom (α.s (fun _ => j₀, j)).val, fun j z hz => ?_⟩
    refine (gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·) ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_) ?_)
    · exact congrArg (· ^ e) (gs_appLE r z _ _ _ hz _)
    · exact (gs_appLE r z _ _ _ hz _).trans (gs_unit r z _ (l₂ j hz) _)
  have hcov : (⊤ : Z.Opens) ≤ iSup V := fun z _ => by
    obtain ⟨j, hj⟩ := Geo.Tor.exists_chart hL (r z)
    exact Opens.mem_iSup.2 ⟨j, hj⟩
  obtain ⟨a, ha, -⟩ := Z.sheaf.existsUnique_gluing' V ⊤ (fun j => homOfLE le_top) hcov u
    (fun j j' => fn_ext (V := V j ⊓ V j') fun z hz => by
      refine (gs_res (𝟙 Z) z inf_le_left hz _).trans (Eq.trans ?_ (gs_res (𝟙 Z) z inf_le_right hz _).symm)
      rw [hu j z hz.1, hu j' z hz.2, sec_gs s r z hz.1 hz.2,
        (isGen_iff α).1 hα Z r z j₀ j₀ j j' (h₀ z) (h₀ z) hz.1 hz.2]
      have h1 : gm (r ≫ m) z (H.U j₀ ⊓ H.U j₀) (H.g j₀ j₀) = 1 := gm_self hH _ z (h₀ z)
      have t₁ : gm r z ((pw L e).U j ⊓ (pw L e).U j') ((pw L e).g j j') =
          gm r z (L.U j ⊓ L.U j') (L.g j j') ^ (e : ℤ) := map_zpow _ _ _
      rw [h1, t₁]
      exact pow_cancel _ _ _ _)
  refine ⟨a, ?_⟩
  ext z
  obtain ⟨j, hj⟩ := Geo.Tor.exists_chart hL (r z)
  have k₁ : gs (𝟙 Z) z ⊤ a = gs (𝟙 Z) z (V j) (u j) :=
    (gs_res (𝟙 Z) z le_top hj a).symm.trans (congrArg (gs (𝟙 Z) z (V j)) (ha j))
  have k₂ : z ∈ Z.basicOpen (show Γ(Z, ⊤) from a) ↔ IsUnit (gs r z (L.U j) (s.f j)) := by
    refine (isUnit_gs (𝟙 Z) z ⊤ trivial a).symm.trans ?_
    rw [k₁, hu j z hj, Units.isUnit_mul_units, isUnit_pow_iff he]
  refine k₂.trans ⟨fun h => ?_, fun h => ?_⟩
  · exact Opens.mem_iSup.2 ⟨j, (isUnit_gs r z _ hj _).1 h⟩
  · obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show r z ∈ nonzeroLocus s from h)
    have hk' : r z ∈ L.U k := W.basicOpen_le _ hk
    rw [sec_gs s r z hj hk']
    exact (Units.isUnit _).mul ((isUnit_gs r z _ hk' _).2 hk)

theorem isFinite_of_pull_iso_pow :
    ∀ (K : Type) [Field K] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) (H : LB X) (H' : LB X') (n : ℕ) (s : Fin (n + 1) → LB.Sec H') (d : ℕ), H.IsLB → H'.IsLB → IsSeparated f → VeryAmpleBy (φ ≫ f) H' s → 1 ≤ d → LBIso (pw H' d) (H.pull φ) → IsFinite φ := by
  intro K _ X X' f φ H H' n s d hH hH' hf hva hd ⟨α, hα⟩
  have : IsProper (φ ≫ f) := isProper_of_isProjBy K X' _ ⟨H', hH', n, s, hva⟩
  have : IsProper φ := .of_comp _ f
  suffices LocallyQuasiFinite φ from .of_isProper_of_locallyQuasiFinite _
  refine .of_fiberToSpecResidueField _ fun y => ?_
  obtain ⟨hcov, hs⟩ := hva
  have hy : ∀ z, φ (φ.fiberι y z) = y := fun z => (φ.range_fiberι y).le ⟨z, rfl⟩
  have := isAffineHom_fromSpecResidueField X y
  have : IsAffineHom (φ.fiberι y) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0})
      (IsPullback.of_hasPullback φ (X.fromSpecResidueField y)).flip this
  obtain ⟨j₀, hj₀⟩ := Geo.Tor.exists_chart hH y
  have key := fun i => exists_fn H hH H' hH' (s i) φ d (by omega) α hα (φ.fiberι y) j₀ (fun z => by
    rw [hy]; exact hj₀)
  choose a ha using key
  have : IsProper (φ.fiberToSpecResidueField y) :=
    inferInstanceAs (IsProper (pullback.snd φ (X.fromSpecResidueField y)))
  refine locallyQuasiFinite_of_cover (K := X.residueField y) (φ.fiberToSpecResidueField y) a ?_ fun i => ?_
  · simp only [ha]
    rw [← Scheme.Hom.preimage_iSup]
    exact (congrArg (fun V => φ.fiberι y ⁻¹ᵁ V) hcov).trans rfl
  · rw [ha]
    exact (hs i).1.preimage _

end GlobalTheory.PullAmpleFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfUniformisationOverDvr
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem quasiCompact_of_fibres_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {X : Scheme.{0}} (f : X ⟶ Sp V)
    (h₁ : QuasiCompact (pullback.snd f (spMap (IsLocalRing.residue V))))
    (h₂ : QuasiCompact (pullback.snd f (jK V))) : QuasiCompact f := by
  have c₁ : CompactSpace ↥(pullback f (spMap (IsLocalRing.residue V))) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f _)
  have c₂ : CompactSpace ↥(pullback f (jK V)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f _)
  have hu : Set.range (pullback.fst f (spMap (IsLocalRing.residue V))) ∪ Set.range (pullback.fst f (jK V)) =
      Set.univ := by
    rw [Scheme.Pullback.range_fst, Scheme.Pullback.range_fst, Set.eq_univ_iff_forall]
    intro x
    have hx : (Sp V).fromSpecResidueField (f x) (default : PrimeSpectrum _) = f x :=
      Scheme.fromSpecResidueField_apply _ _
    rcases ZJ.field_point_factor_dvr V ((Sp V).residueField (f x)) ((Sp V).fromSpecResidueField (f x)) with
      ⟨r, hr⟩ | ⟨r, hr⟩
    · exact Or.inl ⟨r (default : PrimeSpectrum _), (congrArg (fun g => g (default : PrimeSpectrum _)) hr).symm.trans hx⟩
    · exact Or.inr ⟨r (default : PrimeSpectrum _), (congrArg (fun g => g (default : PrimeSpectrum _)) hr).symm.trans hx⟩
  have : CompactSpace X := ⟨hu ▸ (isCompact_range (pullback.fst f _).continuous).union
    (isCompact_range (pullback.fst f _).continuous)⟩
  exact (quasiCompact_iff_compactSpace f).2 this

theorem isSemiAbelian_of_unifPre_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], UnifPre (maximalIdeal V) D A G → IsSemiAbelian G := by
  intro V _ _ _ D A G _ _ U
  obtain ⟨E, -, -, -, -, hE⟩ := gtCoord_isGt V (maximalIdeal V) D.toPre 0 G ⟨U.gt 0⟩
  have h0 := isSemiAbelian_of_isGt _ E _ hE
  have := U.gen_hom
  have hK : IsSemiAbelian ((Over.pullback (jK V)).obj G) :=
    isSemiAbelian_of_grpIso U.gen (isSemiAbelian_of_isAbelianScheme A.A A.isAb)
  let ρ : V ⧸ (maximalIdeal V) ^ (0 + 1) →+* ResidueField V :=
    Ideal.Quotient.factor (Ideal.pow_le_self (by norm_num))
  have hr : spMap (residue V) = spMap ρ ≫ thick V (maximalIdeal V) 0 := by
    rw [← Spec.map_comp]
    congr 1
  have hk : IsSemiAbelian ((Over.pullback (spMap (residue V))).obj G) := by
    rw [hr]
    exact isSemiAbelian_of_grpIso (pullCompIso (spMap ρ) (thick V (maximalIdeal V) 0) G)
      (IsSemiAbelian.pullback (spMap ρ) _ h0)
  exact ZJ.isSemiAbelian_of_fibres_dvr V G U.smooth U.separated
    (quasiCompact_of_fibres_dvr V G.hom hk.quasiCompact hK.quasiCompact) hk hK

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyQuasiFiniteOfCubicalPowIsoPull
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubicalQuasiFinite

theorem triv_translDiff_of_fixes {S : Scheme.{0}} {B Z : Over S} [GrpObj B] (φ : B ⟶ Z) {M : LB B.left}
    {H : LB Z.left} (hM : M.IsLB) (hH : H.IsLB) (hw : LBIso M (H.pull φ.left)) (x : 𝟙_ (Over S) ⟶ B)
    (hx : ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ) : Triv (translDiff B M x) := by
  obtain ⟨w, hw⟩ := hw
  replace hw := (isGen_iff w).1 hw
  have e : translPt B x ≫ φ = snd _ B ≫ φ := by
    have e₀ : translPt B x = snd _ B ≫ ((toUnit B ≫ x) * 𝟙 B) := by
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
        toUnit_unique (snd _ B ≫ toUnit B) (fst _ B)]
      rfl
    rw [e₀, Category.assoc, hx]
  have e' : (translPt B x).left ≫ φ.left = (snd _ B).left ≫ φ.left := congrArg CommaMorphism.left e
  obtain ⟨c, hc, -⟩ := exists_gen hH
    (φ' := fun k : Fin 2 => (![(translPt B x).left, (snd _ B).left] : Fin 2 → _) k ≫ φ.left) (ε' := ![1, -1])
    (fun U _ f => (Fintype.prod_empty _).trans (by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e', zpow_one, zpow_neg,
        mul_inv_cancel])) (LB.oneGen H (Y := (𝟙_ (Over S) ⊗ B).left))
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)).symm)
  exact exists_down hw hH hM c hc

theorem locallyQuasiFinite_of_pow_iso_pull : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (_ : CubicalStr B L) (r n : ℕ), n.Prime → (n : K) ≠ 0 → ¬ n ∣ r → (∀ x : baseOver _ ⟶ B, x ^ n = 1 → Triv (translDiff B L.L x) → x = 1) → ∀ (Z : Over (Spec (CommRingCat.of K))) [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] (φ : B ⟶ Z) (H : LB Z.left), H.IsLB → LBIso (pw L.L r) (H.pull φ.left) → LocallyQuasiFinite φ.left := by
  intro hcount K _ _ B _ _ hB L c r n hn hnK hnr hK Z _ _ φ H hH hw
  obtain ⟨C, W, hW, hC, hCW⟩ := GlobalTheory.Stabiliser.exists_closed_stabiliser K B hB Z φ
  have hfin : Finite C := by
    refine GlobalTheory.AbelianSubgroupFinite.finite_of_no_torsion hcount K B n hB hn hnK C W hW hCW fun x hx hxn => ?_
    have h₁ : Triv (translDiff B L.L (x ^ r)) :=
      ((GlobalTheory.Square.square_of_cubical _ B L c K (𝟙 _)).2 r x).1
        (triv_translDiff_of_fixes φ (isLB_pw L.isLB r) hH hw x ((hC x).1 hx))
    have h₂ : x ^ r = 1 := hK (x ^ r) (by
      change (x ^ r) ^ n = 1
      rw [← pow_mul, _root_.mul_comm, pow_mul, hxn, one_pow]) h₁
    have h₃ := pow_gcd_eq_one.2 ⟨hxn, h₂⟩
    rwa [(Nat.Prime.coprime_iff_not_dvd hn).2 hnr, pow_one] at h₃
  refine GlobalTheory.FiniteStabiliser.locallyQuasiFinite_of_finite_stabiliser K B hB Z φ ?_
  have e : {x : 𝟙_ _ ⟶ B | ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ} = (C : Set _) := Set.ext fun x => (hC x).symm
  rw [e]
  exact Set.toFinite _

end GlobalTheory.CubicalQuasiFinite
end

