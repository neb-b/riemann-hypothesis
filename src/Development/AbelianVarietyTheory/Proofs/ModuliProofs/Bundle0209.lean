module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0059

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDualIsogeny
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

open GlobalTheory.CechPic

theorem pow_eq_of_map_add {A Q : Type} [AddCommGroup A] [Group Q] (f : A → Q)
    (hf : ∀ a c, f (a + c) = f a * f c) (n : ℕ) (a : A) : f a ^ n = f (n • a) := by
  induction n with
  | zero =>
    have h := hf 0 0
    rw [add_zero] at h
    rw [pow_zero, zero_nsmul, left_eq_mul.1 h]
  | succ n ih => rw [pow_succ, ih, succ_nsmul, hf]

theorem exists_dual_isogeny : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (p : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o o' : Ob D l s) (ψ : o.t.G ⟶ o'.t.G), p.Prime → ¬ p ∣ l.M' → IsIsog o o' p ψ → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ o.t.G), z ≫ ψ = 1 → z ^ p ^ 2 = 1) → ∃ ψ' : o'.t.G ⟶ o.t.G, ψ ≫ ψ' = 𝟙 o.t.G ^ p ^ 2 ∧ ψ' ≫ ψ = 𝟙 o'.t.G ^ p ^ 2 ∧ IsIsog o' o p ψ' := by
  intro E _ _ _ H D l p S _ s o o' ψ hp _ ⟨⟨hψ, hf, he, hs, hact, hiso⟩, hlev⟩ hker
  have hA : IsAbelianScheme o.t.G := ⟨o.t.semi.comm, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩
  have hB : IsAbelianScheme o'.t.G := ⟨o'.t.semi.comm, o'.t.semi.smooth, o'.proper, o'.t.semi.geomConnected⟩
  have hn : 0 < p ^ 2 := pow_pos hp.pos 2
  have hu : IsUnit ((p ^ 2 : ℕ) : Γ(S, ⊤)) := by
    have h0 : IsUnit ((p ^ 2 : ℕ) : Γ(Sp (KA l), ⊤)) := by
      have := ((baseKA l).unit _ hn).map (Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv.hom
      rwa [map_natCast] at this
    have := h0.map s.appTop.hom
    rwa [map_natCast] at this
  obtain ⟨m1, m2, m3, m4⟩ := abelianScheme_id_pow_finite_etale_surjective S o.t.G (p ^ 2) hA hu
  have := hA.proper
  have := hB.proper
  have := hA.smooth
  have := hB.smooth
  obtain ⟨π, hπ, hψπ, -⟩ := _root_.GlobalTheory.HkFactor.exists_unique_factor S o.t.G o'.t.G o.t.G ψ (𝟙 o.t.G ^ p ^ 2) hA hB inferInstance hψ hf he hs m1
    fun k _ _ x z hz => by rw [MonObj.comp_pow, Category.comp_id, hker k x z hz]
  have hepi : Epi ψ.left := Flat.epi_of_flat_of_surjective _
  have canc : ∀ (Y : Over S) (f f' : o'.t.G ⟶ Y), ψ ≫ f = ψ ≫ f' → f = f' := fun Y f f' h =>
    Over.OverMorphism.ext ((cancel_epi ψ.left).1 (congrArg (·.left) h))
  have hπψ : π ≫ ψ = 𝟙 o'.t.G ^ p ^ 2 := canc _ _ _ (by
    rw [← Category.assoc, hψπ, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id])
  have hl : ψ.left ≫ π.left = (𝟙 o.t.G ^ p ^ 2).left := congrArg (·.left) hψπ
  have hw : π.left ≫ o.t.G.hom = o'.t.G.hom := Over.w π
  have hsep : IsSeparated π.left := by
    have : IsSeparated (π.left ≫ o.t.G.hom) := by rw [hw]; infer_instance
    exact IsSeparated.of_comp _ o.t.G.hom
  have hlfp : LocallyOfFinitePresentation π.left := by
    have : LocallyOfFinitePresentation (π.left ≫ o.t.G.hom) := by rw [hw]; infer_instance
    exact TangentCrit.locallyOfFinitePresentation_of_comp _ o.t.G.hom
  obtain ⟨hf', he'⟩ := isFinite_and_etale_of_comp_of_finite_etale_cover _ _ _ ψ.left π.left hf he hs
    (hl ▸ m2) (hl ▸ m3) hsep hlfp
  have hs' : Surjective π.left := by
    have : Surjective (ψ.left ≫ π.left) := hl ▸ m4
    exact Surjective.of_comp ψ.left π.left
  have hact' : ∀ a, o'.t.act.act a ≫ π = π ≫ o.t.act.act a := fun a => canc _ _ _ (by
    have := o.t.act.hom a
    rw [← Category.assoc, ← hact, Category.assoc, hψπ, ← Category.assoc, hψπ, MonObj.pow_comp, MonObj.comp_pow,
      Category.id_comp, Category.comp_id])
  refine ⟨π, hψπ, hπψ, ⟨hπ, hf', he', hs', hact', ?_⟩, fun p' hp' a => ?_⟩
  · have hL := o.t.PP.isLB
    have hM := o'.t.PP.isLB
    have hΘ : ∃ t : LB.Gen (Theta o.t.G o.t.PP.L), t.IsGen := ⟨o.t.cub.t, o.t.cub.isGen⟩
    have hn' : (lbPow o'.t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb hM _ _
    have hψm : pull ψ.left (cls _ hM) = (p ^ 2) • cls _ hL := by
      rw [← cls_lbPow hL (p ^ 2) (LB.isLB_linComb hL _ _)]
      exact ((cls_eq_iff _ (pull_isLB hM _)).2 hiso).symm
    have h₁ : (cubeLB o.t.G ![fst o'.t.G o'.t.G ≫ π, snd o'.t.G o'.t.G ≫ π] o.t.PP.L).IsLB :=
      LB.isLB_linComb hL _ _
    have h₂ : (cubeLB o'.t.G ![fst o'.t.G o'.t.G, snd o'.t.G o'.t.G] (lbPow o'.t.PP.L (p ^ 2))).IsLB :=
      LB.isLB_linComb hn' _ _
    have hN := LB.isLB_div h₁ h₂
    have val : ∀ {T : Over S} (x y : T ⟶ o'.t.G), pull (lift x y).left (cls _ hN) =
        lam (cls _ hL) (x ≫ π) (y ≫ π) - (p ^ 2) • lam (cls _ hM) x y := by
      intro T x y
      rw [cls_div h₁ h₂, cls_cube_two hL, cls_cube_two hn', map_sub, pull_lam, pull_lam, lift_fst,
        lift_snd, lift_fst_assoc, lift_snd_assoc, cls_lbPow hM, lam_nsmul]
    have hN0 : cls _ hN = 0 := by
      refine (cls_eq_zero_iff hN).2 (_root_.GlobalTheory.IsogenyBitriv.triv_of_triv_pull_isogeny S o.t.G o'.t.G ψ o'.t.PP.L _ (p ^ 2) hA hB hM o'.ample hN hψ hf he hs
        hn hu hker ?_ ?_ ?_)
      · refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
        rw [cls_pull hN, val, MonObj.one_comp, lam_one_left, lam_one_left, nsmul_zero, sub_self]
      · refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
        rw [cls_pull hN, val, MonObj.one_comp, lam_one_right, lam_one_right, nsmul_zero, sub_self]
      · refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
        have e : ψ ⊗ₘ ψ = lift (fst _ _ ≫ ψ) (snd _ _ ≫ ψ) := by ext1 <;> simp
        rw [cls_pull hN, e, val, Category.assoc, Category.assoc, hψπ, MonObj.comp_pow, MonObj.comp_pow,
          Category.comp_id, Category.comp_id, lam_pow_left hL hΘ, lam_pow_right hL hΘ, ← lam_pull, hψm,
          lam_nsmul, sub_self]
    have e : cls _ hL = lam (cls _ hL) (𝟙 _) (o.t.act.act H.w0) :=
      ((cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 o.t.prim).trans (cls_cube_two hL _ _ _)
    have e' : cls _ hM = lam (cls _ hM) (𝟙 _) (o'.t.act.act H.w0) :=
      ((cls_eq_iff hM (LB.isLB_linComb hM _ _)).2 o'.t.prim).trans (cls_cube_two hM _ _ _)
    have key := val (𝟙 _) (o'.t.act.act H.w0)
    rw [hN0, map_zero, ← e', hact', Category.id_comp, eq_comm, sub_eq_zero] at key
    rw [← cls_eq_iff hn' (pull_isLB hL _), cls_lbPow hM, cls_pull hL, ← key]
    conv_rhs => rw [e, pull_lam, Category.comp_id]
  · have hM : ∀ a, o.eta (l.M • a) = 1 := fun a => o.eta_ker _ (by
      rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
      exact Submodule.smul_mem_smul (HeckePoint.natCast_M_mem l) Submodule.mem_top)
    have h2 : p ^ 2 * (p' * p') ≡ 1 [MOD l.M'] := by
      have := hp'.mul hp'
      rwa [show p * p' * (p * p') = p ^ 2 * (p' * p') by ring] at this
    rw [← (hlev p' hp' (p' • a)).1, ← (hlev p' hp' (p' • a)).2, Category.assoc, Category.assoc, hψπ,
      MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id, pow_eq_of_map_add _ o.eta_add,
      pow_eq_of_map_add _ o.etaA_add, smul_smul, smul_smul, _root_.mul_assoc,
      HeckePoint.eq_of_modEq _ o.eta_add hM (h2.of_dvd (Nat.dvd_lcm_left _ _)),
      HeckePoint.eq_of_modEq _ o.etaA_add o.etaA_ker (h2.of_dvd (Nat.dvd_lcm_right _ _)), one_nsmul]
    exact ⟨rfl, rfl⟩

end GlobalTheory.HkFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleHeckeKernelLists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkTuple

theorem exists_equiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (g : T.left ⟶ S) (hg : T.hom ≫ f = g) :
    ∃ ρ : (T ⟶ G') ≃* (Over.mk g ⟶ G), ∀ x, (ρ x).left = x.left ≫ φ := by
  subst hg
  exact GlobalTheory.HkSetPull.exists_equiv h T

theorem exists_tuples {S : Scheme.{0}} (G : Over S) [GrpObj G] (N n : ℕ) (hG : IsAbelianScheme G)
    (hn : IsUnit (N : Γ(S, ⊤))) :
    ∃ (Z : Scheme.{0}) (a : Z ⟶ S) (x : Fin n → (Over.mk a ⟶ G)), IsFinite a ∧ Etale a ∧ (∀ j, x j ^ N = 1) ∧
      ∀ (T : Over S) (y : Fin n → (T ⟶ G)), (∀ j, y j ^ N = 1) → ∃! h : T ⟶ Over.mk a, ∀ j, h ≫ x j = y j := by
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion G hn
  have key : ∃ (Z : Over S) (x : Fin n → (Z ⟶ G)), IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ j, x j ^ N = 1) ∧
      ∀ (T : Over S) (y : Fin n → (T ⟶ G)), (∀ j, y j ^ N = 1) → ∃! h : T ⟶ Z, ∀ j, h ≫ x j = y j := by
    refine ⟨Out.powObj (torsion G N) n, fun i => Out.powPr (torsion G N) i ≫ torsion.ι G N,
      LatticeTorsion.prop_powObj @IsFinite _ hfin n, LatticeTorsion.prop_powObj @Etale _ het n, fun i => ?_,
      fun T y' hy' => ?_⟩
    · rw [← MonObj.comp_pow, LatticeTorsion.torsionι_pow_eq_one, MonObj.comp_one]
    · choose y hy hyu using fun i : Fin n => LatticeTorsion.existsUnique_torsion G N (y' i) (hy' i)
      let h : T ⟶ Out.powObj (torsion G N) n := (Out.powIsLimit (torsion G N) n).lift (Fan.mk T y)
      have hh : ∀ i, h ≫ Out.powPr (torsion G N) i = y i := fun i =>
        (Out.powIsLimit (torsion G N) n).fac (Fan.mk T y) ⟨i⟩
      refine ⟨h, fun i => by rw [← hy i, ← hh i, Category.assoc], fun h' hh' => ?_⟩
      refine (Out.powIsLimit (torsion G N) n).hom_ext fun ⟨i⟩ => ?_
      exact (hyu i _ ((Category.assoc _ _ _).trans (hh' i))).trans (hh i).symm
  obtain ⟨Z, x, h⟩ := key
  exact ⟨Z.left, Z.hom, x, h⟩

theorem eq_of_mem_range {S : Scheme.{0}} {G : Over S} (τ : 𝟙_ (Over S) ⟶ G) {k : Type} [Field k] {x : Sp k ⟶ S}
    (z : Over.mk x ⟶ G) (u : Sp k) (hu : z.left u ∈ Set.range τ.left) : z = toUnit _ ≫ τ := by
  have w : τ.left ≫ G.hom = 𝟙 S := Over.w _
  have i₁ : IsImmersion τ.left := by
    have : IsImmersion (τ.left ≫ G.hom) := by rw [w]; exact inferInstanceAs (IsImmersion (𝟙 S))
    exact IsImmersion.of_comp _ G.hom
  have r : Set.range (pullback.fst z.left τ.left) = Set.univ := by
    rw [Scheme.Pullback.range_fst]
    refine Set.eq_univ_of_forall fun v => ?_
    rw [show v = u from Subsingleton.elim (α := PrimeSpectrum k) _ _]
    exact hu
  have i₂ : IsClosedImmersion (pullback.fst z.left τ.left) :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [r]; exact isClosed_univ)
  have i₃ : Surjective (pullback.fst z.left τ.left) := ⟨Set.range_eq_univ.1 r⟩
  have i₄ : IsReduced (Over.mk x).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  have i₅ : IsIso (pullback.fst z.left τ.left) := isIso_of_isClosedImmersion_of_surjective _
  refine Over.OverMorphism.ext ?_
  have tu : (toUnit (Over.mk x)).left = x := by simp
  have wz : z.left ≫ G.hom = x := Over.w _
  rw [Over.comp_left, tu, ← cancel_epi (pullback.fst z.left τ.left)]
  have e : pullback.fst z.left τ.left ≫ z.left ≫ G.hom ≫ τ.left = pullback.fst z.left τ.left ≫ z.left := by
    rw [pullback.condition_assoc, reassoc_of% w, pullback.condition]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ τ.left) (Category.comp_id _))
  rw [← e, reassoc_of% wz]

theorem range_subset_iff {S : Scheme.{0}} {G : Over S} {n : ℕ} (τ : Fin n → (𝟙_ (Over S) ⟶ G)) {k : Type} [Field k]
    {x : Sp k ⟶ S} (z : Over.mk x ⟶ G) :
    Set.range z.left ⊆ (⋃ j, Set.range (τ j).left) ↔ z ∈ Set.range fun j => toUnit (Over.mk x) ≫ τ j := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (h ⟨(default : PrimeSpectrum k), rfl⟩)
    exact ⟨j, (eq_of_mem_range (τ j) z _ hj).symm⟩
  · rintro ⟨j, rfl⟩ _ ⟨u, rfl⟩
    refine Set.mem_iUnion.2 ⟨j, (toUnit (Over.mk x)).left u, ?_⟩
    exact (Scheme.Hom.comp_apply _ _ _).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem listed_iff {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (D : Datum H) (P : Ideal (𝓞 E))
    (p i : ℕ) (m : SABMap t' t f) {n : ℕ} (σ : Fin n → (𝟙_ (Over S) ⟶ t.G)) (τ : Fin n → (𝟙_ (Over S') ⟶ t'.G))
    (e : ∀ j, (τ j).left ≫ m.φ = f ≫ (σ j).left) {k : Type} [Field k] (x : Sp k ⟶ S') :
    ((Function.Injective fun j => x ≫ (τ j).left) ∧ ∃ C : Subgroup (Over.mk x ⟶ t'.G),
      (C : Set _) = Set.range (fun j => toUnit (Over.mk x) ≫ τ j) ∧ t'.HeckeKer (Over.mk x) D P p i C) ↔
    ((Function.Injective fun j => (x ≫ f) ≫ (σ j).left) ∧ ∃ C : Subgroup (Over.mk (x ≫ f) ⟶ t.G),
      (C : Set _) = Set.range (fun j => toUnit (Over.mk (x ≫ f)) ≫ σ j) ∧
        t.HeckeKer (Over.mk (x ≫ f)) D P p i C) := by
  obtain ⟨ρ, e₀⟩ := exists_equiv m.cart (Over.mk x) (x ≫ f) rfl
  have tu : (toUnit (Over.mk x)).left = x := by simp
  have tu' : (toUnit (Over.mk (x ≫ f))).left = x ≫ f := by simp
  have l₁ : ∀ j, (toUnit (Over.mk x) ≫ τ j).left = x ≫ (τ j).left := fun j => by rw [Over.comp_left, tu]
  have l₂ : ∀ j, (toUnit (Over.mk (x ≫ f)) ≫ σ j).left = (x ≫ f) ≫ (σ j).left := fun j => by
    rw [Over.comp_left, tu']
  have e₁ : ∀ j, ρ (toUnit (Over.mk x) ≫ τ j) = toUnit (Over.mk (x ≫ f)) ≫ σ j := fun j =>
    Over.OverMorphism.ext (by
      rw [e₀, l₁, l₂]
      exact (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) (e j)).trans (Category.assoc _ _ _).symm))
  have mem : ∀ u, u ∈ Set.range (fun j => toUnit (Over.mk x) ≫ τ j) ↔
      ρ u ∈ Set.range (fun j => toUnit (Over.mk (x ≫ f)) ≫ σ j) := fun u =>
    exists_congr fun j => by beta_reduce; rw [← e₁]; exact ρ.injective.eq_iff.symm
  have eq : ∀ (u : Over.mk x ⟶ t'.G) (v : Over.mk (x ≫ f) ⟶ t.G), v.left = u.left ≫ m.φ → v = ρ u :=
    fun u v h => Over.OverMorphism.ext (h.trans (e₀ u).symm)
  refine and_congr (forall₂_congr fun a b => imp_congr_left ?_) ⟨?_, ?_⟩
  · beta_reduce
    rw [← l₁, ← l₁, ← l₂, ← l₂]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [← e₁, ← e₁, Over.OverMorphism.ext h]
    · have := Over.OverMorphism.ext h
      rw [← e₁, ← e₁] at this
      rw [ρ.injective this]
  · rintro ⟨C', h₁, h₂⟩
    refine ⟨C'.comap ρ.symm.toMonoidHom, Set.ext fun v => ?_,
      (GlobalTheory.HkSetPull.heckeKer_iff D P p i m (Over.mk x) C' _ fun u v h => ?_).1 h₂⟩
    · obtain ⟨u, rfl⟩ := ρ.surjective v
      rw [← mem, ← h₁]
      show ρ.symm (ρ u) ∈ C' ↔ _
      rw [ρ.symm_apply_apply]
      rfl
    · rw [eq u v h]
      show _ ↔ ρ.symm (ρ u) ∈ C'
      rw [ρ.symm_apply_apply]
  · rintro ⟨C, h₁, h₂⟩
    refine ⟨C.comap ρ.toMonoidHom, Set.ext fun u => ?_,
      (GlobalTheory.HkSetPull.heckeKer_iff D P p i m (Over.mk x) _ C fun u v h => ?_).2 h₂⟩
    · rw [mem, ← h₁]
      rfl
    · rw [eq u v h]
      rfl

theorem range_subset_of_geom {T Z : Scheme.{0}} (h : T ⟶ Z) (V : Set Z)
    (hV : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T), Set.range (x ≫ h) ⊆ V) : Set.range h ⊆ V := by
  rintro _ ⟨y, rfl⟩
  let k := AlgebraicClosure (T.residueField y)
  let z : Sp k ⟶ T := Spec.map (CommRingCat.ofHom (algebraMap (T.residueField y) k)) ≫ T.fromSpecResidueField y
  have hz : ∀ u, z u = y := fun u => Scheme.fromSpecResidueField_apply y _
  exact hV k z ⟨(default : PrimeSpectrum k), (Scheme.Hom.comp_apply _ _ _).trans (congrArg h (hz _))⟩

end GlobalTheory.HkTuple


open GlobalTheory.HkTuple in
theorem GlobalTheory.exists_finiteEtale_heckeLists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s), admitted l 𝔓 p → ∃ (Y : Scheme.{0}) (a : Y ⟶ S) (oY : Ob D l (a ≫ s)) (m : ObjMap oY o a) (σ : Fin n → (𝟙_ (Over Y) ⟶ oY.t.G)) (K : Set oY.t.G.left), IsFinite a ∧ Etale a ∧ Lists (p ^ 2) σ K ∧ HeckeSet D oY.t 𝔓 p i K ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (t : SAB H T) (mu : SABMap t o.t f) (τ : Fin n → (𝟙_ (Over T) ⟶ t.G)) (K' : Set t.G.left), Lists (p ^ 2) τ K' → HeckeSet D t 𝔓 p i K' → ∃! h : T ⟶ Y, h ≫ a = f ∧ ∀ j, h ≫ (σ j).left ≫ m.toSABMap.φ = (τ j).left ≫ mu.φ := by
  intro E _ _ _ H D l P p i n S s o adm
  have hu : IsUnit ((p ^ 2 : ℕ) : Γ(S, ⊤)) := by
    have := ((baseKA l).unit (p ^ 2) (pow_pos adm.2.2.1.pos 2)).map
      ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ s.appTop).hom
    rwa [map_natCast] at this
  have specMap_id₂ : spMap (RingHom.id (KA l)) = 𝟙 _ := Spec.map_id _
  obtain ⟨Z, b, x, hf, he, hx, huniv⟩ := GlobalTheory.HkTuple.exists_tuples o.t.G (p ^ 2) n (GlobalTheory.ObjDim.isAbelianScheme o) hu
  obtain ⟨oZ, ⟨mZ⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) S Z s (b ≫ s) b rfl rfl
    (by rw [specMap_id₂, Category.comp_id]) o
  obtain ⟨ρ, e₀⟩ := GlobalTheory.HkTuple.exists_equiv mZ.cart (𝟙_ (Over Z)) b (Category.id_comp b)
  let σZ : Fin n → (𝟙_ (Over Z) ⟶ oZ.t.G) := fun j => ρ.symm (x j)
  have eZ : ∀ j, (σZ j).left ≫ mZ.toSABMap.φ = (x j).left := fun j => by
    rw [← e₀, ρ.apply_symm_apply]
  have pZ : ∀ j, σZ j ^ p ^ 2 = 1 := fun j => by rw [← map_pow, hx, map_one]
  obtain ⟨V, hc, hV⟩ := _root_.GlobalTheory.exists_clopen_heckeKer_iff E H D l P p i n Z (b ≫ s) oZ σZ adm pZ
  obtain ⟨oY, ⟨mY⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) Z V (b ≫ s) ((V.ι ≫ b) ≫ s) V.ι
    rfl rfl (by rw [specMap_id₂, Category.comp_id, Category.assoc]) oZ
  obtain ⟨m, hm⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o oZ oY).2 b V.ι mZ).1 mY
  obtain ⟨ρ', e₀'⟩ := GlobalTheory.HkTuple.exists_equiv mY.cart (𝟙_ (Over V.toScheme)) V.ι (Category.id_comp _)
  let σ : Fin n → (𝟙_ (Over V.toScheme) ⟶ oY.t.G) := fun j => ρ'.symm (toUnit _ ≫ σZ j)
  have tu : (toUnit (Over.mk V.ι)).left = V.ι := by simp
  have eY : ∀ j, (σ j).left ≫ mY.toSABMap.φ = V.ι ≫ (σZ j).left := fun j => by
    rw [← e₀', ρ'.apply_symm_apply, Over.comp_left, tu]
  have eσ : ∀ j, (σ j).left ≫ m.toSABMap.φ = V.ι ≫ (x j).left := fun j => by
    rw [hm, ← eZ]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ mZ.toSABMap.φ) (eY j)).trans (Category.assoc _ _ _))
  have hY := fun (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ V.toScheme) =>
    (GlobalTheory.HkTuple.listed_iff D P p i mY.toSABMap σZ σ eY y).2 ((hV k (y ≫ V.ι)).1 (by
      rintro _ ⟨u, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact (y u).2))
  have ci : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion _ (by rwa [Scheme.Opens.range_ι])
  refine ⟨V, V.ι ≫ b, oY, m, σ, ⋃ j, Set.range (σ j).left, inferInstance, inferInstance,
    ⟨fun j => ?_, rfl, fun k _ _ y => (hY k y).1⟩, fun k _ _ y => ?_, ?_⟩
  · rw [← map_pow, ← MonObj.comp_pow, pZ, MonObj.comp_one, map_one]
  · obtain ⟨C, h₁, h₂⟩ := (hY k y).2
    exact ⟨C, fun z => by rw [GlobalTheory.HkTuple.range_subset_iff, ← h₁]; rfl, h₂⟩
  · rintro T f t mu τ K' ⟨hτ, rfl, hinj⟩ hK
    obtain ⟨ρ₂, e₂⟩ := GlobalTheory.HkTuple.exists_equiv mu.cart (𝟙_ (Over T)) f (Category.id_comp _)
    obtain ⟨h₀, hh₀, hh₀u⟩ := huniv (Over.mk f) (fun j => ρ₂ (τ j)) (fun j => by rw [← map_pow, hτ, map_one])
    have e₃ : ∀ j, h₀.left ≫ (x j).left = (τ j).left ≫ mu.φ := fun j => by
      rw [← e₂, ← hh₀, Over.comp_left]
    have uq : ∀ g : T ⟶ Z, g ≫ b = f → (∀ j, g ≫ (x j).left = (τ j).left ≫ mu.φ) → g = h₀.left := fun g w hg =>
      congrArg (·.left) (hh₀u (Over.homMk g w) fun j => Over.OverMorphism.ext ((hg j).trans (e₂ _).symm))
    obtain ⟨g, w, e₄, uq'⟩ : ∃ g : T ⟶ Z, g ≫ b = f ∧ (∀ j, g ≫ (x j).left = (τ j).left ≫ mu.φ) ∧
        ∀ g' : T ⟶ Z, g' ≫ b = f → (∀ j, g' ≫ (x j).left = (τ j).left ≫ mu.φ) → g' = g :=
      ⟨h₀.left, Over.w h₀, e₃, uq⟩
    clear uq e₃ hh₀u hh₀ h₀ e₂ ρ₂
    subst w
    obtain ⟨mu', hmu⟩ := GlobalTheory.ObjMaps.exists_sab_cancel mZ.toSABMap mu
    have e₅ : ∀ j, (τ j).left ≫ mu'.φ = g ≫ (σZ j).left := fun j => by
      have w₁ : (τ j).left ≫ t.G.hom = 𝟙 T := Over.w _
      have w₂ : (σZ j).left ≫ oZ.t.G.hom = 𝟙 Z := Over.w _
      refine mZ.cart.1.hom_ext ?_ ?_
      · exact (Category.assoc _ _ _).trans ((congrArg ((τ j).left ≫ ·) hmu.symm).trans ((e₄ j).symm.trans
          ((congrArg (g ≫ ·) (eZ j).symm).trans (Category.assoc _ _ _).symm)))
      · exact (Category.assoc _ _ _).trans ((congrArg ((τ j).left ≫ ·) mu'.cart.1.w).trans
          ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g) w₁).trans ((Category.id_comp g).trans
          ((Category.comp_id g).symm.trans ((congrArg (g ≫ ·) w₂.symm).trans (Category.assoc _ _ _).symm))))))
    have hr : Set.range g ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      refine GlobalTheory.HkTuple.range_subset_of_geom g _ fun k _ _ y => (hV k (y ≫ g)).2
        ((GlobalTheory.HkTuple.listed_iff D P p i mu' σZ τ e₅ y).1 ⟨hinj k y, ?_⟩)
      obtain ⟨C, h₁, h₂⟩ := hK k y
      exact ⟨C, Set.ext fun z => (h₁ z).trans (GlobalTheory.HkTuple.range_subset_iff τ z), h₂⟩
    refine ⟨IsOpenImmersion.lift V.ι g hr, ⟨by rw [IsOpenImmersion.lift_fac_assoc], fun j => ?_⟩, ?_⟩
    · exact (congrArg (IsOpenImmersion.lift V.ι g hr ≫ ·) (eσ j)).trans
        ((IsOpenImmersion.lift_fac_assoc _ _ _ _).trans (e₄ j))
    · rintro h ⟨w, hh⟩
      rw [← cancel_mono V.ι, IsOpenImmersion.lift_fac]
      exact uq' _ ((Category.assoc _ _ _).trans w) fun j =>
        (Category.assoc _ _ _).trans ((congrArg (h ≫ ·) (eσ j).symm).trans (hh j))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenericObjectMinimalPrimeModuliChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.GenericObject

theorem isThetaPt_unit_mul {S : Scheme.{0}} (P : Out.PolAV S) (k : ℕ) {T : Over S} {I : Type} (x : I → (T ⟶ P.A))
    (v v' : I → Γ(T.left, ⊤)) (c : Γ(T.left, ⊤)) (hc : IsUnit c) (hv : ∀ i, v' i = c * v i)
    (h : Out.IsThetaPt P k x v) : Out.IsThetaPt P k x v' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hp, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h3 p
  have hc1 : IsUnit (show Γ((Out.overRes V).left, ⊤) from V.ι.appTop.hom c) := hc.map V.ι.appTop.hom
  obtain ⟨c', hc'⟩ := hc1
  refine ⟨V, hp, th, s1, α, τ, U, s2, w, c' * u, a1, a2, a3, a4, a5, a6, a7, fun i => ?_⟩
  have e1 : (show Γ((Out.overRes V).left, ⊤) from V.ι.appTop.hom (v' i)) =
      (show Γ((Out.overRes V).left, ⊤) from V.ι.appTop.hom c) * (show Γ((Out.overRes V).left, ⊤) from V.ι.appTop.hom (v i)) := by
    rw [hv i]
    exact map_mul V.ι.appTop.hom c (v i)
  have e2 : (show Γ((Out.overRes V).left, ⊤) from V.ι.appTop.hom (v i)) = u * w i := a8 i
  rw [← hc', e2, ← _root_.mul_assoc] at e1
  exact e1

theorem hasTh_unit_mul {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {S : Scheme.{0}} {s : S ⟶ Sp o}
    (t : TObj g (N' ^ 2) J b s) {R : Type} [CommRing R] (x : Sp R ⟶ S) (v v' : Ix g (N' ^ 2) → R) (c : R) (hc : IsUnit c)
    (hv : ∀ a, v' a = c * v a) (h : t.HasTh x v) : t.HasTh x v' := by
  refine isThetaPt_unit_mul _ _ _ _ _ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) (hc.map _) (fun a => ?_) h
  rw [hv a]
  exact map_mul (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c (v a)

theorem countable_of_finiteType (o : Type) [CommRing o] (h : Algebra.FiniteType ℤ o) : Countable o := by
  obtain ⟨m, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  have : Countable (MvPolynomial (Fin m) ℤ) :=
    (MvPolynomial.basisMonomials (Fin m) ℤ).repr.injective.countable
  exact hf.countable

theorem exists_generic_object : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (Y : MMPre n (n ^ j) (thIdeal em C)) (R : Type) [CommRing R] (β : o →+* R) (x : Sp R ⟶ Y.MM) (v : Ix g ((n ^ j) ^ 2) → R), IsOpenImmersion x → x ≫ Y.s = spMap β → SecCoord Y.de Y.th x v → ∀ q ∈ minimalPrimes R, ∃ (K : Type) (_ : Field K) (y : R →+* K) (e : K →+* ℂ) (t : TObj g ((n ^ j) ^ 2) J b (spMap y ≫ spMap β)) (tc : TObj g ((n ^ j) ^ 2) J b (spMap em)), RingHom.ker y = q ∧ e.comp (y.comp β) = em ∧ C tc ∧ TMap tc t (spMap e) ∧ t.Shape Mat κ ∧ t.Prim w w' ∧ t.HasTh (𝟙 _) (fun a => y (v a)) := by
  intro L1 L2 g J _ Mat κ n w w' hn hodd
  obtain ⟨j₀, hj₀⟩ := _root_.GlobalTheory.ZM.descend_to_theta_field L1 L2 g J Mat κ n w w' hn hodd
  refine ⟨max j₀ 1, fun j hj o _ b em C d har hC Y R _ β x v hx hxs hv q hq => ?_⟩
  have hj0 : j ≥ j₀ := le_trans (le_max_left _ _) hj
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hn3 : 3 ≤ n := by
    have h2 := hn.two_le
    obtain ⟨m, hm⟩ := hodd
    omega
  have hN3 : 3 ≤ n ^ j := le_trans hn3 (Nat.le_self_pow (by omega) n)
  have hNodd : Odd (n ^ j) := hodd.pow
  haveI hqp : q.IsPrime := hq.1.1
  let K := FractionRing (R ⧸ q)
  let y : R →+* K := (algebraMap (R ⧸ q) K).comp (Ideal.Quotient.mk q)
  have hy0 : ∀ r, y r = 0 ↔ r ∈ q := fun r => by
    simp only [y, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ q) K), Ideal.Quotient.eq_zero_iff_mem]
  have hker : RingHom.ker y = q := Ideal.ext fun r => by rw [RingHom.mem_ker, hy0]
  have hfrac : ∀ k : K, ∃ r r' : R, y r' ≠ 0 ∧ k * y r' = y r := by
    intro k
    obtain ⟨a, a', ha', rfl⟩ := IsFractionRing.div_surjective (A := R ⧸ q) k
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective a'
    have h0 : algebraMap (R ⧸ q) K (Ideal.Quotient.mk q r') ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := K) ha'
    exact ⟨r, r', h0, div_mul_cancel₀ _ h0⟩
  obtain ⟨c₀, hc₀⟩ := (Y.loc R β x v hxs hv).2 q hqp 0
  set a₀ := (0 : Ix g ((n ^ j) ^ 2)) + (n ^ j / n) • c₀ with ha₀
  have hva : y (v a₀) ≠ 0 := fun h => hc₀ ((hy0 _).1 h)
  obtain ⟨hcl, hmin⟩ := GlobalTheory.CoordChart.residue_generic o g n (n ^ j) (thIdeal em C) Y R β x v K y a₀ (by omega) hx hxs hv hfrac hva
  have hmin' := hmin (by rw [hker]; exact hq)
  obtain ⟨-, hhom, -⟩ := _root_.GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree o g (n ^ j) J b em C har.2.2
  have hu : (fun a => y (v a) / y (v a₀)) a₀ = 1 := div_self hva
  have hP := GlobalTheory.ker_cone_mem_minimalPrimes o _ K (thIdeal em C) (y.comp β) (fun a => y (v a) / y (v a₀)) a₀ hhom hu hmin'
  obtain ⟨tc, wv, htc, hth, hkw⟩ := GlobalTheory.ZM.exists_object_at_minimalPrime o g (n ^ j) J b em C Mat κ w w' d L1 L2 hN3 hNodd
    (countable_of_finiteType o har.2.1) hC _ hP
  obtain ⟨e, c, hc, he, hec⟩ := _root_.GlobalTheory.exists_embedding_of_homogeneous_ker_eq o K _ (y.comp β) em (fun a => y (v a) / y (v a₀)) wv a₀
    (div_ne_zero hva hva) (by simpa only [div_self hva, div_one] using hcl) hkw.symm
  have heva : e (y (v a₀)) ≠ 0 := (map_ne_zero e).2 hva
  have hth' : tc.HasTh (𝟙 _) (fun a => e (y (v a))) := by
    refine hasTh_unit_mul tc _ wv _ (e (y (v a₀)) * c) (IsUnit.mk0 _ (mul_ne_zero heva hc)) (fun a => ?_) hth
    have := hec a
    simp only [map_div₀] at this
    rw [_root_.mul_assoc, ← this]
    field_simp
  have hs : spMap em = spMap e ≫ spMap (y.comp β) := by
    rw [← he]
    exact Spec.map_comp (CommRingCat.ofHom (y.comp β)) (CommRingCat.ofHom e)
  have hs' : spMap (y.comp β) = spMap y ≫ spMap β :=
    Spec.map_comp (CommRingCat.ofHom β) (CommRingCat.ofHom y)
  have key := hj₀ j hj0 o b K ℂ (y.comp β) e (spMap em) tc (fun a => y (v a)) hs (hC.shape tc htc).1 (hC.shape tc htc).2 hth'
  rw [hs'] at key
  obtain ⟨t, h1, h2, h3, h4⟩ := key
  exact ⟨K, inferInstance, y, e, t, tc, hker, he, htc, h1, h2, h3, h4⟩

end GlobalTheory.GenericObject
end
end

