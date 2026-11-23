module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0015
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0145

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.CommonZeroEvaluation.CombComb
section
noncomputable section

namespace ModelDimension.Near

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open scoped CategoryTheory.Obj

variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

def GT (G : Over X) [GrpObj G] (x : Sp R ⟶ X) (w : Sp (DualNumber R) ⟶ G.left) : Prop :=
  w ≫ G.hom = spMap (algebraMap R (DualNumber R)) ≫ x ∧
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ w = (1 : Over.mk x ⟶ G).left

def GC (G : Over X) [GrpObj G] (x : Sp R ⟶ X) {m : ℕ} (v : Fin m → (Sp (DualNumber R) ⟶ G.left)) (cf : Fin m → R)
    (w : Sp (DualNumber R) ⟶ G.left) : Prop :=
  ∃ u : Fin m → (Over.mk (spMap (algebraMap R (DualNumber R)) ≫ x) ⟶ G),
    (∀ i, (u i).left = spMap (epsScaleR (cf i)) ≫ v i) ∧ (List.ofFn u).prod.left = w

variable {G : Over X} [GrpObj G] {G' : Over X'} [GrpObj G'] {f : X' ⟶ X} {φ : G'.left ⟶ G.left}

theorem one_push (h : IsGrpPullback G' G f φ) {S : Scheme.{0}} (x : S ⟶ X') :
    (1 : Over.mk x ⟶ G').left ≫ φ = (1 : Over.mk (x ≫ f) ⟶ G).left := by
  have e := GlobalTheory.LieCombBaseChange.prod_left_comp h (T := Over.mk (x ≫ f)) (T' := Over.mk x) (𝟙 S)
    (Category.id_comp _) (n := 0) (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
  simp only [List.ofFn_zero, List.prod_nil] at e
  exact e.trans (Category.id_comp _)

theorem gt_push (h : IsGrpPullback G' G f φ) {x : Sp R ⟶ X'} {w : Sp (DualNumber R) ⟶ G'.left} (hw : GT G' x w) :
    GT G (x ≫ f) (w ≫ φ) :=
  ⟨by rw [Category.assoc, h.1.w, ← Category.assoc, hw.1, Category.assoc],
    by rw [← Category.assoc, hw.2, one_push h]⟩

theorem alg_fst : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
  rw [← spMap_comp]
  have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    ext r
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [this]
  exact Spec.map_id _

theorem gt_pull (h : IsGrpPullback G' G f φ) {x : Sp R ⟶ X'} {w : Sp (DualNumber R) ⟶ G'.left}
    (h1 : w ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ x) (hw : GT G (x ≫ f) (w ≫ φ)) : GT G' x w := by
  refine ⟨h1, h.1.hom_ext ?_ ?_⟩
  · rw [Category.assoc, hw.2, one_push h]
  · rw [Category.assoc, h1, ← Category.assoc, alg_fst, Category.id_comp]
    exact (Over.w (1 : Over.mk x ⟶ G')).symm

theorem gt_bc (ψ : R →+* R') {x : Sp R ⟶ X} {w : Sp (DualNumber R) ⟶ G.left} (hw : GT G x w) :
    GT G (spMap ψ ≫ x) (spMap (dualMapR ψ) ≫ w) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, hw.1, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ x) (GlobalTheory.LieCombBaseChange.dualMap_over ψ)
  · have e : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (dualMapR ψ) =
        spMap ψ ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
      rw [← spMap_comp, ← spMap_comp]
      congr 1
      refine RingHom.ext fun r => ?_
      simp [dualMapR]
    rw [← Category.assoc, e, Category.assoc, hw.2]
    let D : Over.mk (spMap ψ ≫ x) ⟶ Over.mk x := Over.homMk (spMap ψ) rfl
    exact congrArg CommaMorphism.left (MonObj.comp_one (M := G) D)

theorem gc_push (h : IsGrpPullback G' G f φ) {x : Sp R ⟶ X'} {m : ℕ} {v : Fin m → (Sp (DualNumber R) ⟶ G'.left)}
    {cf : Fin m → R} {w : Sp (DualNumber R) ⟶ G'.left} (hw : GC G' x v cf w) :
    GC G (x ≫ f) (fun i => v i ≫ φ) cf (w ≫ φ) := by
  obtain ⟨u, hu, rfl⟩ := hw
  let u' : Fin m → (Over.mk (spMap (algebraMap R (DualNumber R)) ≫ x ≫ f) ⟶ G) := fun i =>
    Over.homMk ((u i).left ≫ φ) (by
      have e : (u i).left ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ x := Over.w (u i)
      show ((u i).left ≫ φ) ≫ G.hom = spMap (algebraMap R (DualNumber R)) ≫ x ≫ f
      rw [Category.assoc, h.1.w, ← Category.assoc, e, Category.assoc])
  refine ⟨u', fun i => ?_, ?_⟩
  · show (u i).left ≫ φ = _
    rw [hu, Category.assoc]
  · have e := GlobalTheory.LieCombBaseChange.prod_left_comp h (𝟙 (Sp (DualNumber R)))
      ((Category.id_comp _).trans (Category.assoc _ _ _).symm) u' u (fun i => (Category.id_comp _).symm)
    exact (e.trans (Category.id_comp _)).symm

theorem gc_pull (h : IsGrpPullback G' G f φ) {x : Sp R ⟶ X'} {m : ℕ} {v : Fin m → (Sp (DualNumber R) ⟶ G'.left)}
    {cf : Fin m → R} {w : Sp (DualNumber R) ⟶ G'.left}
    (hv : ∀ i, v i ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ x)
    (h1 : w ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ x)
    (hw : GC G (x ≫ f) (fun i => v i ≫ φ) cf (w ≫ φ)) : GC G' x v cf w := by
  obtain ⟨u, hu, hw⟩ := hw
  let u' : Fin m → (Over.mk (spMap (algebraMap R (DualNumber R)) ≫ x) ⟶ G') := fun i =>
    Over.homMk (spMap (epsScaleR (cf i)) ≫ v i) (by
      show (spMap (epsScaleR (cf i)) ≫ v i) ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ x
      rw [Category.assoc, hv, ← Category.assoc]
      exact congrArg (· ≫ x) (GlobalTheory.LieCombBaseChange.epsScale_over (cf i)))
  refine ⟨u', fun i => rfl, h.1.hom_ext ?_ ?_⟩
  · have e := GlobalTheory.LieCombBaseChange.prod_left_comp h (𝟙 (Sp (DualNumber R)))
      ((Category.id_comp _).trans (Category.assoc _ _ _).symm) u u' (fun i =>
        (Category.assoc _ _ _).trans ((hu i).symm.trans (Category.id_comp _).symm))
    exact e.trans ((Category.id_comp _).trans hw)
  · rw [h1]
    exact Over.w _

theorem gc_bc (ψ : R →+* R') {x : Sp R ⟶ X} {m : ℕ} {v : Fin m → (Sp (DualNumber R) ⟶ G.left)}
    {cf : Fin m → R} {w : Sp (DualNumber R) ⟶ G.left} (hw : GC G x v cf w) :
    GC G (spMap ψ ≫ x) (fun i => spMap (dualMapR ψ) ≫ v i) (fun i => ψ (cf i)) (spMap (dualMapR ψ) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := hw
  let D : Over.mk (spMap (algebraMap R' (DualNumber R')) ≫ spMap ψ ≫ x) ⟶
      Over.mk (spMap (algebraMap R (DualNumber R)) ≫ x) := Over.homMk (spMap (dualMapR ψ)) (by
    show spMap (dualMapR ψ) ≫ spMap (algebraMap R (DualNumber R)) ≫ x = _ ≫ spMap ψ ≫ x
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ x) (GlobalTheory.LieCombBaseChange.dualMap_over ψ))
  refine ⟨fun i => D ≫ u i, fun i => ?_, ?_⟩
  · show spMap (dualMapR ψ) ≫ (u i).left = _
    rw [hu, ← Category.assoc, GlobalTheory.LieCombBaseChange.dualMap_epsScale, Category.assoc]
  · exact (congrArg (fun q => q.left) ((map_list_prod (preHom D) (List.ofFn u)).trans
      (by rw [List.map_ofFn]))).symm

section Ring

open GlobalTheory.Reg.VecEig GlobalTheory.GrpTangent

variable {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A]

theorem comb_comb {n r : ℕ} {v : Fin n → (epsR R ⟶ A)} (hv : ∀ i, IsTangent (v i)) (u : Matrix (Fin n) (Fin r) R)
    (a : Fin r → R) : comb (fun i => comb v fun j => u j i) a = comb v (u.mulVec a) := by
  rw [comb]
  simp only [epsScale_comb]
  simp only [comb, Matrix.mulVec, dotProduct, epsScale_sum_comp (hv _)]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, mul_comm]

theorem exists_prim [IsDomain R] {n r : ℕ} {v : Fin n → (epsR R ⟶ A)} (hv : IsLieBasis v) {I : Type}
    (g : I → (A ⟶ A)) (hg : ∀ i, IsMonHom (g i)) (z : I → R) (ub : Fin r → (epsR R ⟶ A)) (ht : ∀ i, IsTangent (ub i))
    (he : ∀ i k, (ub i ≫ g k).left = spMap (epsScaleR (z k)) ≫ (ub i).left)
    (hb : ∀ w : epsR R ⟶ A, IsTangent w → (∀ k, (w ≫ g k).left = spMap (epsScaleR (z k)) ≫ w.left) →
      ∃! a : Fin r → R, IsLieComb a ub w) :
    ∃ u : Matrix (Fin n) (Fin r) R, (∀ i, IsLieComb (fun j => u j i) v (ub i)) ∧
      ∀ (p : R) (a : Fin r → R) (cv : Fin n → R), p ≠ 0 → u.mulVec a = p • cv → ∃ a', a = p • a' := by
  choose cu hcu using fun i => (hv.2 _ (ht i)).exists
  let u : Matrix (Fin n) (Fin r) R := Matrix.of fun j i => cu i j
  have hub : ub = fun i => comb v fun j => u j i := funext fun i => (isLieComb_iff_comb _ _ _).1 (hcu i)
  refine ⟨u, hcu, fun p a cv hp hcv => ?_⟩
  choose ρ hρ using fun k j => (hv.2 _ (haveI := hg k; isTangent_comp (hv.1 j) (g k))).exists
  have eig : ∀ k (x : Fin n → R), ((comb v x ≫ g k).left = spMap (epsScaleR (z k)) ≫ (comb v x).left) ↔
      (Matrix.of fun i j => ρ k j i).mulVec x = z k • x := by
    intro k x
    haveI := hg k
    rw [← (comb_injective hv).eq_iff, ← epsScale_comb,
      ← comb_comp hv.1 (g k) (Matrix.of fun i j => ρ k j i) (fun j => (isLieComb_iff_comb _ _ _).1 (hρ k j)) x]
    exact ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg CommaMorphism.left h⟩
  have eigu : ∀ k (b : Fin r → R), (Matrix.of fun i j => ρ k j i).mulVec (u.mulVec b) = z k • u.mulVec b := by
    intro k b
    have e : u.mulVec b = ∑ i, b i • fun j => u j i := by
      funext j
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, _root_.mul_comm]
    rw [e, Matrix.mulVec_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := he i k
    rw [congrFun hub i] at h1
    rw [Matrix.mulVec_smul, (eig k _).1 h1, smul_comm]
  have key : ∀ x : Fin n → R, (∀ k, (Matrix.of fun i j => ρ k j i).mulVec x = z k • x) →
      ∃! b : Fin r → R, u.mulVec b = x := by
    intro x hx
    have h1 := hb (comb v x) (isTangent_comb hv.1 x) fun k => (eig k x).2 (hx k)
    refine (existsUnique_congr fun b => ?_).1 h1
    rw [isLieComb_iff_comb, hub, comb_comb hv.1, (comb_injective hv).eq_iff, eq_comm]
  obtain ⟨a', ha', -⟩ := key cv fun k => by
    have h1 := eigu k a
    rw [hcv, Matrix.mulVec_smul, smul_comm] at h1
    exact smul_right_injective _ hp h1
  refine ⟨a', (key _ fun k => eigu k a).unique rfl ?_⟩
  rw [Matrix.mulVec_smul, ha', hcv]

end Ring

section Coord

variable [IsCommMonObj G] {x : Sp R ⟶ X} {n : ℕ} {V : Fin n → (Sp (DualNumber R) ⟶ G.left)}

def IsBas (G : Over X) [GrpObj G] (x : Sp R ⟶ X) {n : ℕ} (V : Fin n → (Sp (DualNumber R) ⟶ G.left)) : Prop :=
  ∃ (A : Over (Sp R)) (_ : GrpObj A) (_ : IsCommMonObj A) (φ : A.left ⟶ G.left) (_ : IsGrpPullback A G x φ)
    (v : Fin n → (epsR R ⟶ A)), (∀ j, (v j).left ≫ φ = V j) ∧ IsLieBasis v

omit [IsCommMonObj G]

theorem gc_iff {A : Over (Sp R)} [GrpObj A] {φ : A.left ⟶ G.left} (h : IsGrpPullback A G x φ) {m : ℕ} (c : Fin m → R)
    (v : Fin m → (epsR R ⟶ A)) (w : epsR R ⟶ A) :
    IsLieComb c v w ↔ GC G x (fun i => (v i).left ≫ φ) c (w.left ≫ φ) :=
  ReciprocityTheory.ChartRestriction.G.Chart.comb_push h c v w

theorem exists_lift {A : Over (Sp R)} [GrpObj A] {φ : A.left ⟶ G.left} (h : IsGrpPullback A G x φ)
    {w : Sp (DualNumber R) ⟶ G.left} (hw : w ≫ G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) :
    ∃ w' : epsR R ⟶ A, w'.left ≫ φ = w :=
  ⟨Over.homMk (h.1.lift w (spMap (algebraMap R (DualNumber R))) hw) (h.1.lift_snd _ _ _), h.1.lift_fst _ _ _⟩

theorem GC.over {m : ℕ} {v : Fin m → (Sp (DualNumber R) ⟶ G.left)} {cf : Fin m → R}
    {w : Sp (DualNumber R) ⟶ G.left} (h : GC G x v cf w) :
    w ≫ G.hom = spMap (algebraMap R (DualNumber R)) ≫ x := by
  obtain ⟨u, -, rfl⟩ := h
  exact Over.w _

theorem IsBas.exists (hV : IsBas G x V) {w : Sp (DualNumber R) ⟶ G.left} (hw : GT G x w) : ∃ cv, GC G x V cv w := by
  obtain ⟨A, _, _, φ, h, v, hv, hb⟩ := hV
  obtain rfl : (fun j => (v j).left ≫ φ) = V := funext hv
  obtain ⟨w', rfl⟩ := exists_lift h hw.1
  obtain ⟨cv, hcv⟩ := (hb.2 w' ((ReciprocityTheory.ChartRestriction.G.Chart.tan_push h w').2 hw.2)).exists
  exact ⟨cv, (gc_iff h _ _ _).1 hcv⟩

theorem IsBas.unique (hV : IsBas G x V) {w : Sp (DualNumber R) ⟶ G.left} {a b : Fin n → R} (ha : GC G x V a w)
    (hb : GC G x V b w) : a = b := by
  obtain ⟨A, _, _, φ, h, v, hv, hB⟩ := hV
  obtain rfl : (fun j => (v j).left ≫ φ) = V := funext hv
  obtain ⟨w', rfl⟩ := exists_lift h ha.over
  exact GlobalTheory.Reg.VecEig.comb_injective hB
    (((GlobalTheory.Reg.VecEig.isLieComb_iff_comb _ _ _).1 ((gc_iff h _ _ _).2 ha)).symm.trans
      ((GlobalTheory.Reg.VecEig.isLieComb_iff_comb _ _ _).1 ((gc_iff h _ _ _).2 hb)))

theorem IsBas.comb (hV : IsBas G x V) {r : ℕ} {w : Fin r → (Sp (DualNumber R) ⟶ G.left)}
    {u : Matrix (Fin n) (Fin r) R} (hu : ∀ i, GC G x V (fun j => u j i) (w i)) {a : Fin r → R}
    {w' : Sp (DualNumber R) ⟶ G.left} (ha : GC G x w a w') : GC G x V (u.mulVec a) w' := by
  obtain ⟨A, _, _, φ, h, v, hv, hB⟩ := hV
  obtain rfl : (fun j => (v j).left ≫ φ) = V := funext hv
  choose w₁ hw₁ using fun i => exists_lift h (hu i).over
  obtain rfl : (fun j => (w₁ j).left ≫ φ) = w := funext hw₁
  obtain ⟨w₂, rfl⟩ := exists_lift h ha.over
  have e1 : w₁ = fun i => GlobalTheory.Reg.VecEig.comb v fun j => u j i :=
    funext fun i => (GlobalTheory.Reg.VecEig.isLieComb_iff_comb _ _ _).1 ((gc_iff h _ _ _).2 (hu i))
  have e2 := (GlobalTheory.Reg.VecEig.isLieComb_iff_comb _ _ _).1 ((gc_iff h _ _ _).2 ha)
  rw [e1, comb_comb hB.1] at e2
  exact (gc_iff h _ _ _).1 ((GlobalTheory.Reg.VecEig.isLieComb_iff_comb _ _ _).2 e2)

end Coord

end ModelDimension.Near
end
end

-- bundled from Development.WeilBound.CoreStatements.CommonZeroEvaluation.ExistsLocalChartCentre
section
open AlgebraicGeometry CategoryTheory
open GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace ModelDimension

theorem inv_mem_range_of_local {S Ω : Type} [CommRing S] [Field Ω] (A : Subring Ω) (ψ : S →+* A)
    (hψ : IsLocalHom ψ) (g : S →+* Ω) (hg : g = (algebraMap A Ω).comp ψ) :
    ∀ a ∈ g.range, a ≠ 0 → a⁻¹ ∈ A → a⁻¹ ∈ g.range := by
  rintro _ ⟨s, rfl⟩ h0 hi
  have hu : IsUnit (ψ s) := by
    refine IsUnit.of_mul_eq_one (⟨_, hi⟩ : A) (Subtype.ext ?_)
    have h1 := mul_inv_cancel₀ h0
    subst hg
    exact h1
  obtain ⟨s', hs'⟩ := (IsUnit.of_map ψ s hu).exists_right_inv
  refine ⟨s', ?_⟩
  have h2 := congrArg g hs'
  rw [map_mul, map_one] at h2
  exact eq_inv_of_mul_eq_one_right h2

theorem exists_local_chart_centre : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → ∀ (A : Subring Ω) [IsLocalRing A] (c : κ), x c ≠ 0 → (∀ c', x c' / x c ∈ A) → ∃ (zq : Spec (CommRingCat.of A) ⟶ X) (hc : genPt ξ ⤳ centre zq), Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ zq = ξ ∧ InChart ξ x c ⟨centre zq, hc⟩ ∧ (∀ a ∈ regAt ξ ⟨centre zq, hc⟩, a ∈ A) ∧ (∀ a ∈ regAt ξ ⟨centre zq, hc⟩, a ≠ 0 → a⁻¹ ∈ A → a⁻¹ ∈ regAt ξ ⟨centre zq, hc⟩) := by
  intro X Ω _ ξ κ x T A _ c hc hA
  obtain ⟨V, hV, hmem⟩ := T.affine c hc
  have hgV : genPt ξ ∈ V := by
    refine (hmem _).2 ⟨specializes_rfl, hc, fun j => ?_⟩
    obtain ⟨s, hs⟩ := T.gen.bij.2 (x j / x c)
    refine ⟨s, ?_⟩
    rw [← hs]
    simp only [genMap, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  let ρ : Γ(X, V) →+* Ω := (X.presheaf.germ V (genPt ξ) hgV ≫ Scheme.stalkClosedPointTo ξ).hom
  have hρ : ∀ (f : Γ(X, V)) (p : Cpt ξ) (hp : p.1 ∈ V), genMap ξ p (X.presheaf.germ V p.1 hp f) = ρ f :=
    fun f p hp => genMap_germ' V hgV f p hp
  have hρA : ∀ f, ρ f ∈ A := fun f => by
    have h1 : ρ f ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) :=
      (T.ring c hc _).2 fun p hp => ⟨_, hρ f p ((hmem _).2 ⟨p.2, hp⟩)⟩
    generalize ρ f = t at h1
    induction h1 using Algebra.adjoin_induction with
    | mem a ha => obtain ⟨j, rfl⟩ := ha; exact hA j
    | algebraMap r => simpa using intCast_mem A r
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  let φ : Γ(X, V) ⟶ CommRingCat.of A := CommRingCat.ofHom (ρ.codRestrict A hρA)
  have hz : centre (Spec.map φ ≫ hV.fromSpec) ∈ V := by
    change _ ∈ (V : Set X)
    rw [← hV.range_fromSpec]
    exact ⟨_, rfl⟩
  obtain ⟨hs, hin⟩ := (hmem _).1 hz
  have hfac : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ Spec.map φ ≫ hV.fromSpec = ξ := by
    have e1 : φ ≫ CommRingCat.ofHom (algebraMap A Ω) =
        X.presheaf.germ V (genPt ξ) hgV ≫ Scheme.stalkClosedPointTo ξ := rfl
    have e2 : Spec.map (X.presheaf.germ V (genPt ξ) hgV) ≫ hV.fromSpec = X.fromSpecStalk (genPt ξ) :=
      hV.fromSpecStalk_eq_fromSpecStalk hgV
    rw [← Category.assoc, ← Spec.map_comp, e1]
    exact (congrArg (· ≫ hV.fromSpec) (Spec.map_comp _ _)).trans ((Category.assoc _ _ _).trans
      ((congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) e2).trans
        (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)))
  have hg := genMap_eq_of_factor (algebraMap A Ω) _ hfac hs
  refine ⟨Spec.map φ ≫ hV.fromSpec, hs, hfac, hin, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    rw [hg]
    exact Subtype.property _
  · exact inv_mem_range_of_local A (Scheme.stalkClosedPointTo (Spec.map φ ≫ hV.fromSpec)).hom
      (Scheme.isLocalHom_stalkClosedPointTo _) _ hg

end ModelDimension
end
end

-- bundled from Development.WeilBound.CoreStatements.CommonZeroEvaluation.LieLatticeLocalRing
section
open AlgebraicGeometry CategoryTheory MonObj
open GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace ModelDimension

theorem lie_lattice_local_ring : ∀ (X : Scheme.{0}) (G : CategoryTheory.Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (A : Subring Ω) [IsLocalRing A], IsCptGen ξ → AlgebraicGeometry.Smooth G.hom → ∀ (zq : Spec (CommRingCat.of A) ⟶ X), Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ zq = ξ → ∀ (hc : genPt ξ ⤳ centre zq) (e : Li), e ∈ Submodule.span A (M.lat ⟨centre zq, hc⟩ : Set Li) ↔ ∃ v : GlobalTheory.CompanionTheory.Ar.epsAt zq ⟶ G, GlobalTheory.CompanionTheory.Ar.IsTanAt G zq v ∧ (M.pt e).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap A Ω))) ≫ v.left := by
  intro X G _ _ Ω _ ξ Li _ _ M A _ hξ hG zq hz hc e
  have hg := genMap_eq_of_factor (algebraMap A Ω) zq hz hc
  subst hz
  rw [← lieLat_fibAt_iff X G Ω _ Li M A zq Ω Li M hξ hG hc specializes_rfl e]
  unfold LieModel.fibAt
  refine Iff.of_eq (congrArg (fun s : Set Li => e ∈ Submodule.span A s) (Set.ext fun w => ⟨fun hw => ?_, ?_⟩))
  · obtain ⟨v, hv⟩ := ((lieLat_carrier X G Ω _ Li M _).1 w).1 hw
    refine ⟨hc, w, hw, LieFib.valAt_base M zq hc specializes_rfl v hv _
      (LieCarrier.epsHom (Scheme.stalkClosedPointTo zq).hom _ _ (Scheme.Spec_stalkClosedPointTo_fromSpecStalk zq) ≫ v)
      ?_ rfl⟩
    have e1 := LieFib.spec_dualMap_comp (Scheme.stalkClosedPointTo zq).hom (algebraMap A Ω)
    rw [← hg] at e1
    exact hv.2.trans ((congrArg (· ≫ v.left) e1).trans (Category.assoc _ _ _))
  · rintro ⟨_, e', he', h, v, hv, hw⟩
    have hg' := genMap_eq_of_factor (RingHom.id Ω) (Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ zq)
      (by rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]) h
    have h2 := hv.2
    rw [hg'] at h2
    have : w = e' := M.inj (Over.OverMorphism.ext (hw.trans h2.symm))
    rw [this]
    exact he'

end ModelDimension
end
end

