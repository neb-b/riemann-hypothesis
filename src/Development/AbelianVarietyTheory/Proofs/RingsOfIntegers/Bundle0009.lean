module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.BoxProductLinearIndependent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace BoxIndep

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_tensor_pow (F O : Type) [Field F] [CommRing O] [Algebra F O] {m : ℕ} (β : Fin m → O)
    (hβ : LinearIndependent F β) (j : ℕ) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra F B) (em : Fin j → (O →ₐ[F] B)),
      LinearIndependent F (fun a : Fin j → Fin m => ∏ i, em i (β (a i))) := by
  induction j with
  | zero =>
    refine ⟨F, inferInstance, inferInstance, fun i => i.elim0, ?_⟩
    rw [linearIndependent_unique_iff]
    simp
  | succ j ih =>
    obtain ⟨B, _, _, em, h⟩ := ih
    refine ⟨TensorProduct F O B, inferInstance, inferInstance,
      Fin.cons Algebra.TensorProduct.includeLeft
        (fun i => (Algebra.TensorProduct.includeRight).comp (em i)), ?_⟩
    have h2 := (hβ.tmul_of_isDomain h).comp (Fin.consEquiv (fun _ : Fin (j+1) => Fin m)).symm
      (Equiv.injective _)
    refine (congrArg (fun v : (Fin (j + 1) → Fin m) → TensorProduct F O B => LinearIndependent F v) (funext fun a => ?_)).mpr h2
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, AlgHom.comp_apply, Function.comp_apply]
    rw [← map_prod, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
    rfl

variable {X Z : Scheme.{0}}

noncomputable def germOf {B : CommRingCat.{0}} (r : Z ⟶ Spec B) (z : Z) : B →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (r ⁻¹ᵁ ⊤) z trivial).hom.comp ((r.app ⊤).hom.comp (Scheme.ΓSpecIso B).inv.hom)

theorem germOf_apply {B : CommRingCat.{0}} (r : Z ⟶ Spec B) (z : Z) (a : B) :
    germOf r z a = gs r z ⊤ ((Scheme.ΓSpecIso B).inv.hom a) := (gs_eq r z ⊤ trivial _).symm

theorem germOf_map {B C : CommRingCat.{0}} (r : Z ⟶ Spec C) (φ : B ⟶ C) (z : Z) (a : B) :
    germOf (r ≫ Spec.map φ) z a = germOf r z (φ.hom a) := by
  rw [germOf_apply, germOf_apply, ← gs_pull r (Spec.map φ) z ⊤ trivial]
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality φ)
  exact congrArg (gs r z ⊤) e.symm

theorem eq_zero_of_germOf {B : CommRingCat.{0}} (a : B) (h : ∀ z, germOf (𝟙 (Spec B)) z a = 0) : a = 0 := by
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).inv).1
  refine fn_ext fun z hz => ?_
  rw [map_zero, gs_zero _ _ _ hz]
  exact (germOf_apply _ _ _).symm.trans (h z)

theorem fromSpecStalk_mem (x : X) {U : X.Opens} (hx : x ∈ U) (y : Spec (X.presheaf.stalk x)) :
    X.fromSpecStalk x y ∈ U := by
  have : X.fromSpecStalk x y ∈ Set.range (X.fromSpecStalk x) := ⟨y, rfl⟩
  rw [Scheme.range_fromSpecStalk] at this
  exact Specializes.mem_open this U.isOpen hx

theorem gs_fromSpecStalk (x : X) {U : X.Opens} (hx : x ∈ U) (r : Z ⟶ Spec (X.presheaf.stalk x)) (z : Z)
    (a : Γ(X, U)) : gs (r ≫ X.fromSpecStalk x) z U a = germOf r z (gs (𝟙 X) x U a) := by
  have hm := fromSpecStalk_mem x hx (r z)
  rw [← gs_pull r _ z U hm, Scheme.fromSpecStalk_app hx, germOf_apply, gs_eq (𝟙 X) x U hx]
  exact gs_res r z le_top hm _

theorem fromSpecStalk_comp {B : CommRingCat.{0}} (p : X ⟶ Spec B) (x : X) :
    X.fromSpecStalk x ≫ p = Spec.map (CommRingCat.ofHom (germOf p x)) := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, ← cancel_epi (Scheme.ΓSpecIso B).inv,
    ← Scheme.ΓSpecIso_inv_naturality]
  ext a
  have e : CommRingCat.ofHom (germOf p x) =
      (Scheme.ΓSpecIso B).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ x trivial := rfl
  simp [e]

theorem exists_test {F : Type} [Field F] (p : X ⟶ Spec (CommRingCat.of F)) (x : X) {U : X.Opens} (hx : x ∈ U) {m : ℕ}
    (s : Fin m → Γ(X, U))
    (hs : ∀ c : Fin m → F, ∑ l, germOf p x (c l) * gs (𝟙 X) x U (s l) = 0 → c = 0) (j : ℕ) :
    ∃ (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of F)) (r : Fin j → (Z ⟶ X)), (∀ i, r i ≫ p = q) ∧
      (∀ i z, r i z ∈ U) ∧ ∀ c : (Fin j → Fin m) → F,
        (∀ z, ∑ a, germOf q z (c a) * ∏ i, gs (r i) z U (s (a i)) = 0) → c = 0 := by
  let : Algebra F (X.presheaf.stalk x) := (germOf p x).toAlgebra
  have hβ : LinearIndependent F (fun l => gs (𝟙 X) x U (s l)) :=
    Fintype.linearIndependent_iff.2 fun c hc => congrFun (hs c (by simp only [Algebra.smul_def] at hc; exact hc))
  obtain ⟨B, _, _, em, h⟩ := exists_tensor_pow F _ _ hβ j
  refine ⟨Spec (CommRingCat.of B), Spec.map (CommRingCat.ofHom (algebraMap F B)),
    fun i => (Spec.map (CommRingCat.ofHom (em i).toRingHom) : _ ⟶ Spec (X.presheaf.stalk x)) ≫ X.fromSpecStalk x,
    fun i => ?_, fun i z => fromSpecStalk_mem x hx _, fun c hc => ?_⟩
  · rw [Category.assoc, fromSpecStalk_comp]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact (em i).commutes a
  · funext a
    refine Fintype.linearIndependent_iff.1 h c (eq_zero_of_germOf (B := CommRingCat.of B) _ fun z => ?_) a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc z, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Algebra.smul_def, map_mul, map_prod]
    congr 1
    · rw [← Category.id_comp (Spec.map _), germOf_map]; rfl
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [gs_fromSpecStalk x hx]
      exact (germOf_map (B := X.presheaf.stalk x) (𝟙 _) (CommRingCat.ofHom (em i).toRingHom) z _).symm

theorem gs_liftFun {S : Scheme.{0}} (A : Over S) {B : CommRingCat.{0}} (t : Spec B ⟶ S)
    (W : (Over.mk t ⊗ A).left.Opens) (r : Z ⟶ (Over.mk t ⊗ A).left) (z : Z) (hz : r z ∈ W) (a : B) :
    gs r z W (liftFun A (T := Over.mk t) W ((Scheme.ΓSpecIso B).inv.hom a)) =
      germOf (B := B) (r ≫ (fst (Over.mk t) A).left) z a :=
  (gs_res r z le_top hz _).trans ((gs_pull r (fst (Over.mk t) A).left z ⊤ trivial _).trans (germOf_apply _ _ _).symm)

theorem gs_comb {S : Scheme.{0}} (A : Over S) {B : CommRingCat.{0}} (t : Spec B ⟶ S)
    (W : (Over.mk t ⊗ A).left.Opens) (r : Z ⟶ (Over.mk t ⊗ A).left) (z : Z) (hz : r z ∈ W) {K : Type} [Fintype K]
    (c : K → B) (f : K → Γ((Over.mk t ⊗ A).left, W)) :
    gs r z W (∑ l, liftFun A (T := Over.mk t) W ((Scheme.ΓSpecIso B).inv.hom (c l)) * f l) =
      ∑ l, germOf (B := B) (r ≫ (fst (Over.mk t) A).left) z (c l) * gs r z W (f l) := by
  rw [gs_fsum r z W hz]
  exact Finset.sum_congr rfl fun l _ => by rw [gs_mul r z W hz, gs_liftFun A t W r z hz]

theorem box_indep {S : Scheme.{0}} (j : ℕ) (A A' : PolAV S) (pA : IsPowPolAV A' A j) (F : Type) [Field F]
    (t : Spec (CommRingCat.of F) ⟶ S) (k m : ℕ)
    (b : Fin m → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (Over.mk t) A.A).left) (fun _ => (k : ℤ))))
    (hb : ∀ c : Fin m → F,
      (∀ jj, ∑ l, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c l)) * (b l).f jj = 0) → c = 0)
    (t' : (Fin j → Fin m) →
      LB.Sec (LB.LinComb A'.L (K := Fin 1) (fun _ => (snd (Over.mk t) A'.A).left) (fun _ => (k : ℤ))))
    (ht : ∀ a, (∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.mk t) ⊗ A'.A).left) (z : Z) (J J'), Good A.L z J → Good A'.L z J' →
      (bw pA.w (r ≫ (snd (Over.mk t) A'.A).left) z (fun i => J ((r ≫ (snd (Over.mk t) A'.A).left) ≫ (pA.pr i).left))
        (J' (r ≫ (snd (Over.mk t) A'.A).left)) ^ k).val * sval (t' a) r z J' =
        ∏ i, sval (b (a i)) (r ≫ ((Over.mk t) ◁ pA.pr i).left) z J))
    (c : (Fin j → Fin m) → F)
    (hc : ∀ jj, ∑ a, liftFun A'.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c a)) * (t' a).f jj = 0) :
    c = 0 := by
  have := A.isAb.smooth
  have := A.isAb.geomConnected
  have hg := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres A.A.hom
  have hint : IsIntegral (Over.mk t ⊗ A.A).left :=
    hg.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback t A.A.hom).flip
  obtain ⟨j₀, hj₀⟩ := exists_chart A.isLB ((snd (Over.mk t) A.A).left (genericPoint (Over.mk t ⊗ A.A).left))
  have hx : genericPoint (Over.mk t ⊗ A.A).left ∈
      LB.wchart A.L (fun _ : Fin 1 => (snd (Over.mk t) A.A).left) (fun _ => j₀) := Set.mem_iInter.2 fun _ => hj₀
  obtain ⟨Z, q, r, hq, hr, H⟩ := exists_test (F := F) (fst (Over.mk t) A.A).left _ hx (fun l => (b l).f (fun _ => j₀))
    (fun c hc => hb c fun jj => by
      refine fn_ext fun y hy => congrArg _ ?_
      have hy' : genericPoint (Over.mk t ⊗ A.A).left ∈
          LB.wchart A.L (fun _ : Fin 1 => (snd (Over.mk t) A.A).left) jj :=
        ((genericPoint_spec _).mem_open_set_iff (TopologicalSpace.Opens.isOpen _)).mpr ⟨y, trivial, hy⟩
      apply germ_injective_of_isIntegral _ _ hy'
      refine (gs_eq (𝟙 _) _ _ hy' _).symm.trans (Eq.trans ?_ (map_zero _).symm)
      refine (gs_comb A.A t _ (𝟙 _) _ hy' c _).trans ?_
      simp only [fun l => sec_trans (b l) (𝟙 _) _ hy' hx, Category.id_comp, mul_left_comm _ (Units.val _)]
      rw [← Finset.mul_sum]
      exact (congrArg _ hc).trans (mul_zero _)) j
  let T : Over S := Over.mk (q ≫ t)
  let q' : T ⟶ Over.mk t := Over.homMk q rfl
  let r' : Fin j → (T ⟶ Over.mk t ⊗ A.A) := fun i => Over.homMk (r i) (by
    rw [← Over.w (fst (Over.mk t) A.A), ← Category.assoc, hq]; rfl)
  let ρ : T ⟶ Over.mk t ⊗ A'.A := lift q' (Fan.IsLimit.lift pA.lim fun i => r' i ≫ snd _ _)
  have hρ : ∀ i, ρ ≫ Over.mk t ◁ pA.pr i = r' i := fun i => by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, lift_fst]
      exact Over.OverMorphism.ext (hq i).symm
    · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd]
      exact Fan.IsLimit.fac pA.lim _ i
  have hρ' : ∀ i, (ρ.left : Z ⟶ _) ≫ (Over.mk t ◁ pA.pr i).left = r i := fun i => congrArg (fun g => g.left) (hρ i)
  have hρq : (ρ.left : Z ⟶ _) ≫ (fst (Over.mk t) A'.A).left = q :=
    congrArg (fun g => g.left) (lift_fst q' (Fan.IsLimit.lift pA.lim fun i => r' i ≫ snd _ _))
  refine H c fun z => ?_
  obtain ⟨J, hJ, eJ⟩ := exists_good A.L A.isLB z (fun i => r i ≫ (snd (Over.mk t) A.A).left) (fun _ => j₀)
    (fun _ _ _ => rfl) (fun i => Set.mem_iInter.1 (hr i z) 0)
  choose J' hJ' using fun ψ : Z ⟶ A'.A.left => exists_chart A'.isLB (ψ z)
  have hJ' : Good A'.L z J' := hJ'
  have hm := hJ'.mem (fun _ : Fin 1 => (snd (Over.mk t) A'.A).left) (ρ.left : Z ⟶ _)
  have E := (gs_comb A'.A t _ (ρ.left : Z ⟶ _) z hm c _).symm.trans
    ((congrArg _ (hc _)).trans (gs_zero _ _ _ hm))
  have E' := fun a => ht a Z ρ.left z J J' hJ hJ'
  simp only [hρ'] at E'
  rw [hρq] at E
  obtain ⟨u, hu⟩ : ∃ u : Z.presheaf.stalk z, ∀ a, u * sval (Z := Z) (t' a) ρ.left z J' =
      ∏ i, sval (b (a i)) (r i) z J := ⟨_, E'⟩
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) ((Finset.mul_sum _ _ u).symm.trans
    ((congrArg _ E).trans (mul_zero _)))
  refine Eq.trans (congrArg _ ((Finset.prod_congr rfl fun i _ =>
    (sval_of (b (a i)) (r i) z J (fun _ => j₀) (fun _ => eJ i)).symm).trans (hu a).symm)) ?_
  exact mul_left_comm _ _ _

end BoxIndep

theorem boxProduct_linearIndependent : ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (pA : IsPowPolAV A' A j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (m : ℕ) (b : Fin m → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (k : ℤ)))), (∀ c : Fin m → F, (∀ jj, ∑ l, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c l)) * (b l).f jj = 0) → c = 0) → ∀ t' : (Fin j → Fin m) → LB.Sec (LB.LinComb A'.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A'.A).left) (fun _ => (k : ℤ))), (∀ a, (∀ (Z : Scheme.{0}) (r : Z ⟶ ((TFK (R := R) F) ⊗ A'.A).left) (z : Z) (J J'), Geo.Tor.Good A.L z J → Geo.Tor.Good A'.L z J' → (bw pA.w (r ≫ (snd (TFK (R := R) F) A'.A).left) z (fun i => J ((r ≫ (snd (TFK (R := R) F) A'.A).left) ≫ (pA.pr i).left)) (J' (r ≫ (snd (TFK (R := R) F) A'.A).left)) ^ k).val * Geo.Tor.sval (t' a) r z J' = ∏ i, Geo.Tor.sval (b (a i)) (r ≫ ((TFK (R := R) F) ◁ pA.pr i).left) z J)) → ∀ c : (Fin j → Fin m) → F, (∀ jj, ∑ a, liftFun A'.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c a)) * (t' a).f jj = 0) → c = 0 :=
  fun R _ _ j A A' pA F _ _ k m b hb t' ht c hc =>
    BoxIndep.box_indep j A A' pA F (jFK (R := R) F) k m b hb t' ht c hc

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxIso
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowerThickIso

section General

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_res gm_pull gm_div gm_linComb gm_pull_g gm_self mem_pull PGen isGen_iff glue_unit
  exists_chart)

variable {B B' G G' Ge Ge' : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {j : ℕ}
  {pr : Fin j → (B' ⟶ B)} {prG : Fin j → (G' ⟶ G)} {pG : Ge ⟶ B} {pG' : Ge' ⟶ B'} {fG : Ge ⟶ G} {fG' : Ge' ⟶ G'}
  {h : Fin j → (Ge' ⟶ Ge)}

theorem gm_box_g {Z : Scheme.{0}} (ψ : Z ⟶ B') (z : Z) (a b : Fin j → M.ι) (ha : ∀ i, pr i (ψ z) ∈ M.U (a i))
    (hb : ∀ i, pr i (ψ z) ∈ M.U (b i)) :
    gm ψ z (LB.wchart M pr a ⊓ LB.wchart M pr b) ((LB.LinComb M pr (fun _ => 1)).g a b) =
      ∏ i, gm (ψ ≫ pr i) z (M.U (a i) ⊓ M.U (b i)) (M.g (a i) (b i)) :=
  (gm_linComb M pr (fun _ => 1) ψ z a b (Set.mem_iInter.2 ha) (Set.mem_iInter.2 hb)).trans
    (Finset.prod_congr rfl fun _ _ => zpow_one _)

theorem bw_change {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} (hw : w.IsGen) {Z : Scheme.{0}} (ψ : Z ⟶ B') (z : Z)
    (a b : Fin j → M.ι) (k k' : M'.ι) (ha : ∀ i, pr i (ψ z) ∈ M.U (a i)) (hb : ∀ i, pr i (ψ z) ∈ M.U (b i))
    (hk : ψ z ∈ M'.U k) (hk' : ψ z ∈ M'.U k') :
    bw w ψ z a k = (∏ i, gm (ψ ≫ pr i) z (M.U (a i) ⊓ M.U (b i)) (M.g (a i) (b i))) *
      (gm ψ z _ (M'.g k k'))⁻¹ * bw w ψ z b k' := by
  have hm : ψ z ∈ LB.wchart M pr a ⊓ M'.U k ⊓ (LB.wchart M pr b ⊓ M'.U k') :=
    ⟨⟨Set.mem_iInter.2 ha, hk⟩, Set.mem_iInter.2 hb, hk'⟩
  have e := congrArg (gm ψ z (LB.wchart M pr a ⊓ M'.U k ⊓ (LB.wchart M pr b ⊓ M'.U k'))) (hw (a, k) (b, k'))
  have e' := (gm_res ψ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div M' (LB.LinComb M pr (fun _ => 1)) ψ z (a, k) (b, k') hm) (gm_res ψ z _ hm _))))
  rw [← gm_box_g ψ z a b ha hb]
  exact e'

def germ (pG' : Ge' ⟶ B') (h : Fin j → (Ge' ⟶ Ge)) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1)))
    (we : LB.Iso (L.pull fG) (M.pull pG)) {Z : Scheme.{0}} (r : Z ⟶ Ge') (z : Z) (jM : Fin j → M.ι) (jM' : M'.ι)
    (jL : Fin j → L.ι) : (Z.presheaf.stalk z)ˣ :=
  (bw w (r ≫ pG') z jM jM')⁻¹ * ∏ i, Geo.Tor.gw we (r ≫ h i) z (jM i) (fun _ => jL i)

theorem germ_change (e₁ : ∀ i, pG' ≫ pr i = h i ≫ pG) (e₂ : ∀ i, h i ≫ fG = fG' ≫ prG i)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : w.IsGen) (hwe : PGen we)
    {Z : Scheme.{0}} (r : Z ⟶ Ge') (z : Z) (jM kM : Fin j → M.ι) (jM' kM' : M'.ι) (jL kL : Fin j → L.ι)
    (a₁ : ∀ i, pr i (pG' (r z)) ∈ M.U (jM i)) (a₂ : pG' (r z) ∈ M'.U jM') (a₃ : ∀ i, prG i (fG' (r z)) ∈ L.U (jL i))
    (b₁ : ∀ i, pr i (pG' (r z)) ∈ M.U (kM i)) (b₂ : pG' (r z) ∈ M'.U kM') (b₃ : ∀ i, prG i (fG' (r z)) ∈ L.U (kL i)) :
    germ pG' h w we r z jM jM' jL =
      gm (r ≫ pG') z _ (M'.g jM' kM') *
        (∏ i, gm ((r ≫ fG') ≫ prG i) z (L.U (jL i) ⊓ L.U (kL i)) (L.g (jL i) (kL i)))⁻¹ *
        germ pG' h w we r z kM kM' kL := by
  have p₁ : ∀ i, pG (h i (r z)) = pr i (pG' (r z)) := fun i => congrArg (fun g => g (r z)) (e₁ i).symm
  have p₂ : ∀ i, fG (h i (r z)) = prG i (fG' (r z)) := fun i => congrArg (fun g => g (r z)) (e₂ i)
  have a := bw_change hw (r ≫ pG') z jM kM jM' kM' a₁ b₁ a₂ b₂
  have c : ∀ i, Geo.Tor.gw we (r ≫ h i) z (jM i) (fun _ => jL i) =
      gm ((r ≫ pG') ≫ pr i) z (M.U (jM i) ⊓ M.U (kM i)) (M.g (jM i) (kM i)) *
        (gm ((r ≫ fG') ≫ prG i) z (L.U (jL i) ⊓ L.U (kL i)) (L.g (jL i) (kL i)))⁻¹ *
        Geo.Tor.gw we (r ≫ h i) z (kM i) (fun _ => kL i) := fun i => by
    have c₃ : fG (h i (r z)) ∈ L.U (jL i) := p₂ i ▸ a₃ i
    have d₃ : fG (h i (r z)) ∈ L.U (kL i) := p₂ i ▸ b₃ i
    have c₁ : pG (h i (r z)) ∈ M.U (jM i) := p₁ i ▸ a₁ i
    have d₁ : pG (h i (r z)) ∈ M.U (kM i) := p₁ i ▸ b₁ i
    have c := hwe Z (r ≫ h i) z (jM i) (kM i) (fun _ => jL i) (fun _ => kL i) c₁ d₁ (mem_pull.2 c₃) (mem_pull.2 d₃)
    rw [gm_pull_g L fG (r ≫ h i) z (fun _ => jL i) (fun _ => kL i) (mem_pull.2 c₃) (mem_pull.2 d₃),
      Category.assoc, Category.assoc, ← e₁, e₂] at c
    rw [Category.assoc, Category.assoc]
    exact c
  unfold germ
  rw [a, Finset.prod_congr rfl fun i _ => c i, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib]
  generalize (∏ i, gm ((r ≫ pG') ≫ pr i) z (M.U (jM i) ⊓ M.U (kM i)) (M.g (jM i) (kM i))) = A
  generalize (∏ i, gm ((r ≫ fG') ≫ prG i) z (L.U (jL i) ⊓ L.U (kL i)) (L.g (jL i) (kL i))) = C
  generalize gm (r ≫ pG') z _ (M'.g jM' kM') = A'
  generalize bw w (r ≫ pG') z kM kM' = P
  generalize (∏ i, Geo.Tor.gw we (r ≫ h i) z (kM i) (fun _ => kL i)) = R
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_unit (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB)
    (e₁ : ∀ i, pG' ≫ pr i = h i ≫ pG) (e₂ : ∀ i, h i ≫ fG = fG' ≫ prG i)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : w.IsGen) (hwe : PGen we)
    (jM' : M'.ι) (jL : Fin j → L.ι) :
    ∃ s : Γ(Ge', (M'.pull pG').U (fun _ => jM') ⊓ ((LB.LinComb L prG (fun _ => 1)).pull fG').U (fun _ => jL))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : Fin j → M.ι), (∀ i, pr i (pG' (r z)) ∈ M.U (jM i)) →
        pG' (r z) ∈ M'.U jM' → (∀ i, prG i (fG' (r z)) ∈ L.U (jL i)) →
        gm r z _ s = germ pG' h w we r z jM jM' jL := by
  have p₁ : ∀ i x, pG (h i x) = pr i (pG' x) := fun i x => congrArg (fun g => g x) (e₁ i).symm
  have p₂ : ∀ i x, fG (h i x) = prG i (fG' x) := fun i x => congrArg (fun g => g x) (e₂ i)
  obtain ⟨W, hW⟩ : ∃ W : (Fin j → M.ι) → Ge'.Opens, ∀ a x, x ∈ W a ↔
      (∀ i, pr i (pG' x) ∈ M.U (a i)) ∧ pG' x ∈ M'.U jM' ∧ ∀ i, prG i (fG' x) ∈ L.U (jL i) :=
    ⟨fun a => pG' ⁻¹ᵁ LB.wchart M pr a ⊓ (pG' ⁻¹ᵁ M'.U jM' ⊓ fG' ⁻¹ᵁ LB.wchart L prG jL),
      fun _ _ => and_congr Set.mem_iInter (and_congr Iff.rfl Set.mem_iInter)⟩
  have l₀ : ∀ a, W a ≤ (M'.pull pG').U (fun _ => jM') ⊓ ((LB.LinComb L prG (fun _ => 1)).pull fG').U (fun _ => jL) :=
    fun a x hx => ⟨mem_pull.2 ((hW a x).1 hx).2.1, mem_pull.2 (Set.mem_iInter.2 ((hW a x).1 hx).2.2)⟩
  have l₁ : ∀ a, W a ≤ pG' ⁻¹ᵁ (LB.wchart M pr a ⊓ M'.U jM') := fun a x hx =>
    ⟨Set.mem_iInter.2 ((hW a x).1 hx).1, ((hW a x).1 hx).2.1⟩
  have l₂ : ∀ a i, W a ≤ h i ⁻¹ᵁ ((M.pull pG).U (fun _ => a i) ⊓ (L.pull fG).U (fun _ => jL i)) := fun a i x hx =>
    ⟨mem_pull.2 ((p₁ i x).symm ▸ ((hW a x).1 hx).1 i), mem_pull.2 ((p₂ i x).symm ▸ ((hW a x).1 hx).2.2 i)⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ a, Γ(Ge', W a)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (a : Fin j → M.ι), r z ∈ W a →
      gm r z (W a) (u a) = germ pG' h w we r z a jM' jL :=
    ⟨fun a => (res (l₁ a) (pullU pG' _ (w.s (a, jM'))))⁻¹ *
        ∏ i, res (l₂ a i) (pullU (h i) _ (we.s (fun _ => a i, fun _ => jL i))),
      fun Z r z a hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹)
        ((gm_res r z (l₁ a) hz _).trans (gm_pull r pG' z _ (l₁ a hz) _)))) ((map_prod _ _ _).trans
          (Finset.prod_congr rfl fun i _ =>
            (gm_res r z (l₂ a i) hz _).trans (gm_pull r (h i) z _ (l₂ a i hz) _))))⟩
  obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
      choose a ha using fun i => exists_chart hM (pr i (pG' x))
      exact TopologicalSpace.Opens.mem_iSup.2
        ⟨a, (hW a x).2 ⟨ha, mem_pull.1 hx.1, Set.mem_iInter.1 (mem_pull.1 hx.2)⟩⟩) u
    (fun a a' x hx => by
      have h₁ := (hW a x).1 hx.1
      have h₂ := (hW a' x).1 hx.2
      have k := germ_change e₁ e₂ hw hwe (𝟙 Ge') x a a' jM' jM' jL jL h₁.1 h₁.2.1 h₁.2.2 h₂.1 h₂.2.1 h₂.2.2
      rw [gm_self hM' (𝟙 Ge' ≫ pG') x h₁.2.1, Finset.prod_eq_one fun i _ =>
        gm_self hL ((𝟙 Ge' ≫ fG') ≫ prG i) x (h₁.2.2 i), inv_one, _root_.one_mul, _root_.one_mul] at k
      exact (hu _ (𝟙 Ge') x a hx.1).trans (k.trans (hu _ (𝟙 Ge') x a' hx.2).symm))
  refine ⟨s, fun Z r z jM a₁ a₂ a₃ => ?_⟩
  have hz := (hW jM (r z)).2 ⟨a₁, a₂, a₃⟩
  exact (gm_res r z (l₀ jM) hz s).symm.trans ((congrArg (gm r z (W jM)) (hs jM)).trans (hu Z r z jM hz))

theorem exists_box_iso (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB)
    (e₁ : ∀ i, pG' ≫ pr i = h i ≫ pG) (e₂ : ∀ i, h i ≫ fG = fG' ≫ prG i)
    (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (we : LB.Iso (L.pull fG) (M.pull pG)) (hw : w.IsGen)
    (hwe : we.IsGen) :
    ∃ we' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull fG') (M'.pull pG'), we'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : Fin j → M.ι) (jM' : M'.ι) (jL : Fin j → L.ι),
        (∀ i, pr i (pG' (r z)) ∈ M.U (jM i)) → pG' (r z) ∈ M'.U jM' → (∀ i, prG i (fG' (r z)) ∈ L.U (jL i)) →
        bw w (r ≫ pG') z jM jM' * Geo.Tor.gw we' r z jM' (fun _ => jL) =
          ∏ i, Geo.Tor.gw we (r ≫ h i) z (jM i) (fun _ => jL i) := by
  rw [isGen_iff] at hwe
  choose s hs using exists_unit hM hM' hL e₁ e₂ hw hwe
  refine ⟨⟨fun p => s (p.1 PUnit.unit) (p.2 PUnit.unit)⟩, (isGen_iff _).2 ?_, fun Z r z jM jM' jL a₁ a₂ a₃ => ?_⟩
  · intro Z r z l l' k k' a₂ b₂ a₄ b₄
    choose a ha using fun i => exists_chart hM (pr i (pG' (r z)))
    have a₄' : ∀ i, prG i (fG' (r z)) ∈ L.U (k PUnit.unit i) := Set.mem_iInter.1 (mem_pull.1 a₄)
    have b₄' : ∀ i, prG i (fG' (r z)) ∈ L.U (k' PUnit.unit i) := Set.mem_iInter.1 (mem_pull.1 b₄)
    have c := germ_change e₁ e₂ hw hwe r z a a l l' _ _ ha a₂ a₄' ha b₂ b₄'
    rw [← hs l _ Z r z a ha a₂ a₄', ← hs l' _ Z r z a ha b₂ b₄', ← gm_box_g (r ≫ fG') z _ _ a₄' b₄'] at c
    rw [gm_pull_g (LB.LinComb L prG (fun _ => 1)) fG' r z k k' a₄ b₄]
    exact c
  · exact (congrArg (bw w (r ≫ pG') z jM jM' * ·) (hs jM' jL Z r z jM a₁ a₂ a₃)).trans
      (mul_inv_cancel_left _ _)

end General

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (e : ℕ) (g : GtCoord I D.toPre e G) (g' : GtCoord I D'.toPre e G'), (∀ i, g'.pG.left ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ g.pG.left) → ∀ (L : LB G.left), L.IsLB → ∀ w : LB.Iso (L.pull (fstG I e G).left) (D.toPre.P.L.pull g.pG.left), w.IsGen → ∃ w' : LB.Iso ((boxLB L pG.pr).pull (fstG I e G').left) (D'.toPre.P.L.pull g'.pG.left), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : Fin j → L.ι), (∀ i, (pD.pw.pr i).left (g'.pG.left (r z)) ∈ D.toPre.P.L.U (jM i)) → g'.pG.left (r z) ∈ D'.toPre.P.L.U jM' → (∀ i, (pG.pr i).left ((fstG I e G').left (r z)) ∈ L.U (jL i)) → bw pD.w (r ≫ g'.pG.left) z jM jM' * Geo.Tor.gw w' r z jM' (fun _ => jL) = ∏ i, Geo.Tor.gw w (r ≫ ((Over.pullback (thick R I e)).map (pG.pr i)).left) z (jM i) (fun _ => jL i) := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG e g g' hq L hL w hw
  have hρ : ∀ i, rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := fun i => pullback.lift_fst _ _ _
  exact exists_box_iso (Ge := (thickObj R I e G).left) (Ge' := (thickObj R I e G').left) (h := rhoE I pG e)
    (pG := g.pG.left) (pG' := g'.pG.left) (fG := fGl I G e) (fG' := fGl I G' e)
    D.toPre.P.isLB D'.toPre.P.isLB hL hq hρ pD.w w pD.w_gen hw

end GlobalTheory.PowerThickIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPivot
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.SatLin

theorem exists_pivot {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {Ix : Type}
    (x : Ix → V) (hx : x ≠ 0) :
    ∃ (i₀ : Ix) (u : Ix → V), x i₀ ≠ 0 ∧ ∀ i, x i = x i₀ * u i := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
  have : Nonempty Ix := ⟨j⟩
  let f : Ix → ℕ∞ := fun i => IsDiscreteValuationRing.addVal V (x i)
  let i₀ := Function.argmin f
  have h : ∀ i, x i₀ ∣ x i := fun i =>
    IsDiscreteValuationRing.addVal_le_iff_dvd.1 (Function.argmin_le f i)
  choose u hu using h
  refine ⟨i₀, u, fun h0 => hj ?_, hu⟩
  rw [hu j, h0, zero_mul]; rfl

theorem aux {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {K : Type} [Field K] {F : Type} [Field F] (φ : V →+* K) (hφ : Function.Injective φ) (κ : K →+* F)
    (v : AddValuation F (WithTop ℚ)) (hv : ∀ x : V, (0 : WithTop ℚ) ≤ v (κ (φ x))) {Ix : Type} (n : ℕ) :
    ∀ (w : Fin n → Ix → V) (c : Fin n → F),
      (∀ i, (0 : WithTop ℚ) ≤ v (∑ p, c p * κ (φ (w p i)))) →
      ∃ (m : ℕ) (c' : Fin m → F) (a : Fin m → Fin n → K) (u : Fin m → Ix → V),
        (∀ l, (0 : WithTop ℚ) ≤ v (c' l)) ∧ (∀ l i, φ (u l i) = ∑ p, a l p * φ (w p i)) ∧
        ∀ i, ∑ p, c p * κ (φ (w p i)) = ∑ l, c' l * κ (φ (u l i)) := by
  induction n with
  | zero =>
    intro w c _
    exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun l => l.elim0, fun l => l.elim0, fun i => by simp⟩
  | succ n ih =>
    intro w c hc
    by_cases h0 : w 0 = 0
    · obtain ⟨m, c', a, u, h1, h2, h3⟩ := ih (fun p => w p.succ) (fun p => c p.succ) (fun i => by
        have := hc i
        rw [Fin.sum_univ_succ, h0] at this
        simpa using this)
      refine ⟨m, c', fun l => Fin.cons 0 (a l), u, h1, fun l i => ?_, fun i => ?_⟩
      · rw [Fin.sum_univ_succ, h2]; simp
      · rw [Fin.sum_univ_succ, h0, ← h3]; simp
    · obtain ⟨i₀, u₀, hne, hu⟩ := exists_pivot (w 0) h0
      have hne' : φ (w 0 i₀) ≠ 0 := fun h => hne (hφ (by rw [h, map_zero]))
      have key : ∀ i, ∑ p : Fin n, c p.succ * κ (φ (w p.succ i - w p.succ i₀ * u₀ i)) =
          ∑ p, c p * κ (φ (w p i)) - (∑ p, c p * κ (φ (w p i₀))) * κ (φ (u₀ i)) := fun i => by
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hu i, add_mul, Finset.sum_mul]
        simp only [map_sub, map_mul, mul_sub, Finset.sum_sub_distrib, _root_.mul_assoc]
        ring
      obtain ⟨m, c', a, u, h1, h2, h3⟩ := ih (fun p i => w p.succ i - w p.succ i₀ * u₀ i)
        (fun p => c p.succ) (fun i => by
          rw [key i]
          refine AddValuation.map_le_sub v (hc i) ?_
          rw [AddValuation.map_mul]
          exact add_nonneg (hc i₀) (hv _))
      refine ⟨m + 1, Fin.cons (∑ p, c p * κ (φ (w p i₀))) c',
        Fin.cons (Fin.cons (φ (w 0 i₀))⁻¹ 0)
          (fun l => Fin.cons (-(∑ p, a l p * φ (w p.succ i₀)) * (φ (w 0 i₀))⁻¹) (a l)),
        Fin.cons u₀ u, fun l => ?_, fun l i => ?_, fun i => ?_⟩
      · refine Fin.cases ?_ (fun l => ?_) l
        · simpa using hc i₀
        · simpa using h1 l
      · refine Fin.cases ?_ (fun l => ?_) l
        · rw [Fin.sum_univ_succ, hu i]
          simp only [Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
            add_zero, map_mul]
          rw [inv_mul_cancel_left₀ hne']
        · rw [Fin.sum_univ_succ, hu i]
          simp only [Fin.cons_zero, Fin.cons_succ, map_mul]
          rw [h2, _root_.mul_assoc, inv_mul_cancel_left₀ hne', neg_mul, Finset.sum_mul]
          simp only [map_sub, map_mul, mul_sub, Finset.sum_sub_distrib, _root_.mul_assoc]
          ring
      · rw [Fin.sum_univ_succ (n := m)]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [← h3, key]
        ring

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (Ix : Type) (n : ℕ) (w : Fin n → Ix → V) (c : Fin n → F), (∀ i, (0 : WithTop ℚ) ≤ v (∑ p, c p * algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (w p i)))) → ∃ (m : ℕ) (c' : Fin m → F) (a : Fin m → Fin n → (FractionRing V)) (u : Fin m → Ix → V), (∀ l, (0 : WithTop ℚ) ≤ v (c' l)) ∧ (∀ l i, algebraMap V (FractionRing V) (u l i) = ∑ p, a l p * algebraMap V (FractionRing V) (w p i)) ∧ ∀ i, ∑ p, c p * algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (w p i)) = ∑ l, c' l * algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (u l i)) := by
  intro V _ _ _ ϖ hϖ F _ _ v hv Ix n w c hc
  exact aux (algebraMap V (FractionRing V)) (IsFractionRing.injective V _)
    (algebraMap (FractionRing V) F) v (GC.v_alg_nonneg hϖ hv) n w c hc

end GlobalTheory.SatLin
end

