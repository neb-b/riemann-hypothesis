module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPointThetaPullbacksIsUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.SimilNonvan

theorem isUnit_gs_of_mem {X Z : Scheme.{0}} {H : LB X} (t : LB.Sec H) (r : Z ⟶ X) (z : Z) {k : H.ι}
    (hk : r z ∈ H.U k) (h : r z ∈ Out.nonzeroLocus t) : IsUnit (gs r z _ (t.f k)) := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  have hj' : r z ∈ H.U j := X.basicOpen_le _ hj
  rw [gs_compat t r z hk hj']
  refine (Units.isUnit _).mul ?_
  rw [gs_eq r z _ hj']
  refine (Z.mem_basicOpen ((r.app _).hom (t.f j)) z hj').1 ?_
  rw [← Scheme.Hom.preimage_basicOpen]
  exact hj

theorem mul_transpose_eq {n : Type} [Fintype n] [DecidableEq n] {al : Matrix n n ℤ} {m : ℤ} (hm : m ≠ 0)
    (h : al.transpose * al = m • (1 : Matrix n n ℤ)) : al * al.transpose = m • (1 : Matrix n n ℤ) := by
  let f : ℤ →+* ℚ := Int.castRingHom ℚ
  have hm' : (m : ℚ) ≠ 0 := Int.cast_ne_zero.2 hm
  have e : ∀ B : Matrix n n ℤ, B = m • (1 : Matrix n n ℤ) ↔ (m : ℚ)⁻¹ • B.map f = 1 := fun B => by
    rw [inv_smul_eq_iff₀ hm']
    constructor
    · rintro rfl
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp [f]
    · intro hB
      ext i j
      have := congrFun (congrFun hB i) j
      apply Int.cast_injective (α := ℚ)
      by_cases hij : i = j <;> simpa [f, Matrix.one_apply, hij] using this
  rw [e, Matrix.map_mul] at h ⊢
  rw [← Matrix.smul_mul] at h
  rw [← Matrix.mul_smul]
  exact mul_eq_one_comm.1 h

variable {K : Type} [Field K] [IsAlgClosed K]

theorem exists_pt_mem (x : KeyIn K) : ∃ z : Pt x, ∀ p, z.left p ∈ Out.nonzeroLocus x.th := by
  obtain ⟨a, -, ha⟩ := x.th_ne (IsLocalRing.closedPoint K)
  haveI := x.P.isAb.proper
  have : JacobsonSpace x.P.A.left := LocallyOfFiniteType.jacobsonSpace x.P.A.hom
  obtain ⟨c, hc, hc'⟩ := nonempty_inter_closedPoints (Z := (Out.nonzeroLocus x.th : Set x.P.A.left)) ⟨a, ha⟩
    (Out.nonzeroLocus x.th).isOpen.isLocallyClosed
  refine ⟨Over.homMk (pointOfClosedPoint x.P.A.hom c hc') (pointOfClosedPoint_comp _ _ _), fun p => ?_⟩
  exact (pointOfClosedPoint_apply x.P.A.hom c hc' p).symm ▸ hc

theorem exists_pow_eq (hM : Out.MulNSt) (x : KeyIn K) {n : ℕ} (hn : n ≠ 0) (a : Pt x) : ∃ b : Pt x, b ^ n = a := by
  obtain ⟨hfin, -, hsurj, -, -⟩ := hM _ x.P n (Nat.pos_of_ne_zero hn)
  obtain ⟨u, hu⟩ := ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_section (k := K) (pullback.snd (Out.mulA x.P.A n).left a.left)
  have hb : (u ≫ pullback.fst (Out.mulA x.P.A n).left a.left) ≫ (Out.mulA x.P.A n).left = a.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hu]
    exact Category.id_comp _
  have hw : (u ≫ pullback.fst (Out.mulA x.P.A n).left a.left) ≫ x.P.A.hom = (𝟙_ (Over (Sp K))).hom := by
    rw [← Over.w (Out.mulA x.P.A n), ← Category.assoc, hb]
    exact Over.w a
  refine ⟨Over.homMk _ hw, ?_⟩
  have e : ∀ b : Pt x, b ^ n = b ≫ Out.mulA x.P.A n := fun b =>
    (congrArg (· ^ n) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 x.P.A) n b).symm
  rw [e]
  exact Over.OverMorphism.ext hb

theorem exists_pt_isUnit : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ : Fin 4 → Pt x), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∃ y : 𝟙_ (Over (Sp K)) ⟶ Out.powObj x.P.A 4, ∀ (p : (𝟙_ (Over (Sp K))).left) J, Good x.P.L p J → ∀ r, IsUnit (gs (y.left ≫ (alMap x al r (ξ r)).left) p (x.P.L.U (J (y.left ≫ (alMap x al r (ξ r)).left))) (x.th.f (J (y.left ≫ (alMap x al r (ξ r)).left)))) := by
  intro laws K _ _ x m al ξ hm hal
  have hm0 : m ≠ 0 := by rintro rfl; exact hm Nat.cast_zero
  have hal' := mul_transpose_eq (Int.natCast_ne_zero.2 hm0) hal
  haveI := x.P.isAb.comm
  obtain ⟨z, hz⟩ := exists_pt_mem x
  choose u hu using fun r => exists_pow_eq laws.mulN x hm0 (z * (ξ r)⁻¹)
  let v : Fin 4 → Pt x := fun c => ∏ r', u r' ^ al r' c
  let y : 𝟙_ (Over (Sp K)) ⟶ Out.powObj x.P.A 4 := (Out.powIsLimit x.P.A 4).lift (Fan.mk _ v)
  have hy : ∀ c, y ≫ Out.powPr x.P.A c = v c := fun c => (Out.powIsLimit x.P.A 4).fac (Fan.mk _ v) ⟨c⟩
  have key : ∀ r, y ≫ alMap x al r (ξ r) = z := fun r => by
    have e₁ : y ≫ alMap x al r (ξ r) = (∏ c, v c ^ al r c) * ξ r := by
      have e₀ : y ≫ toUnit _ = 𝟙 _ := toUnit_unique _ _
      simp only [alMap, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, MonObj.comp_mul,
        GrpObj.comp_zpow, MonObj.comp_one, hy, reassoc_of% e₀, Fin.prod_univ_succ, Fin.prod_univ_zero]
    have e₂ : ∏ c, v c ^ al r c = u r ^ m := by
      simp only [v, ← Finset.prod_zpow, ← zpow_mul]
      rw [Finset.prod_comm]
      have e₃ : ∀ r', ∏ c, u r' ^ (al r' c * al r c) = if r' = r then u r' ^ m else 1 := fun r' => by
        have h := congrFun (congrFun hal' r') r
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
        rw [Fin.sum_univ_four] at h
        rw [Fin.prod_univ_four, ← zpow_add, ← zpow_add, ← zpow_add, h]
        split_ifs <;> simp
      simp only [e₃, Finset.prod_ite_eq', Finset.mem_univ, if_true]
    rw [e₁, e₂, hu, inv_mul_cancel_right]
  refine ⟨y, fun p J hJ r => ?_⟩
  refine isUnit_gs_of_mem x.th _ p (hJ _) ?_
  have e : y.left ≫ (alMap x al r (ξ r)).left = z.left := congrArg (·.left) (key r)
  rw [e]
  exact hz p

end GlobalTheory.SimilNonvan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSectionBoxProductDivGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.KeyQuot

open TopologicalSpace Opposite

theorem gs_prod {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {K : Type} [Fintype K]
    (a : K → Γ(X, U)) : gs f y U (∏ k, a k) = ∏ k, gs f y U (a k) := by
  simp only [gs_eq f y U h, map_prod]

theorem exists_boxSec {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (th : L.Sec) :
    ∃ t : LB.Sec (LB.LinComb L φ (fun _ => 1)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J, Good L z J →
      sval t r z J = ∏ k, gs (r ≫ φ k) z (L.U (J (r ≫ φ k))) (th.f (J (r ≫ φ k))) := by
  have l : ∀ (j : K → L.ι) (k : K), LB.wchart L φ j ≤ φ k ⁻¹ᵁ L.U (j k) :=
    fun _ k _ hy => Set.mem_iInter.1 hy k
  let a : ∀ j : K → L.ι, Γ(Y, LB.wchart L φ j) := fun j =>
    ∏ k, (Y.presheaf.map (homOfLE (l j k)).op).hom (((φ k).app (L.U (j k))).hom (th.f (j k)))
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L φ j →
      gs r z (LB.wchart L φ j) (a j) = ∏ k, gs (r ≫ φ k) z (L.U (j k)) (th.f (j k)) := fun Z r z j hj =>
    (gs_prod r z _ hj _).trans (Finset.prod_congr rfl fun k _ =>
      (gs_res r z (l j k) hj _).trans (gs_pull r (φ k) z _ (l j k hj) _))
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z J hJ => v Z r z _ (hJ.mem φ r)⟩
  refine ((gs_res (𝟙 Y) y _ hy _).trans (v _ _ y j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
      (congrArg Units.val (gm_linComb L φ _ (𝟙 Y) y j j' hy.1 hy.2)))
      ((gs_res (𝟙 Y) y _ hy _).trans (v _ _ y j' hy.2)))).symm)
  rw [Units.coe_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [zpow_one]
  exact gs_compat th (𝟙 Y ≫ φ k) y (l j k hy.1) (l j' k hy.2)

theorem exists_sec_quot : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ : K₁ → (Y ⟶ X)) (ψ : K₂ → (Y ⟶ X)) (e : ℤ) (th : L.Sec) (w : LB.Gen (LB.LinComb L (K := K₁ ⊕ K₂) (Sum.elim φ ψ) (Sum.elim (fun _ => 1) (fun _ => -e)))), w.IsGen → ∃ s : LB.Sec (LB.LinComb L ψ (fun _ => e)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J, Good L z J → ∏ k, gs (r ≫ φ k) z (L.U (J (r ≫ φ k))) (th.f (J (r ≫ φ k))) = (val w r z J).val * sval s r z J := by
  intro X Y L hL K₁ K₂ _ _ φ ψ e th w hw
  obtain ⟨t, ht⟩ := exists_boxSec L φ th
  have hu := DVR.invGen_isGen _ _ _ _ hw
  obtain ⟨s, hs⟩ := exists_sec hL (φ' := ψ) (ε' := fun _ => e) (by
    intro U _ h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Category.id_comp, zpow_one,
      zpow_neg, Finset.prod_inv_distrib, mul_inv, mul_inv_cancel_left, inv_inv]) (pullMulSec t (𝟙 Y) _ hu)
  refine ⟨s, fun Z r z J hJ => ?_⟩
  rw [hs Z r z J hJ, sval_pullMulSec t (𝟙 Y) _ hu r z hJ, Category.comp_id, ht Z r z J hJ, val_inv,
    mul_left_comm, Units.mul_inv, _root_.mul_one]

end GlobalTheory.KeyQuot
end
end

