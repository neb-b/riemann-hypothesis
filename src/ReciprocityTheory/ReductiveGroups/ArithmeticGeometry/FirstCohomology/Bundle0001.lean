module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem exists_gen_move (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : PGen w)
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (φ' : K → (Y' ⟶ X')) (ε : K → ℤ) (h : Y' ⟶ Y)
    (hc : ∀ k, φ' k ≫ F = h ≫ φ k) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧ PMaps w φ' φ ε a t h := by
  classical
  let O : (K → L'.ι) → (K → L.ι) → Y'.Opens := fun q p =>
    LB.wchart L' φ' q ⊓ LB.wchart (L.pull F) φ' (fun k _ => p k)
  have le1 : ∀ q p k, O q p ≤ φ' k ⁻¹ᵁ ((L.pull F).U (fun _ => p k) ⊓ L'.U (q k)) := fun q p k y hy =>
    ⟨Set.mem_iInter.1 hy.2 k, Set.mem_iInter.1 hy.1 k⟩
  have le2 : ∀ q p, O q p ≤ h ⁻¹ᵁ LB.wchart L φ p := fun q p y hy => Set.mem_iInter.2 fun k => by
    have := mem_pull.1 (Set.mem_iInter.1 hy.2 k)
    show φ k (h y) ∈ L.U (p k)
    rw [pt_eq hc]; exact this
  let v : ∀ q p, Γ(Y', O q p)ˣ := fun q p =>
    (∏ k, res (le1 q p k) (pullU (φ' k) _ (w.s (fun _ => p k, q k))) ^ ε k)⁻¹ * res (le2 q p) (pullU h _ (t.s p))
  have germ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) q p, r z ∈ O q p →
      gm r z (O q p) (v q p) = (∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k)⁻¹ * gm (r ≫ h) z (LB.wchart L φ p) (t.s p) := by
    intro Z r z q p hz
    have m2 := le2 q p hz
    show gm r z (O q p) ((∏ k, _)⁻¹ * _) = _
    rw [map_mul, map_inv, map_prod]
    refine congrArg₂ (· * ·) (congrArg (·⁻¹) (Finset.prod_congr rfl fun k _ => ?_))
      ((gm_res r z (le2 q p) hz _).trans (gm_pull r h z _ m2 _))
    have m := le1 q p k hz
    exact (map_zpow _ _ _).trans (congrArg (· ^ ε k) ((gm_res r z (le1 q p k) hz _).trans (gm_pull r (φ' k) z _ m _)))
  have memO : ∀ q (y : Y'), y ∈ LB.wchart L' φ' q → ∃ p, y ∈ O q p := fun q y hy => by
    choose p hp using fun k => exists_chart hL (F (φ' k y))
    exact ⟨p, hy, Set.mem_iInter.2 fun k => mem_pull.2 (hp k)⟩
  have glue : ∀ q, ∃ s : Γ(Y', LB.wchart L' φ' q)ˣ, ∀ p, res (inf_le_left : O q p ≤ _) s = v q p := by
    intro q
    refine glue_unit _ (O q) (fun p => inf_le_left) (fun y hy => ?_) (v q) fun p p' y hy => ?_
    · obtain ⟨p, hp⟩ := memO q y hy
      exact Opens.mem_iSup.2 ⟨p, hp⟩
    · rw [germ _ _ y q p hy.1, germ _ _ y q p' hy.2]
      have hp : ∀ k, F (φ' k y) ∈ L.U (p k) := fun k => mem_pull.1 (Set.mem_iInter.1 hy.1.2 k)
      have hp' : ∀ k, F (φ' k y) ∈ L.U (p' k) := fun k => mem_pull.1 (Set.mem_iInter.1 hy.2.2 k)
      have hq : ∀ k, φ' k y ∈ L'.U (q k) := fun k => Set.mem_iInter.1 hy.1.1 k
      have e1 : ∀ k, gw w (𝟙 Y' ≫ φ' k) y (p k) (q k) =
          gm (φ' k ≫ F) y _ (L.g (p k) (p' k)) * gw w (𝟙 Y' ≫ φ' k) y (p' k) (q k) := fun k => by
        rw [Category.id_comp, hw _ (φ' k) y (p k) (p' k) (q k) (q k) (hp k) (hp' k) (hq k) (hq k),
          gm_self hL' _ y (hq k), inv_one, mul_one]
      have e2 : trF φ ε (𝟙 Y' ≫ h) y p p' = ∏ k, gm (φ' k ≫ F) y _ (L.g (p k) (p' k)) ^ ε k :=
        Finset.prod_congr rfl fun k _ => by rw [Category.id_comp, ← hc k]
      rw [gen_trans ht (𝟙 Y' ≫ h) y (le2 q p hy.1) (le2 q p' hy.2), e2]
      simp only [e1, mul_zpow, Finset.prod_mul_distrib, mul_inv_rev]
      rw [mul_assoc, inv_mul_cancel_left]
  choose s hs using glue
  have vals : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) q p, r z ∈ O q p →
      gm r z (LB.wchart L' φ' q) (s q) =
        (∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k)⁻¹ * gm (r ≫ h) z (LB.wchart L φ p) (t.s p) := by
    intro Z r z q p hz
    rw [← gm_res r z (inf_le_left : O q p ≤ _) hz, hs q p, germ Z r z q p hz]
  refine ⟨⟨s⟩, fun q q' => unit_ext fun y hy => ?_, fun Z r z p q hp hq => ?_⟩
  · have hq : ∀ k, φ' k y ∈ L'.U (q k) := fun k => Set.mem_iInter.1 hy.1 k
    have hq' : ∀ k, φ' k y ∈ L'.U (q' k) := fun k => Set.mem_iInter.1 hy.2 k
    choose p hp using fun k => exists_chart hL (F (φ' k y))
    have m : y ∈ O q p := ⟨hy.1, Set.mem_iInter.2 fun k => mem_pull.2 (hp k)⟩
    have m' : y ∈ O q' p := ⟨hy.2, Set.mem_iInter.2 fun k => mem_pull.2 (hp k)⟩
    rw [gm_res _ y _ hy, map_mul, gm_res _ y _ hy]
    show gm (𝟙 Y') y (LB.wchart L' φ' q) (s q) = gm (𝟙 Y') y (LB.wchart L' φ' q ⊓ LB.wchart L' φ' q')
      ((LB.LinComb L' φ' ε).g q q') * gm (𝟙 Y') y (LB.wchart L' φ' q') (s q')
    rw [gm_linComb L' φ' ε (𝟙 Y') y q q' hy.1 hy.2, vals _ _ y q p m, vals _ _ y q' p m']
    have e3 : ∀ k, gw w (𝟙 Y' ≫ φ' k) y (p k) (q k) =
        (gm (𝟙 Y' ≫ φ' k) y _ (L'.g (q k) (q' k)))⁻¹ * gw w (𝟙 Y' ≫ φ' k) y (p k) (q' k) := fun k => by
      rw [Category.id_comp, hw _ (φ' k) y (p k) (p k) (q k) (q' k) (hp k) (hp k) (hq k) (hq' k),
        gm_self hL _ y (hp k), one_mul]
    simp only [e3, mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib, mul_inv_rev, inv_inv]
    exact (congrArg (· * _) (mul_comm _ _)).trans (mul_assoc _ _ _)
  · have m : r z ∈ O q p := ⟨Set.mem_iInter.2 hq, Set.mem_iInter.2 fun k => mem_pull.2 (hp k)⟩
    show _ = _ * gm r z (LB.wchart L' φ' q) (s q)
    rw [vals Z r z q p m, mul_inv_cancel_left]

end ReciprocityTheory.ChartRestriction.G.H1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

def OneCStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso →
    letI := H.starRing
    ∀ (α : 𝓞 E) (N : ℕ), 1 ≤ N → α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) →
      IsUnit ((N : ℕ) : V) →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)),
      ValOver ϖ F v →
    ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ P.A.A) (fun a g => g ≫ P.oA.act a)
        (fun n g g' c => WeilIs P.A.A P.A.L n g g' (unitOn c))),
    ∀ θ : Fam P.D.toPre F 1, NuGe P.D Q F v 1 θ 0 →
      (∃ (σ : P.D.toPre.SecB 1 0)
        (σF : LB.Sec (LB.LinComb P.D.toPre.P.L (DegPre.famφ P.D.toPre F 0) (DegPre.famε 1))),
        GeneratorPullback.SecScal P.D.toPre.P.L (DegPre.famφ P.D.toPre F 0) (DegPre.famε 1) σF
          (P.D.toPre.famφB 0) (DegPre.famε 1) σ (DegPre.prB P.D.toPre F).left 1 ∧
        (∀ j, (θ.s 0).f j = σF.f j) ∧
        ¬ ∃ σ' : P.D.toPre.SecB 1 0, ∀ j, σ.f j = constFn P.D.toPre.P.A.hom _ ϖ * σ'.f j) →
    ∀ θα : Fam P.D.toPre F (1 * N), PullAl P.D F P.oD α 1 N θ θα →
    ∀ s : Fam P.D.toPre F (1 * N), NuGe P.D Q F v (1 * N) s 0 →
      ∃ (m : ℕ) (p : Fin m → QkPt P.D.toPre F (1 * N)) (x : Fin m → (TFK (R := V) F ⟶ P.A.A))
        (w : ∀ i, LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p i).g.b)
          (DegPre.lineε (1 * N))))
        (ζ : Fin m → F) (t : Fin m → Fam P.D.toPre F (1 * N)) (a : Fin m → F),
        (∀ i, P.ToA F (1 * N) (p i) (x i)) ∧
        (∀ i, x i ≫ P.oA.act (star α) = 1) ∧
        (∀ i, (w i).IsGen ∧ ζ i ≠ 0 ∧ FinOrd P.D F (1 * N) (p i) (w i) (ζ i)) ∧
        (∀ i, ∃ t' : Fam P.D.toPre F (1 * N),
          PhiRel P.D.toPre F (1 * N) (p i) (w i) θα t' ∧ Fam.IsSmul P.D.toPre F (ζ i) t' (t i)) ∧
        (∀ i, (0 : WithTop ℚ) ≤ v (a i)) ∧
        s = ∑ i, a i • t i

end ReciprocityTheory.ChartRestriction.G.H1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X Y Z : Scheme.{0}}

def secAdd {M : LB Y} (s t : LB.Sec M) : LB.Sec M where
  f i := s.f i + t.f i
  compat i j := by rw [map_add (f := _), map_add (f := _), s.compat, t.compat, mul_add]

def secZero (M : LB Y) : LB.Sec M where
  f _ := 0
  compat _ _ := by rw [map_zero, map_zero, mul_zero]

def secCMul {M : LB Y} {V : Y.Opens} (hV : ∀ i, M.U i ≤ V) (c : Γ(Y, V)) (s : LB.Sec M) : LB.Sec M where
  f i := (Y.presheaf.map (homOfLE (hV i)).op).hom c * s.f i
  compat i j := fn_ext fun y hy => by
    have e := congrArg (gs (𝟙 Y) y (M.U i ⊓ M.U j)) (s.compat i j)
    rw [gs_res (𝟙 Y) y inf_le_left hy, gs_mul (𝟙 Y) y _ hy, gs_res (𝟙 Y) y inf_le_right hy] at e
    rw [gs_res (𝟙 Y) y inf_le_left hy, gs_mul (𝟙 Y) y _ hy.1, gs_res (𝟙 Y) y (hV i) hy.1, e,
      gs_mul (𝟙 Y) y _ hy, gs_res (𝟙 Y) y inf_le_right hy, gs_mul (𝟙 Y) y _ hy.2, gs_res (𝟙 Y) y (hV j) hy.2]
    ring

variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

def pullSec {Y' : Scheme.{0}} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) :
    LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε) :=
  have l : ∀ j : K → L.ι, LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  { f := fun j => (Y'.presheaf.map (homOfLE (l j)).op).hom ((h.app _).hom (s.f j))
    compat := fun j j' => fn_ext fun y hy => by
      have v : ∀ j : K → L.ι, y ∈ LB.wchart L (fun k => h ≫ φ k) j →
          gs (𝟙 Y') y _ ((Y'.presheaf.map (homOfLE (l j)).op).hom ((h.app _).hom (s.f j))) =
            gs (𝟙 Y' ≫ h) y (LB.wchart L φ j) (s.f j) := fun j hj =>
        (gs_res _ y _ hj _).trans (gs_pull _ h y _ (l j hj) _)
      refine ((gs_res (𝟙 Y') y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y') y _ hy _ _).trans
        (congrArg₂ (· * ·) ((gs_unit (𝟙 Y') y _ hy _).trans
          (congrArg Units.val (gm_linComb L _ _ (𝟙 Y') y j j' hy.1 hy.2))) ((gs_res (𝟙 Y') y _ hy _).trans (v j' hy.2)))).symm)
      rw [sec_trans s (𝟙 Y' ≫ h) y (l j hy.1) (l j' hy.2)]
      simp only [trF, Category.assoc] }

theorem sval_pullSec {Y' : Scheme.{0}} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (pullSec s h) r z J = sval s (r ≫ h) z J := by

  have hm1 := hJ.mem (fun k => h ≫ φ k) r
  have hm2 := hJ.mem φ (r ≫ h)
  simp only [Category.assoc] at hm2
  unfold sval
  simp only [Category.assoc]
  exact (gs_res r z _ hm1 _).trans (gs_pull r h z _ hm2 _)

def mulSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (t : LB.Sec (LB.LinComb L φ' ε')) :
    LB.Sec (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')) :=
  have l₁ : ∀ j : K ⊕ K' → L.ι, LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ (j ∘ Sum.inl) :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)
  have l₂ : ∀ j : K ⊕ K' → L.ι, LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ' (j ∘ Sum.inr) :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)
  { f := fun j => (Y.presheaf.map (homOfLE (l₁ j)).op).hom (s.f (j ∘ Sum.inl)) *
      (Y.presheaf.map (homOfLE (l₂ j)).op).hom (t.f (j ∘ Sum.inr))
    compat := fun j j' => fn_ext fun y hy => by
      have v : ∀ j : K ⊕ K' → L.ι, y ∈ LB.wchart L (Sum.elim φ φ') j →
          gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (l₁ j)).op).hom (s.f (j ∘ Sum.inl)) *
            (Y.presheaf.map (homOfLE (l₂ j)).op).hom (t.f (j ∘ Sum.inr))) =
          gs (𝟙 Y) y (LB.wchart L φ (j ∘ Sum.inl)) (s.f (j ∘ Sum.inl)) *
            gs (𝟙 Y) y (LB.wchart L φ' (j ∘ Sum.inr)) (t.f (j ∘ Sum.inr)) := fun j hj =>
        (gs_mul _ y _ hj _ _).trans (congrArg₂ (· * ·) (gs_res _ y _ hj _) (gs_res _ y _ hj _))
      refine ((gs_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
        (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
          (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2))) ((gs_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)
      rw [sec_trans s (𝟙 Y) y (l₁ j hy.1) (l₁ j' hy.2), sec_trans t (𝟙 Y) y (l₂ j hy.1) (l₂ j' hy.2),
        Fintype.prod_sum_type, Units.val_mul, mul_mul_mul_comm]
      simp only [trF, Sum.elim_inl, Sum.elim_inr]
      rfl }

theorem sval_mulSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (t : LB.Sec (LB.LinComb L φ' ε')) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (mulSec s t) r z J = sval s r z J * sval t r z J := by

  have hm := hJ.mem (Sum.elim φ φ') r
  unfold sval
  exact (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res r z _ hm _) (gs_res r z _ hm _))

def powSec {I : Type} [Fintype I] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : I → LB.Sec (LB.LinComb L φ ε)) :
    LB.Sec (LB.LinComb L (fun p : I × K => φ p.2) (fun p => ε p.2)) :=
  have l : ∀ (j : I × K → L.ι) (i : I), LB.wchart L (fun p : I × K => φ p.2) j ≤ LB.wchart L φ (fun k => j (i, k)) :=
    fun _ i _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)
  { f := fun j => ∏ i, (Y.presheaf.map (homOfLE (l j i)).op).hom ((s i).f (fun k => j (i, k)))
    compat := fun j j' => fn_ext fun y hy => by
      have v : ∀ j : I × K → L.ι, y ∈ LB.wchart L (fun p : I × K => φ p.2) j →
          gs (𝟙 Y) y _ (∏ i, (Y.presheaf.map (homOfLE (l j i)).op).hom ((s i).f (fun k => j (i, k)))) =
          ∏ i, gs (𝟙 Y) y (LB.wchart L φ (fun k => j (i, k))) ((s i).f (fun k => j (i, k))) := fun j hj => by
        rw [gs_eq (𝟙 Y) y _ hj, map_prod, map_prod]
        exact Finset.prod_congr rfl fun i _ => (gs_eq (𝟙 Y) y _ hj _).symm.trans (gs_res _ y _ hj _)
      refine ((gs_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
        (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
          (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2))) ((gs_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)
      have e : ∀ i, gs (𝟙 Y) y (LB.wchart L φ (fun k => j (i, k))) ((s i).f (fun k => j (i, k))) =
          (trF φ ε (𝟙 Y) y (fun k => j (i, k)) (fun k => j' (i, k))).val *
            gs (𝟙 Y) y (LB.wchart L φ (fun k => j' (i, k))) ((s i).f (fun k => j' (i, k))) :=
        fun i => sec_trans (s i) (𝟙 Y) y (l j i hy.1) (l j' i hy.2)
      rw [Finset.prod_congr rfl fun i _ => e i, Finset.prod_mul_distrib, ← Units.coe_prod]
      congr 2
      simp only [trF]
      rw [Fintype.prod_prod_type] }

theorem sval_powSec {I : Type} [Fintype I] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : I → LB.Sec (LB.LinComb L φ ε))
    (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (powSec s) r z J = ∏ i, sval (s i) r z J := by

  have hm := hJ.mem (fun p : I × K => φ p.2) r
  unfold sval
  dsimp only [powSec]
  refine (gs_eq r z _ hm _).trans ?_
  erw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun i _ => (gs_eq r z _ hm _).symm.trans (gs_res r z _ hm _)

theorem germ_eq_sval {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (y : Y)
    {J : (Y ⟶ X) → L.ι} (hJ : Good L y J) (j : K → L.ι) (hy : y ∈ LB.wchart L φ j) :
    (Y.presheaf.germ (LB.wchart L φ j) y hy).hom (s.f j) =
      (trF φ ε (𝟙 Y) y j (fun k => J (𝟙 Y ≫ φ k))).val * sval s (𝟙 Y) y J := by
  have h1 := sec_trans s (𝟙 Y) y (j' := fun k => J (𝟙 Y ≫ φ k)) hy (hJ.mem φ (𝟙 Y))
  erw [gs_eq (𝟙 Y) y _ hy] at h1
  unfold sval
  rw [← h1]
  first | rfl | simp

theorem isUnit_sval {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (k : (LB.LinComb L φ ε).ι) (hk : r z ∈ Y.basicOpen (s.f k)) :
    IsUnit (sval s r z J) := by

  have hkU : r z ∈ LB.wchart L φ k := Y.basicOpen_le _ hk
  have hm := hJ.mem φ r
  unfold sval
  rw [sec_trans s r z hm hkU]
  refine (Units.isUnit _).mul ?_
  erw [gs_eq r z _ hkU]
  have hz : z ∈ Z.basicOpen ((r.app _).hom (s.f k)) := by
    rw [← Scheme.preimage_basicOpen]; exact hk
  exact (Z.mem_basicOpen _ z hkU).1 hz

end ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
end
end

