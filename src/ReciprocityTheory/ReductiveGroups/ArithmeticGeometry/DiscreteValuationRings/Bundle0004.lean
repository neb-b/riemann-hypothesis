module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenLevel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

lemma resTop_scal {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (W : Y.Opens)
    (r : R) : resTop W (scal p r) = toW p W r := rfl

theorem sec_div {R : Type} [CommRing R] [IsDomain R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) [Flat p]
    {M : LB Y} (s : LB.Sec M) {a : R} (ha : a ≠ 0) {J : Ideal R} (hJ : J ≤ Ideal.span {a})
    (h0 : ∀ j, (pullback.fst p (tq J)).app _ (s.f j) = 0) :
    ∃ g : LB.Sec M, ∀ j, s.f j = toW p _ a * g.f j := by
  choose g hg using fun j => exists_div p ha hJ (M.U j) (s.f j) (h0 j)
  refine ⟨⟨g, fun i j => ?_⟩, hg⟩
  apply sub_eq_zero.1
  apply toW_mul_eq_zero p _ ha
  have c := s.compat i j
  rw [hg i, hg j, map_mul, map_mul, toW_res, toW_res] at c
  rw [mul_sub, sub_eq_zero, c]
  ring

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

lemma thickMap_fst (e : ℕ) : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left := by
  unfold thickMap fstG pullback.map
  simp only [Over.homMk_left]
  try simp

lemma pG_struct {e : ℕ} (g : GtCoord I D.toPre e G) :
    g.pG.left ≫ D.toPre.P.A.hom = (fstG I e G).left ≫ G.hom :=
  (Over.w g.pG).trans (Over.w (fstG I e G)).symm

end ReciprocityTheory.ChartRestriction.G.DVR.TG

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

lemma app_eq_zero_of_comp {X Y Z : Scheme.{0}} {f : X ⟶ Z} {g : X ⟶ Y} {h : Y ⟶ Z} (hf : g ≫ h = f)
    (W : Z.Opens) (x : Γ(Z, W)) (hx : g.app (h ⁻¹ᵁ W) (h.app W x) = 0) : f.app W x = 0 := by
  subst hf
  first
  | exact hx
  | (rw [Scheme.comp_app]; exact hx)
  | (simp only [Scheme.comp_app, CommRingCat.comp_apply]; exact hx)

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def thickO (e : ℕ) : (Over.map (thick R I e)).obj (thickObj R I e G) ⟶
    (Over.map (thick R I (e + 1))).obj (thickObj R I (e + 1) G) :=
  Over.homMk (thickMap R I e G) (by
    show thickMap R I e G ≫ pullback.snd G.hom (thick R I (e + 1)) ≫ thick R I (e + 1) =
      pullback.snd G.hom (thick R I e) ≫ thick R I e
    rw [thickMap, pullback.lift_snd_assoc, Category.assoc, thickTrans_comp])

lemma thickO_pG (U : UnifPre I D A G) (e : ℕ) : thickO e ≫ (U.gt (e + 1)).pG = (U.gt e).pG :=
  Over.OverMorphism.ext (U.gt_q e)

lemma Oφ_thick (U : UnifPre I D A G) (e : ℕ) (α : D.toPre.X) (k : Fin 4) :
    thickMap R I e G ≫ D.toPre.Oφ (U.gt (e + 1)).pG α k = D.toPre.Oφ (U.gt e).pG α k := by
  have := WeightPf.Oφ_comp (thickO (G := G) (I := I) e) (U.gt (e + 1)).pG α k
  rw [thickO_pG] at this
  exact this

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm

def ValOver {V : Type} [CommRing V] [IsDomain V] (ϖ : V) (F : Type) [Field F]
    [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) : Prop :=
  ∀ (c : FractionRing V) (n : ℤ), HasVal ϖ c n → v (algebraMap (FractionRing V) F c) = ((n : ℚ) : WithTop ℚ)

section Defs

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ)
  (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ))

def VGe (k : ℕ) (α : D.toPre.X)
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))) (r : ℚ) : Prop :=
  ∃ (n : ℕ) (a : Fin n → F) (σ : Fin n → D.toPre.SecB k α)
    (σF : Fin n → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))),
    (∀ i, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (σF i)
        (D.toPre.famφB α) (DegPre.famε k) (σ i) (DegPre.prB D.toPre F).left 1) ∧
    (∀ i, ((r : ℚ) : WithTop ℚ) ≤ v (a i)) ∧
    ∀ j, s.f j = ∑ i, DegPre.constBF D.toPre F (a i) _ * (σF i).f j

def NuGe (k : ℕ) (s : Fam D.toPre F k) (r : ℚ) : Prop :=
  ∀ χ : D.toPre.X, VGe D F v k χ (s.s χ) (r + (Q χ : ℚ) / k)

variable {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X]

def aF (oa : D.toPre.OAct O) (a : O) : DegPre.BF D.toPre F ⟶ DegPre.BF D.toPre F :=
  lift (fst _ _) (DegPre.prB D.toPre F ≫ oa.onB.act a)

def pullφ (oa : D.toPre.OAct O) (a : O) (χ : D.toPre.X) :
    Fin 4 ⊕ Fin 4 → ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left) :=
  Sum.elim (DegPre.famφ D.toPre F (star a • χ)) (fun i => (aF D F oa a).left ≫ DegPre.famφ D.toPre F χ i)

def pullε (k N : ℕ) : Fin 4 ⊕ Fin 4 → ℤ :=
  Sum.elim (DegPre.famε (k * N)) (fun i => - DegPre.famε k i)

def PullAl (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (s : Fam D.toPre F k)
    (s' : Fam D.toPre F (k * N)) : Prop :=
  (∀ χ : D.toPre.X, ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N)), u.IsGen ∧
    LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1)))
        (jFK (R := V) F)) ∧
    GeneratorPullback.SecRel D.toPre.P.L (DegPre.famφ D.toPre F (star a • χ)) (DegPre.famε (k * N))
      (s'.s (star a • χ)) (DegPre.famφ D.toPre F χ) (DegPre.famε k) (s.s χ) (aF D F oa a).left
      (pullφ D F oa a χ) (pullε k N) u) ∧
  ∀ β : D.toPre.X, (∀ χ, β ≠ star a • χ) → ∀ j, (s'.s β).f j = 0

def FinOrd (k : ℕ) (p : QkPt D.toPre F k)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (ζ : F) :
    Prop :=
  ∃ M : ℕ, 1 ≤ M ∧ ∀ (ss : Fin (M + 1) → Fam D.toPre F k) (ts : Fin M → Fam D.toPre F k),
    (∀ i : Fin M, PhiRel D.toPre F k p w (ss i.castSucc) (ts i) ∧
      Fam.IsSmul D.toPre F ζ (ts i) (ss i.succ)) →
    ∀ α j, ((ss (Fin.last M)).s α).f j = ((ss 0).s α).f j

def Val0 (k : ℕ) (α : D.toPre.X)
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))) (x : F) : Prop :=
  ∃ τ : LB.Gen (LB.LinComb D.toPre.P.L
      (fun i => (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i) (DegPre.famε k)),
    τ.IsGen ∧
    LB.Gen.Corr D.toPre.P.L _ _ _ _ τ
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK k) (jFK (R := V) F)) ∧
    ∀ j, ((TF (R := V) F).left.presheaf.map (homOfLE
        ((fun _ hy => Set.mem_iInter.2 fun i => Set.mem_iInter.1 hy i) :
          LB.wchart D.toPre.P.L (fun i => (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i) j ≤
            (DegPre.zF D.toPre F).left ⁻¹ᵁ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F α) j)).op).hom
        (((DegPre.zF D.toPre F).left.app _).hom (s.f j)) =
      ((TF (R := V) F).left.presheaf.map (homOfLE le_top).op).hom
          ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom x) * (τ.s j).val

def SumTo (x : D.toPre.X → F) (w : F) : Prop :=
  ∀ q : ℚ, ∃ S : Finset D.toPre.X, ∀ T : Finset D.toPre.X, S ⊆ T →
    ((q : ℚ) : WithTop ℚ) ≤ v (w - ∑ α ∈ T, x α)

def ValAt0 (k : ℕ) (s : Fam D.toPre F k) (w : F) : Prop :=
  ∃ x : D.toPre.X → F, (∀ α, Val0 D F k α (s.s α) (x α)) ∧ SumTo D F v x w

def FamIsAdd {k : ℕ} (s s' s'' : Fam D.toPre F k) : Prop :=
  ∀ (α : D.toPre.X) (j : Fin 4 → D.toPre.P.L.ι), (s''.s α).f j = (s.s α).f j + (s'.s α).f j

end Defs

def ValuationMinRepresentatives : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ k : ℕ, 1 ≤ k → ∀ S : Finset D.toPre.X, (∀ χ : D.toPre.X, ∃ α ∈ S, ∃ m0, χ = α + k • m0) →
      ∀ (s : Fam D.toPre F k) (r : ℚ),
        NuGe D Q F v k s r ↔ ∀ α ∈ S, VGe D F v k α (s.s α) (r + (Q α : ℚ) / k)

def PositiveValuationMaximalIdeal : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)),
    ValOver ϖ F v →
    ∀ k : ℕ, 1 ≤ k → ∀ s : Fam D.toPre F k, NuGe D Q F v k s 0 →
      ((∃ r : ℚ, 0 < r ∧ NuGe D Q F v k s r) ↔
        ∃ (ζ : F) (s' : Fam D.toPre F k), (0 : WithTop ℚ) < v ζ ∧ NuGe D Q F v k s' 0 ∧
          Fam.IsSmul D.toPre F ζ s' s)

def FiniteOrderValuationInvariance : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ k : ℕ, 1 ≤ k → ∀ (p : QkPt D.toPre F k)
      (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))),
      w.IsGen → ∀ ζ : F, ζ ≠ 0 → FinOrd D F k p w ζ →
      ∀ s t s' : Fam D.toPre F k, PhiRel D.toPre F k p w s t → Fam.IsSmul D.toPre F ζ t s' →
        ∀ r : ℚ, NuGe D Q F v k s r ↔ NuGe D Q F v k s' r

def ValuationBoundAtZero : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ m : ℕ, 1 ≤ m → ∀ (R' : ℕ) (β : D.toPre.X) (s : Fam D.toPre F m),
      (∀ α : D.toPre.X, (∀ z : D.toPre.X, α ≠ β + R' • z) → ∀ j, (s.s α).f j = 0) →
      NuGe D Q F v m s 0 → ∀ w : F, ValAt0 D F v m s w →
      ∀ q : ℚ, (∀ z : D.toPre.X, q ≤ (Q (β + R' • z) : ℚ) / m) → ((q : ℚ) : WithTop ℚ) ≤ v w

def GermIntegrality : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (k : ℕ)
      (s : Fam D.toPre F k), NuGe D Q F v k s 0 → ∀ χ, VGe D F v k χ (s.s χ) 0

def UUStatement : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    (IsAlgClosed F ∨ ∃ d : ℕ, 1 ≤ d ∧ ∀ x : F, x ≠ 0 → ∃ n : ℤ, v x = (((n : ℚ) / d : ℚ) : WithTop ℚ)) →
    ∀ k : ℕ, 1 ≤ k → ∃ b : Fin (k ^ (D.toPre.rank + D.toPre.P.g)) → Fam D.toPre F k,
      LinearIndependent F b ∧ (∀ i, NuGe D Q F v k (b i) 0) ∧
      ∀ s : Fam D.toPre F k, NuGe D Q F v k s 0 ↔
        ∃ c : Fin (k ^ (D.toPre.rank + D.toPre.P.g)) → F, (∀ i, (0 : WithTop ℚ) ≤ v (c i)) ∧
          s = ∑ i, c i • b i

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

