module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasTorusWeightIffTorusEquivariant
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.PureWt

theorem cf_diag {A R X : Type} [CommRing A] [CommRing R] [AddCommGroup X]
    {f : A →+* R} {m : Multiplicative X →* R}
    (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f m (fun _ _ => Commute.all _ _)))
    (σ : R →+ R) (κ : X → A)
    (hσ : ∀ b ψ, σ (f b * m (Multiplicative.ofAdd ψ)) = f (κ ψ) * (f b * m (Multiplicative.ofAdd ψ)))
    (χ : X) (s : R) : WtPart.cf hb χ (σ s) = κ χ * WtPart.cf hb χ s := by
  obtain ⟨a, rfl⟩ := hb.2 s
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp only [map_zero, WtPart.cf_zero, mul_zero]
  | add x y hx hy => simp only [map_add (f := _), WtPart.cf_add, mul_add, hx, hy]
  | single ψ b =>
    rw [AddMonoidAlgebra.liftNCRingHom_single, hσ, ← _root_.mul_assoc, ← map_mul, WtPart.cf_mono,
      WtPart.cf_mono]
    split_ifs with h
    · rw [h]
    · rw [mul_zero]

theorem exists_char_ne {k X K : Type} [Field k] [Infinite k] [AddCommGroup X] (b : Module.Basis K ℤ X)
    {χ α : X} (h : χ ≠ α) :
    ∃ t : Multiplicative X →* kˣ, t (Multiplicative.ofAdd χ) ≠ t (Multiplicative.ofAdd α) := by
  obtain ⟨i, hi⟩ : ∃ i, b.repr χ i ≠ b.repr α i := by
    by_contra hn
    push Not at hn
    exact h (b.repr.injective (Finsupp.ext hn))
  have hn : (b.repr χ i - b.repr α i).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (sub_ne_zero.2 hi)
  obtain ⟨x, hx⟩ : ∃ x : kˣ, x ^ (b.repr χ i - b.repr α i).natAbs ≠ 1 := by
    by_contra hc
    push Not at hc
    generalize (b.repr χ i - b.repr α i).natAbs = n at hn hc
    have : NeZero n := ⟨hn⟩
    have : Finite kˣ := Finite.of_surjective (fun x : rootsOfUnity n k => (x : kˣ))
      fun x => ⟨⟨x, (mem_rootsOfUnity n x).2 (hc x)⟩, rfl⟩
    have : Finite k := Finite.of_surjective (fun x : Option kˣ => x.elim (0 : k) Units.val) fun x => by
      by_cases hx : x = 0
      · exact ⟨none, hx.symm⟩
      · exact ⟨some (Units.mk0 x hx), rfl⟩
    exact not_finite k
  refine ⟨(zpowersHom kˣ x).comp (AddMonoidHom.toMultiplicative (b.coord i).toAddMonoidHom), fun e => hx ?_⟩
  have e' : x ^ (b.repr χ i) = x ^ (b.repr α i) := e
  rw [pow_natAbs_eq_one, zpow_sub, e', mul_inv_cancel]

variable {S : Scheme.{0}} {E : SplitExt S} {G : Over S} [GrpObj G] (D : E.GtDatum G)

theorem translate_mem {Z : Over S} (τ : Z ⟶ splitTorus S E.X) (g : Z ⟶ G) (V : E.B.left.Opens) (z : Z.left)
    (hz : g.left z ∈ D.q.left ⁻¹ᵁ V) : ((τ ≫ D.i) * g).left z ∈ D.q.left ⁻¹ᵁ V :=
  haveI := D.q_hom
  GtBaseChange.translate_mem D.q D.i D.isKernel τ g V z hz

theorem gm_points {X : Type} [AddCommGroup X] {Z : Over S} (τ : Z ⟶ splitTorus S X) (z : Z.left) (χ : X) :
    gm (𝟙 Z.left) z ⊤ (splitTorusPointsEquiv S X Z τ (Multiplicative.ofAdd χ)) =
      gm τ.left z ⊤ (charUnit S X χ) := by
  apply Units.ext
  rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial, splitTorusPointsEquiv_val]
  rfl

theorem hasWt_mono (j : E.ChartIdx) (V : E.B.left.Opens) (h : V ≤ E.chart j) (c : Γ(E.B.left, V)) (χ : E.X) :
    UFib.HasWt D.i (D.q.left ⁻¹ᵁ V)
      ((D.q.left.app V).hom c * WtPart.mono D j V h (Multiplicative.ofAdd χ)) χ := by
  intro Z τ g z hz
  have hz' := translate_mem D τ g V z hz
  set v := AddMonoidHom.toMultiplicativeLeft
    (E.basis.constr ℤ (fun k => Additive.ofMul
      (res (Scheme.Hom.preimage_mono D.q.left h) (D.u j k)))).toAddMonoidHom with hv
  let A : Multiplicative E.X →* (Z.left.presheaf.stalk z)ˣ := (gm ((τ ≫ D.i) * g).left z _).comp v
  let C : Multiplicative E.X →* (Z.left.presheaf.stalk z)ˣ :=
    (gm (𝟙 Z.left) z ⊤).comp (splitTorusPointsEquiv S E.X Z τ) * (gm g.left z _).comp v
  have hAC : (MonoidHom.toAdditiveRight A).toIntLinearMap = (MonoidHom.toAdditiveRight C).toIntLinearMap := by
    refine E.basis.ext fun k => ?_
    have hvk : v (Multiplicative.ofAdd (E.basis k)) = res (Scheme.Hom.preimage_mono D.q.left h) (D.u j k) := by
      simp [hv]
    refine congrArg Additive.ofMul ?_
    change gm _ z _ (v (Multiplicative.ofAdd (E.basis k))) =
      gm (𝟙 Z.left) z ⊤ (splitTorusPointsEquiv S E.X Z τ (Multiplicative.ofAdd (E.basis k))) *
        gm _ z _ (v (Multiplicative.ofAdd (E.basis k)))
    rw [hvk, gm_points, gm_res _ z _ hz, gm_res _ z _ hz']
    exact (GtBaseChange.hasWeight_iff D.i _ _ _ (D.act_le _) _).2 (D.equiv j k) Z τ g z (h hz)
  have e : gm ((τ ≫ D.i) * g).left z _ (v (Multiplicative.ofAdd χ)) =
      gm (𝟙 Z.left) z ⊤ (splitTorusPointsEquiv S E.X Z τ (Multiplicative.ofAdd χ)) *
        gm g.left z _ (v (Multiplicative.ofAdd χ)) :=
    congrArg (fun φ => Additive.toMul (φ χ)) hAC
  have em : WtPart.mono D j V h (Multiplicative.ofAdd χ) = (v (Multiplicative.ofAdd χ)).val := rfl
  rw [em, gs_mul _ z _ hz, gs_mul _ z _ hz', gs_unit _ z _ hz, gs_unit _ z _ hz', e, gm_points,
    gs_pull _ _ z V hz, gs_pull _ _ z V hz', TorusTranslate.translate_comp_q, Units.val_mul]
  ring

theorem translate_appLE (V : E.B.left.Opens) (τ : G ⟶ splitTorus S E.X)
    (hle : D.q.left ⁻¹ᵁ V ≤ ((τ ≫ D.i) * 𝟙 G).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V))
    (s : Γ(G.left, D.q.left ⁻¹ᵁ V)) (χ : E.X) (hs : UFib.HasWt D.i _ s χ) (a : Γ(S, ⊤))
    (ha : τ.left.appTop.hom (charUnit S E.X χ).val = G.hom.appTop.hom a) :
    (((τ ≫ D.i) * 𝟙 G).left.appLE _ _ hle).hom s =
      (D.q.left.app V).hom ((E.B.hom.appLE ⊤ V le_top).hom a) * s := by
  refine fn_ext fun z hz => ?_
  have e := hs G τ (𝟙 G) z hz
  have e₁ : gs (𝟙 G.left) z _ ((((τ ≫ D.i) * 𝟙 G).left.appLE _ _ hle).hom s) =
      gs ((τ ≫ D.i) * 𝟙 G).left z _ s :=
    (gs_res (𝟙 G.left) z hle hz _).trans ((gs_pull (𝟙 G.left) ((τ ≫ D.i) * 𝟙 G).left z (D.q.left ⁻¹ᵁ V) (hle hz) s).trans (by rw [Category.id_comp]))
  have e₂ : gs (𝟙 G.left) z _ ((D.q.left.app V).hom ((E.B.hom.appLE ⊤ V le_top).hom a)) =
      gs G.hom z ⊤ a := by
    refine (gs_pull (𝟙 G.left) _ z V hz _).trans ((gs_res (𝟙 G.left ≫ D.q.left) z (U := E.B.hom ⁻¹ᵁ ⊤) le_top hz _).trans
      ((gs_pull _ E.B.hom z ⊤ trivial a).trans ?_))
    rw [Category.id_comp, Over.w]
  rw [e₁, e, gs_mul (𝟙 G.left) z (D.q.left ⁻¹ᵁ V) hz, e₂, gm_val _ _ ⊤ trivial, gs_eq _ _ ⊤ trivial]
  exact congrArg₂ (· * ·) (congrArg (G.left.presheaf.germ ⊤ z trivial).hom ha) rfl

theorem hasWt_iff_weight : ∀ (k : Type) [Field k] [IsAlgClosed k] (E : SplitExt (Sp k)) (G : Over (Sp k)) [GrpObj G] (D : E.GtDatum G) (j : E.ChartIdx) (V : E.B.left.Opens) (hV : IsAffineOpen V) (h : V ≤ E.chart j) (f : Γ(G.left, D.q.left ⁻¹ᵁ V)) (α : E.X), UFib.HasWt D.i (D.q.left ⁻¹ᵁ V) f α ↔ ∀ χ, χ ≠ α → D.weight j V hV h χ f = 0 := by
  intro k _ _ E G _ D j V hV h f α
  have hb := D.coord j V hV h
  constructor
  · intro hf χ hχ
    obtain ⟨t, ht⟩ := exists_char_ne (k := k) E.basis hχ
    let c : k →+* Γ(Sp k, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    let e := splitTorusPointsEquiv (Sp k) E.X G
    let τ := e.symm ((Units.map (G.hom.appTop.hom.comp c).toMonoidHom).comp t)
    have hτ : ∀ ψ, τ.left.appTop.hom (charUnit (Sp k) E.X ψ).val =
        G.hom.appTop.hom (c (t (Multiplicative.ofAdd ψ))) := fun ψ => by
      rw [← splitTorusPointsEquiv_val]
      change (e (e.symm _) _).val = _
      rw [e.apply_symm_apply]
      rfl
    have hle : D.q.left ⁻¹ᵁ V ≤ ((τ ≫ D.i) * 𝟙 G).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V) :=
      fun z hz => translate_mem D τ (𝟙 G) V z hz
    let κ : k →+* Γ(E.B.left, V) := (E.B.hom.appLE ⊤ V le_top).hom.comp c
    have e₁ := cf_diag hb (((τ ≫ D.i) * 𝟙 G).left.appLE _ _ hle).hom.toAddMonoidHom
      (fun ψ => κ (t (Multiplicative.ofAdd ψ)))
      (fun b ψ => translate_appLE D V τ hle _ ψ (hasWt_mono D j V h b ψ) _ (hτ ψ)) χ f
    have e₂ := cf_diag hb (AddMonoidHom.mulLeft ((D.q.left.app V).hom (κ (t (Multiplicative.ofAdd α)))))
      (fun _ => κ (t (Multiplicative.ofAdd α))) (fun _ _ => rfl) χ f
    have e₃ := e₁.symm.trans ((congrArg (WtPart.cf hb χ) (translate_appLE D V τ hle f α hf _ (hτ α))).trans e₂)
    rw [← sub_eq_zero, ← sub_mul, ← map_sub] at e₃
    exact ((IsUnit.mk0 _ (sub_ne_zero.2 fun e => ht (Units.ext e))).map κ).mul_right_eq_zero.1 e₃
  · intro hf
    have e : f = (D.q.left.app V).hom (WtPart.cf hb α f) * WtPart.mono D j V h (Multiplicative.ofAdd α) := by
      refine WtPart.cf_ext hb fun χ => ?_
      rw [WtPart.cf_mono]
      split_ifs with hχ
      · rw [hχ]
      · exact hf χ fun e => hχ e.symm
    rw [e]
    exact hasWt_mono D j V h _ α

end GlobalTheory.ZH.PureWt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLinCombIffPullbackMulGenerator
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem gs_linSum {Y Z : Scheme.{0}} {R : Type} [CommRing R] (p : Y ⟶ Sp R) {I : Type} [Fintype I] (a : I → R)
    (r : Z ⟶ Y) (z : Z) (W : Y.Opens) (hm : r z ∈ W) (f : I → Γ(Y, W)) :
    gs r z W (∑ i, constFn p W (a i) * f i) = ∑ i, cst (r ≫ p) z (a i) * gs r z W (f i) := by
  have e : ∀ (b : I → Γ(Y, W)), gs r z _ (∑ i, b i) = ∑ i, gs r z _ (b i) := fun b => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [gs_eq r z _ hm, map_sum]
  rw [e]
  exact Finset.sum_congr rfl fun i _ => (gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_constFn p _ r z hm _) rfl)

theorem isLin_iff_of_red : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → ∀ (I : Type) [Fintype I] (b : I → LB.Sec (LB.LinComb L ψ ε)) (φ : I → (Φ.H 1).Sec) (b₀ : LB.Sec (LB.LinComb L ψ ε)) (φ₀ : (Φ.H 1).Sec) (a : I → k), (∀ i, UFib.Red Φ c t (b i) (φ i)) → UFib.Red Φ c t b₀ φ₀ → (IsLin Φ.E.B.hom b a b₀ ↔ IsLin Φ.G.hom φ a φ₀) := by
  intro k _ _ Φ Y L hL π N c K K' _ _ ψ ε φt εt t _ I _ b φ b₀ φ₀ a hb hb₀
  have pick : ∀ (y : Φ.G.left) (l : Φ.N₀.ι), y ∈ Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l →
      ∃ J, Good L y J ∧ J (𝟙 _ ≫ Φ.D.q.left ≫ π) = c.idx l := fun y l hy => by
    obtain ⟨J, hJ, e⟩ := exists_good L hL y (fun _ : PUnit => 𝟙 _ ≫ Φ.D.q.left ≫ π) (fun _ => c.idx l)
      (fun _ _ _ => rfl) (fun _ => c.le l hy)
    exact ⟨J, hJ, e PUnit.unit⟩
  have hw : (𝟙 _ ≫ Φ.D.q.left) ≫ Φ.E.B.hom = 𝟙 _ ≫ Φ.G.hom := by
    rw [Category.assoc, Over.w]
  constructor
  · intro h l
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ, e⟩ := pick y l hy
    refine (hb₀ _ (𝟙 _) y J hJ l hy e).trans (Eq.trans ?_ (gs_linSum Φ.G.hom a (𝟙 _) y _ hy _).symm)
    have m := hJ.mem ψ (𝟙 _ ≫ Φ.D.q.left)
    have e₁ : sval b₀ (𝟙 _ ≫ Φ.D.q.left) y J =
        ∑ i, cst (𝟙 _ ≫ Φ.G.hom) y (a i) * sval (b i) (𝟙 _ ≫ Φ.D.q.left) y J := by
      rw [← hw]
      exact (congrArg (gs _ y _) (h _)).trans (gs_linSum Φ.E.B.hom a _ y _ m _)
    rw [e₁, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (mul_assoc _ _ _).trans (congrArg _ (hb i _ (𝟙 _) y J hJ l hy e).symm)
  · intro h j
    have := Φ.D.q_flat
    have := Φ.D.q_surjective
    apply GlobalTheory.FunDescent.app_injective Φ.D.q.left
    refine fn_ext fun y hy => ?_
    refine (gs_pull (𝟙 _) Φ.D.q.left y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) Φ.D.q.left y _ hy _).symm)
    refine Eq.trans ?_ (gs_linSum Φ.E.B.hom a (𝟙 _ ≫ Φ.D.q.left) y _ hy _).symm
    obtain ⟨l, hl⟩ := exists_chart Φ.isLB (Φ.D.q.left y)
    obtain ⟨J, hJ, e⟩ := pick y l hl
    have m := hJ.mem ψ (𝟙 _ ≫ Φ.D.q.left)
    have e₁ : sval b₀ (𝟙 _ ≫ Φ.D.q.left) y J =
        ∑ i, cst (𝟙 _ ≫ Φ.G.hom) y (a i) * sval (b i) (𝟙 _ ≫ Φ.D.q.left) y J := by
      refine (Units.mul_left_inj (val t (𝟙 _) y J)).1 ?_
      refine (hb₀ _ (𝟙 _) y J hJ l hl e).symm.trans ((congrArg (gs _ y _) (h l)).trans
        ((gs_linSum Φ.G.hom a (𝟙 _) y _ hl _).trans ?_))
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact (congrArg _ (hb i _ (𝟙 _) y J hJ l hl e)).trans (mul_assoc _ _ _).symm
    refine (sec_trans b₀ (𝟙 _ ≫ Φ.D.q.left) y (j := j) hy m).trans ((congrArg _ e₁).trans ?_)
    rw [Finset.mul_sum, hw]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (mul_left_comm _ _ _).trans (congrArg _ (sec_trans (b i) (𝟙 _ ≫ Φ.D.q.left) y (j := j) hy m).symm)

end GlobalTheory.ZH.UFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KfBijective
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ClassWeight
open GlobalTheory.UT

def kf (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] :
    F →+* Γ((TFK (R := R) F).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

theorem kf_bijective (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] :
    Function.Bijective (kf R F) :=
  ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem base_eq : (show (TFK (R := u.V) (PadicAlgCl p)).left ⟶ (baseOver (Sp S.R)).left from spMap y₀) ≫
    (baseOver (Sp S.R)).hom = (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK := by
  refine (Category.comp_id _).trans ?_
  exact (congrArg spMap u.fac.symm).trans
    (Spec.map_comp (CommRingCat.ofHom u.yK) (CommRingCat.ofHom (algebraMap (FractionRing u.V) (PadicAlgCl p))))

def Moved (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)) {k : ℕ} (t : SecA u.A (PadicAlgCl p) k)
    (s : LB.Sec (LPow ρ.P.A ρ.P.L (k : ℤ) (baseOver (Sp S.R)))) : Prop :=
  ThetaPtMove.SecRel u.cart (T := TFK (R := u.V) (PadicAlgCl p)) (T₀ := baseOver (Sp S.R)) (spMap y₀) (base_eq u) w t s

theorem exists_moved {w : LB.Iso u.A.L (ρ.P.L.pull u.φ)} (hw : w.IsGen) {k : ℕ}
    (s : LB.Sec (LPow ρ.P.A ρ.P.L (k : ℤ) (baseOver (Sp S.R)))) : ∃ t, Moved u w t s :=
  ThetaPtMove.exists_secRel u.cart _ _ hw ρ.P.isLB u.A.isLB s

end GlobalTheory.ZH.ClassWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MaximalMinorsRegularAndUnitIffToric
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem RatModel.exists_ringHom_val {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    {K : Type} [Field K] (y : Sp K ⟶ M.Z) {U : Set M.Z} (hy : Set.range y ⊆ U) :
    ∃ ψ : M.ringOn U →+* K, ∀ a, ψ a = M.val y a :=
  ⟨(RatModel.valHom y _ (RatModel.range_eq_singleton y (IsLocalRing.closedPoint K))).comp
    (Subalgebra.inclusion (RatModel.ringOn_le_O (hy ⟨_, rfl⟩))).toRingHom, fun _ => rfl⟩

theorem minors_regular_and_unit_iff : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (R' : Subalgebra o Ω) (hR : S.R ≤ R') (n a : ℕ) (GG : Fin n → S.J → R'), S.Over₀ M U₀ → R' ≤ M.ringOn U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (p : ℕ) [Fact p.Prime] (y' : R' →+* PadicAlgCl p) (τ : S.Test p (y'.comp (Subalgebra.inclusion hR).toRingHom)), (∀ b : o, ‖y' (algebraMap o R' b)‖ ≤ 1) → ∀ w : S.J → PadicAlgCl p, w ∈ Submodule.span (OO p) (Set.range fun k j => y' (GG k j)) ↔ ∀ v ∈ τ.E, ‖w ⬝ᵥ v‖ ≤ τ.δ ^ a) → ∀ z : M.Z, ∀ x₀ ∈ S.supI M z, (∀ k, (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) k / S.th x₀ ^ (a * Fintype.card S.J) ∈ M.O z) ∧ (S.TT M z = ⊥ ↔ ∃ k, (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) k ≠ 0 ∧ S.th x₀ ^ (a * Fintype.card S.J) / (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) k ∈ M.O z) := by
  intro o Ω _ _ _ _ S M U₀ R' hR n a GG hO hR' hLL hT hsup hTT hcl hGG
  obtain ⟨hLL, -⟩ := hLL
  obtain ⟨-, -, -, hcp⟩ := hTT
  set D : (S.J → Fin n) → Ω := fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω)) with hD
  set m := a * Fintype.card S.J with hm

  have hDR : ∀ k, D k = ((Matrix.det (Matrix.of fun i j => GG (k i) j) : R') : Ω) := fun k =>
    ((R'.val.toRingHom.map_det (Matrix.of fun i j => GG (k i) j))).symm
  have hclosed : ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∀ x₀ ∈ S.supI M z,
      (∀ k, D k / S.th x₀ ^ m ∈ M.O z) ∧ (S.TT M z = ⊥ ↔ ∃ k, D k ≠ 0 ∧ S.th x₀ ^ m / D k ∈ M.O z) := by
    intro z hz x₀ hx₀
    have h0 : S.th x₀ ≠ 0 := hx₀.1
    have hth : S.th x₀ ∈ M.ringOn U₀ := hO.le (S.th_mem x₀)
    have hinv : (S.th x₀)⁻¹ ∈ M.ringOn U₀ := hO.th_unit x₀ h0
    have hDm : ∀ k, D k ∈ M.ringOn U₀ := fun k => hDR k ▸ hR' (Subtype.prop _)
    have hφ : ∀ k, D k / S.th x₀ ^ m ∈ M.ringOn U₀ := fun k => by
      rw [div_eq_mul_inv, ← inv_pow]
      exact mul_mem (hDm k) (pow_mem hinv m)
    have htest : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y →
        (∀ k, ‖M.val (gPt p ≫ y) (D k / S.th x₀ ^ m)‖ ≤ 1) ∧
        ((∃ k, ‖M.val (gPt p ≫ y) (D k / S.th x₀ ^ m)‖ = 1) ↔ S.TT M z = ⊥) := by
      intro p _ y hy
      obtain ⟨ψ, hψ⟩ := M.exists_ringHom_val (gPt p ≫ y) hy.2
      obtain ⟨y₀, hAt, hb, ⟨τ⟩⟩ := hT z p y hy
      let y' : R' →+* PadicAlgCl p := ψ.comp (Subalgebra.inclusion hR').toRingHom
      have e : y₀ = y'.comp (Subalgebra.inclusion hR).toRingHom :=
        RingHom.ext fun b => (hAt b).trans (hψ ⟨b, hO.le b.2⟩).symm
      subst e
      obtain ⟨hs, hH⟩ := hsup z p y _ τ hy hAt
      have hδ := (hs x₀).1 hx₀
      have hpos := τ.δ_pos
      obtain ⟨h1, h2⟩ := _root_.GlobalTheory.ZH.minors_dual_testLattice o Ω S p _ τ hb hcl n (τ.δ ^ a) (fun k j => y' (GG k j)) (pow_pos hpos a)
        (hGG p y' τ hb)
      rw [← pow_mul, ← hm] at h1 h2
      have hpm : 0 < τ.δ ^ m := pow_pos hpos m
      have hval : ∀ k, ‖M.val (gPt p ≫ y) (D k / S.th x₀ ^ m)‖ * τ.δ ^ m =
          ‖Matrix.det (Matrix.of fun i j => y' (GG (k i) j))‖ := by
        intro k
        have e1 : (⟨_, hφ k⟩ : M.ringOn U₀) * ⟨_, hth⟩ ^ m =
            Subalgebra.inclusion hR' (Matrix.det (Matrix.of fun i j => GG (k i) j)) :=
          Subtype.ext ((div_mul_cancel₀ _ (pow_ne_zero m h0)).trans (hDR k))
        have e2 := congrArg (fun t => ‖ψ t‖) e1
        simp only [map_mul, map_pow, norm_mul, norm_pow] at e2
        rw [hψ, hψ] at e2
        rw [← hδ]
        refine e2.trans ?_
        exact congrArg norm (y'.map_det (Matrix.of fun i j => GG (k i) j))
      refine ⟨fun k => ?_, ?_⟩
      · have := h1 k
        rw [← hval] at this
        exact le_of_mul_le_mul_right (by simpa using this) hpm
      · rw [ThetaSys.TT, hH, ← h2]
        refine exists_congr fun k => ?_
        rw [← hval]
        exact ⟨fun h => by rw [h, _root_.one_mul], fun h => mul_right_cancel₀ hpm.ne' (h.trans (_root_.one_mul _).symm)⟩
    obtain ⟨⟨p, _, y, hy⟩, hreg⟩ := hLL U₀ le_rfl hO.ne z hz
    have hmem : ∀ k, D k / S.th x₀ ^ m ∈ M.O z := fun k =>
      hreg _ (hφ k) fun p _ y hy => (htest p y hy).1 k
    refine ⟨hmem, ?_⟩
    rw [← (htest p y hy).2]
    refine exists_congr fun k => ?_
    rw [RatModel.norm_val_eq_one_iff hy.1 (hmem k), RatModel.isUnit_O_iff]
    simp only [inv_div, ne_eq, div_eq_zero_iff, pow_ne_zero m h0, or_false]
  intro z x₀ hx₀
  have hTTeq : ∀ x : M.Z, S.supI M x = S.supI M z → S.TT M x = S.TT M z := fun x h => by
    rw [ThetaSys.TT, ThetaSys.TT, ThetaSys.HH, ThetaSys.HH, h]
  obtain ⟨x, -, hx, hzx, hs⟩ := hcp z ⊤ trivial
  obtain ⟨h1, h2⟩ := hclosed x hx x₀ (hs ▸ hx₀)
  refine ⟨fun k => RatModel.O_le_of_specializes hzx (h1 k), fun h => ?_, fun ⟨k, hk, hk'⟩ => ?_⟩
  · obtain ⟨k, hk, hk'⟩ := h2.1 ((hTTeq x hs).trans h)
    exact ⟨k, hk, RatModel.O_le_of_specializes hzx hk'⟩
  · obtain ⟨x', hW, hx', -, hs'⟩ := hcp z ⟨_, M.isOpen_setOf_mem_O (S.th x₀ ^ m / D k)⟩ hk'
    exact (hTTeq x' hs').symm.trans ((hclosed x' hx' x₀ (hs' ▸ hx₀)).2.2 ⟨k, hk, hW⟩)

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiEvenDescendBaseChange
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.PsiRing

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {φ : R →+* V} {D : DegPre R}
  {D' : DegPre V} {β : D'.P.A.left ⟶ D.P.A.left} {v : LB.Iso D'.P.L (D.P.L.pull β)}

theorem inv_comp_of_isGrpPullback (gp : IsGrpPullback D'.P.A D.P.A (spMap φ) β) :
    (ι[D'.P.A]).left ≫ β = β ≫ (ι[D.P.A]).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom gp D'.P.A) (𝟙 _))
  rw [Hom.inv_def, Hom.inv_def, Category.id_comp] at e
  refine e.trans ?_
  show ((𝟙 D'.P.A : D'.P.A ⟶ D'.P.A).left ≫ β) ≫ _ = _
  rw [Over.id_left, Category.id_comp]

theorem val_sym_comp (hG : GlobalFnsSt) (gp : IsGrpPullback D'.P.A D.P.A (spMap φ) β) (hv₀ : v.IsGen)
    {Z : Scheme.{0}} (r : Z ⟶ D'.P.A.left) (z : Z) {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    val D.sym (r ≫ β) z J =
      gw v (r ≫ (ι[D'.P.A]).left) z (J ((r ≫ (ι[D'.P.A]).left) ≫ β)) (J' (r ≫ (ι[D'.P.A]).left)) *
        (gw v r z (J (r ≫ β)) (J' r))⁻¹ * val D'.sym r z J' := by
  have he : eSec D'.P.A ≫ β = spMap φ ≫ eSec D.P.A := (cubeMapOf gp).e_comm
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff v).1 hv₀) D.P.isLB D'.P.isLB D'.sym D'.sym_gen
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val t r z J =
      gw v (r ≫ (ι[D'.P.A]).left) z (J ((r ≫ (ι[D'.P.A]).left) ≫ β)) (J' (r ≫ (ι[D'.P.A]).left)) *
        (gw v r z (J (r ≫ β)) (J' r))⁻¹ * val D'.sym r z J' := fun Z r z J J' hJ hJ' => by
    refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) ?_ rfl)
    rw [pw, Fin.prod_univ_two]
    show gw v (r ≫ (ι[D'.P.A]).left) z (J (r ≫ (ι[D'.P.A]).left ≫ β)) (J' (r ≫ (ι[D'.P.A]).left)) ^ (1 : ℤ) *
      gw v (r ≫ 𝟙 _) z (J (r ≫ 𝟙 _ ≫ β)) (J' (r ≫ 𝟙 _)) ^ (-1 : ℤ) = _
    rw [Category.comp_id, Category.id_comp, Category.assoc r, zpow_one, zpow_neg_one]
  have oi : eSec D'.P.A ≫ (ι[D'.P.A]).left = eSec D'.P.A := by
    have : η[D'.P.A] ≫ ι[D'.P.A] = η[D'.P.A] := by simp
    exact congrArg (fun q => q.left) this
  have key := gen_unique' D.P.isLB
    (φ := fun k => β ≫ (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) k) (ε := ![1, -1])
    (fun V _ k => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two]
      show k ((ι[D'.P.A]).left ≫ β) ^ (1 : ℤ) * k (𝟙 _ ≫ β) ^ (-1 : ℤ) =
        k (β ≫ (ι[D.P.A]).left) ^ (1 : ℤ) * k (β ≫ 𝟙 _) ^ (-1 : ℤ)
      rw [inv_comp_of_isGrpPullback gp, Category.id_comp, Category.comp_id])
    D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2
    (DVR.pullGen_isGen _ _ _ _ D.sym_gen β) ht (fun y I hI => by
      choose I' hI' using fun χ : (𝟙_ (Over (Spec (CommRingCat.of V)))).left ⟶ D'.P.A.left =>
        exists_chart D'.P.isLB (χ y)
      have a := val_corr hI' D'.sym_rig (𝟙 _)
      rw [val_pull hI', val_one, Category.id_comp] at a
      have b := val_corr hI D.sym_rig (spMap φ)
      rw [val_pull hI, val_one, ← he] at b
      refine ((val_pull hI _ _ _).trans b).trans (Eq.symm ((hv' _ _ y I I' hI hI').trans ?_))
      rw [a, oi, mul_inv_cancel, _root_.one_mul]) Z r z J hJ
  exact (val_pull hJ _ _ _).symm.trans (key.trans (hv' _ _ z J J' hJ hJ'))

theorem psiEven_descend : GlobalFnsSt → ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → D'.PsiEven → D.PsiEven := by
  intro hG R V _ _ _ _ φ D D' β v xe gp hv hc gam hgam hψ h χ
  obtain ⟨x, rfl⟩ := xe.surjective χ
  have sep : D.P.A.left.IsSeparated := by
    have := D.P.isAb.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from D.P.A.hom]
    infer_instance
  obtain ⟨z⟩ : Nonempty (TK V).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing V)))
  have red : IsReduced (TK R).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (FractionRing R))))
  have sub : Subsingleton (TK R).left := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  have cx : ∀ a, D'.xK a ≫ β = gam ≫ D.xK (xe a) := fun a => by
    show (jK V ≫ (D'.c a).left) ≫ β = gam ≫ jK R ≫ (D.c (xe a)).left
    rw [Category.assoc, hc, ← Category.assoc, ← hgam, Category.assoc]
  have cn : D'.xK (-x) = D'.xK x ≫ (ι[D'.P.A]).left := by
    show (toUnit _ ≫ D'.c (-x)).left = _
    rw [PsiEvenPull.c_neg, ← Category.assoc, Over.comp_left]
  refine TauPull.corr_of_dense D.P.isLB gam z (fun U ⟨y, hy⟩ => Subsingleton.elim y (gam z) ▸ hy) fun J hJ => ?_
  choose J' hJ₀ using fun χ : (TK V).left ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ z)
  have hJ' : Good D'.P.L z J' := hJ₀
  have vψ : ∀ a, val (D.psi (xe a)) gam z J =
      (gw v (D'.xK a) z (J (D'.xK a ≫ β)) (J' (D'.xK a)))⁻¹ * val (D'.psi a) (𝟙 _) z J' := fun a => by
    have := CubTransport.val_pmaps (fun _ => cx a) (hψ a) (𝟙 _) hJ hJ'
    rwa [Fintype.prod_unique, Category.id_comp, Category.id_comp, zpow_neg_one] at this
  have e := val_corr hJ' (h x) (𝟙 _)
  rw [val_mul hJ', val_pull hJ', Category.id_comp] at e
  rw [val_mul hJ, val_pull hJ, ← map_neg, vψ, vψ, ← cx, val_sym_comp hG gp hv _ z hJ hJ', ← cn]
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

end GlobalTheory.PsiRing
end
end

