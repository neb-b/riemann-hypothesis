module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0127
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThreePointSeriesExponentialOfDefect
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecLinIffComb
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0125
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0126
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueNormalisedPullbackChainRule
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonDegenerateFormalBiextensionSquare

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthParamsPlusMinusCountsEqKappa
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem numOf_Dplus_Dminus : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → (numOf D L).Dplus j = ((∑ τ, ∑ i, (kaR Tp hK j).aP τ i : ℕ) : ℚ) ∧ (numOf D L).Dminus j = ((∑ τ, ∑ i, (kaR Tp hK j).aM τ i : ℕ) : ℚ) := by
  intro D L Pm Tp hK j hj
  have hb := (_root_.GlobalTheory.RunDepth.plOf_bijective_card D).1
  have h1 := hj.1
  have h2 := hj.2
  constructor
  · have e : (numOf D L).Dplus j =
        ∑ z : RPl D.R, ∑ i ∈ Finset.range (D.R.sigW j).1, DV.aPlusQ D j (plOf D z) i := rfl
    rw [e, hb.sum_comp (fun τ => ∑ i ∈ Finset.range (D.R.sigW j).1, DV.aPlusQ D j τ i)]
    push_cast
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← (hK j h1 h2 τ).1 i, ← kaWt_big D hK (even_nV Tp) j h1 h2 τ i, Int.cast_natCast]
    rfl
  · have e : (numOf D L).Dminus j =
        ∑ z : RPl D.R, ∑ i ∈ Finset.range (D.R.sigW j).2, DV.aMinusQ D j (plOf D z) i := rfl
    rw [e, hb.sum_comp (fun τ => ∑ i ∈ Finset.range (D.R.sigW j).2, DV.aMinusQ D j τ i)]
    push_cast
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_range, ← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 := kaWt_small D hK (even_nV Tp) j h1 h2 τ i
    have e2 := (hK j h1 h2 τ).2 (Fin.rev i)
    have e3 := congrArg (fun q : ℤ => (q : ℚ)) e1
    simp only [Int.cast_natCast, Int.cast_neg] at e3
    rw [e2, neg_neg] at e3
    exact e3.symm

end GlobalTheory.RunDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.EigenEquationTranslationKernelGenericFibre
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Jets

theorem units_mul_pow_mul_inv_cancel {R : Type} [CommRing R] (x y m : Rˣ) (s : R) :
    x.val * s * (y * x⁻¹ * m).val = y.val * (m.val * s) := by
  rw [Units.val_mul, Units.val_mul]
  linear_combination (s * y.val * m.val) * x.mul_inv

theorem ring_relation_transfer_identity {R : Type} [CommRing R] {t t' m m' e : R} (E : t' * m = e * (t * m')) (x y y' : R) :
    y' * t' * (y * x * m) = e * (y * t * (y' * x * m')) := by
  linear_combination (x * y * y') * E

theorem sval_of_isoRelM {Y Y' X₁ X₂ Z₁ Z : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} {m : Y' ⟶ Y} {k : ℕ} {g₁ : Z₁ ⟶ X₁} {h₁ : Y' ⟶ Z₁}
    {a : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ)))}
    {b : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => m ≫ f₂) (fun _ => (k : ℤ)))}
    (H : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a (m ≫ f₂) (𝟙 _) b) (r : Z ⟶ Y') (z : Z) {J₂} {J₁}
    (hJ₂ : Good L₂ z J₂) (hJ₁ : Good L₁ z J₁) :
    sval b r z J₂ = (isoVal w (r ≫ m) z (J₂ ((r ≫ m) ≫ f₂)) (J₁ ((r ≫ m) ≫ f₁)) ^ (k : ℤ)).val *
      sval a (r ≫ h₁) z J₁ := by
  have := (GlobalTheory.FieldBaseChange.isoRelM_iff w m k h₁ H.1 _ H.2.1 a b).1 H Z r z _ _
    (hJ₂ ((r ≫ m) ≫ f₂)) (hJ₁ ((r ≫ m) ≫ f₁))
  rw [Category.comp_id] at this
  rw [GlobalTheory.FieldBaseChange.sval_eq_powVal, GlobalTheory.FieldBaseChange.sval_eq_powVal, Category.assoc r h₁, H.1,
    ← Category.assoc r m f₁, ← Category.assoc r m f₂]
  exact this

theorem eigen_transfer {S X : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] (e : B ≅ A)
    [IsMonHom e.hom] {L₁ : LB A.left} {L₂ : LB X} (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (f : B.left ⟶ X)
    {K : Type} [Field K] (p : Spec (CommRingCat.of K) ⟶ S) (φ : X ⟶ X) (b : B ⟶ B) (hφ : b.left ≫ f = f ≫ φ)
    (a : A ⟶ A) (ha : IsMonHom a) (hb : b ≫ e.hom = e.hom ≫ a) (N k : ℕ)
    (mu : LB.Gen (LB.LinComb L₂ (K := Fin 2) ![𝟙 X, φ] ![(N : ℤ), -1])) (hmu : mu.IsGen)
    (w : LB.Iso (L₁.pull e.hom.left) (L₂.pull f)) (hw : w.IsGen)
    (σ₀ : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => (snd (Over.mk p) B).left ≫ f) (fun _ => (k : ℤ))))
    (σ' τ : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => (snd (Over.mk p) B).left ≫ f)
      (fun _ => ((k * N : ℕ) : ℤ))))
    (t' t : LB.Sec (LPow A L₁ ((k * N : ℕ) : ℤ) (Over.mk p)))
    (h₀ : ∀ (y : (Over.mk p ⊗ B).left) (J), Good L₂ y J → sval σ' (𝟙 _) y J =
      sval σ₀ (Over.mk p ◁ b).left y J * (val mu ((snd (Over.mk p) B).left ≫ f) y J).val ^ k)
    (h₁ : GeneratorPullback.IsoRelM L₁ L₂ e.hom.left f w (snd (Over.mk p) B).left (k * N) (snd (Over.mk p) A).left
      (lift (fst (Over.mk p) B) (snd (Over.mk p) B ≫ e.hom)).left t' ((snd (Over.mk p) B).left ≫ f) (𝟙 _) σ')
    (h₂ : GeneratorPullback.IsoRelM L₁ L₂ e.hom.left f w (snd (Over.mk p) B).left (k * N) (snd (Over.mk p) A).left
      (lift (fst (Over.mk p) B) (snd (Over.mk p) B ≫ e.hom)).left t ((snd (Over.mk p) B).left ≫ f) (𝟙 _) τ)
    (θ : ThetaGrp A L₁ ((k * N : ℕ) : ℤ) (Over.mk p)) (hθ : IsActOf A L₁ ((k * N : ℕ) : ℤ) θ t' t)
    (c : Over.mk p ⟶ A) (u : Γ((Over.mk p).left, ⊤)ˣ) (hc : c ≫ a = 1)
    (hW : WeilIs A L₁ ((k * N : ℕ) : ℤ) c θ.pt u)
    (Z : Scheme.{0}) (ρ : Z ⟶ (Over.mk p ⊗ B).left) (z : Z) (J) (hJ : Good L₂ z J) :
    sval τ (ρ ≫ (translT B (c ≫ e.inv)).left) z J * (val mu (ρ ≫ (snd (Over.mk p) B).left ≫ f) z J).val ^ k =
      gs (ρ ≫ (fst (Over.mk p) B).left) z ⊤ u.val * (sval τ ρ z J *
        (val mu ((ρ ≫ (translT B (c ≫ e.inv)).left) ≫ (snd (Over.mk p) B).left ≫ f) z J).val ^ k) := by
  obtain ⟨g, hg⟩ : ∃ g, g = lift (fst (Over.mk p) B) (snd (Over.mk p) B ≫ e.hom) := ⟨_, rfl⟩
  rw [← hg] at h₁ h₂
  have g₁ : g ≫ fst _ _ = fst _ _ := by rw [hg, lift_fst]
  have g₂ : g ≫ snd _ _ = snd _ _ ≫ e.hom := by rw [hg, lift_snd]
  let n : Over.mk p ⊗ A ⟶ Over.mk p ⊗ B := lift (fst _ _) (snd _ _ ≫ e.inv)
  have hn : n ≫ g = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n, g₁, g₂]
  have hn' : g ≫ n = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n, g₁, reassoc_of% g₂]
  have hb' : a ≫ e.inv = e.inv ≫ b := by
    rw [Iso.comp_inv_eq, Category.assoc, hb, e.inv_hom_id_assoc]
  have gb : Over.mk p ◁ b ≫ g = g ≫ Over.mk p ◁ a := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [g₁, g₂, reassoc_of% g₂, hb]
  have gt : translT B (c ≫ e.inv) ≫ g = g ≫ translT A c := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [translT, g₁]
    · rw [Category.assoc, Category.assoc, g₂, translT, translT, lift_snd_assoc, lift_snd]
      show ((fst _ B ≫ c ≫ e.inv) * snd _ B) ≫ e.hom = g ≫ ((fst _ A ≫ c) * snd _ A)
      rw [MonObj.mul_comp, MonObj.comp_mul, g₂, reassoc_of% g₁]
      simp
  have tb : translT B (c ≫ e.inv) ≫ snd _ _ ≫ b = snd _ _ ≫ b := by
    rw [← cancel_mono e.hom]
    simp only [Category.assoc]
    rw [hb, ← reassoc_of% g₂, reassoc_of% gt, GlobalTheory.KernelEigen.translT_snd_comp a hc]
  obtain ⟨s, hs⟩ := ((GlobalTheory.FieldBaseChange.isoRelM_bijective (k := k) (m := (snd (Over.mk p) B).left)
    (g₁ := (snd (Over.mk p) A).left) (h₁ := g.left) hL₁ hL₂ hw (congrArg (fun q => q.left) g₂) n.left
    (congrArg (fun q => q.left) hn) (congrArg (fun q => q.left) hn')).2 σ₀).exists
  obtain ⟨ν, hν, vν⟩ := exists_gen hL₂ (K' := Fin 2) (φ' := ![𝟙 X, φ]) (ε' := ![((k * N : ℕ) : ℤ), -(k : ℤ)])
    (fun U _ h => by simp [Fin.prod_univ_two]) (GeneratorPullback.powGen L₂ _ _ mu k) (GlobalTheory.FrameGeo.powGen_isGen _ _ _ _ hmu k)
  obtain ⟨mA, hmA, vmA⟩ := exists_gen_move_back _ _ _ _ _ L₁ L₂ hL₁ hL₂ _ _ w hw (Fin 2)
    ![(snd (Over.mk p) A ≫ e.inv).left, (snd (Over.mk p) A ≫ a ≫ e.inv).left] _
    ![(snd (Over.mk p) A).left, (snd (Over.mk p) A ≫ a).left]
    (fun i => by
      fin_cases i
      · show (snd (Over.mk p) A).left = (snd (Over.mk p) A ≫ e.inv).left ≫ e.hom.left
        rw [← Over.comp_left, Category.assoc, e.inv_hom_id, Category.comp_id]
      · show (snd (Over.mk p) A ≫ a).left = (snd (Over.mk p) A ≫ a ≫ e.inv).left ≫ e.hom.left
        rw [← Over.comp_left, Category.assoc, Category.assoc, e.inv_hom_id, Category.comp_id])
    _ ((snd (Over.mk p) A ≫ e.inv).left ≫ f)
    (fun i => by
      fin_cases i
      · exact Category.comp_id _
      · show ((snd (Over.mk p) A ≫ e.inv).left ≫ f) ≫ φ = (snd (Over.mk p) A ≫ a ≫ e.inv).left ≫ f
        rw [Category.assoc, ← hφ, ← Category.assoc, ← Over.comp_left, Category.assoc, hb'])
    ν hν
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk p ⊗ B).left) (z : Z) (J₂) (J₁), Good L₂ z J₂ → Good L₁ z J₁ →
      val mu (r ≫ (snd (Over.mk p) B).left ≫ f) z J₂ ^ k =
        isoVal w (r ≫ (snd (Over.mk p) B).left) z (J₂ ((r ≫ (snd (Over.mk p) B).left) ≫ f))
          (J₁ ((r ≫ (snd (Over.mk p) B).left) ≫ e.hom.left)) ^ ((k * N : ℕ) : ℤ) *
        (isoVal w (r ≫ (snd (Over.mk p) B ≫ b).left) z (J₂ ((r ≫ (snd (Over.mk p) B ≫ b).left) ≫ f))
          (J₁ ((r ≫ (snd (Over.mk p) B ≫ b).left) ≫ e.hom.left)) ^ (k : ℤ))⁻¹ * val mA (r ≫ g.left) z J₁ := by
    intro Z r z J₂ J₁ hJ₂ hJ₁
    have e₀ : (r ≫ g.left) ≫ (snd (Over.mk p) A ≫ e.inv).left = r ≫ (snd (Over.mk p) B).left := by
      rw [Category.assoc, ← Over.comp_left, reassoc_of% g₂, e.hom_inv_id, Category.comp_id]
    have e₁ : (r ≫ g.left) ≫ (snd (Over.mk p) A ≫ a ≫ e.inv).left = r ≫ (snd (Over.mk p) B ≫ b).left := by
      rw [Category.assoc, ← Over.comp_left, reassoc_of% g₂, hb', e.hom_inv_id_assoc]
    have := vmA Z (r ≫ g.left) z J₂ J₁ hJ₂ hJ₁
    rw [vν _ _ z J₂ hJ₂, GlobalTheory.FrameGeo.val_powGen, Fin.prod_univ_two, ← Category.assoc, e₀, Category.assoc] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e₀, e₁, zpow_neg] at this
    exact this
  have hσ := secRel_iff hL₂ _ _ σ' _ _ σ₀ (Over.mk p ◁ b).left _ _
    (LB.pullGen L₂ _ _ (GeneratorPullback.powGen L₂ _ _ mu k) ((snd (Over.mk p) B).left ≫ f))
  have h₀' := hσ.1 (hσ.2 fun y J hJ => by
    rw [h₀ y J hJ, val_pull hJ, GlobalTheory.FrameGeo.val_powGen, Category.id_comp, Category.id_comp,
      Units.val_pow_eq_pow_val])
  choose J₁ hJ₁ using fun χ : Z ⟶ A.left => exists_chart hL₁ (χ z)
  have E := GlobalTheory.translate_pullback_eigensection S A L₁ hL₁ K p a ha N k mA hmA s t' t (fun y I₁ hI₁ => by
    choose I₂ hI₂ using fun χ : (Over.mk p ⊗ A).left ⟶ X => exists_chart hL₂ (χ y)
    have ng : n.left ≫ g.left = 𝟙 _ := congrArg (fun q => q.left) hn
    have e₁ : (n.left ≫ (Over.mk p ◁ b).left) ≫ g.left = (Over.mk p ◁ a).left := by
      rw [← Over.comp_left, ← Over.comp_left, Category.assoc, gb, reassoc_of% hn]
    have e₂ : (n.left ≫ (Over.mk p ◁ b).left) ≫ (snd (Over.mk p) B).left =
        n.left ≫ (snd (Over.mk p) B ≫ b).left := by
      rw [Category.assoc, ← Over.comp_left, whiskerLeft_snd]
    have := h₀' _ n.left y I₂ hI₂
    rw [val_pull hI₂, GlobalTheory.FrameGeo.val_powGen, hv _ _ y I₂ I₁ hI₂ hI₁, sval_of_isoRelM h₁ _ y hI₂ hI₁,
      sval_of_isoRelM hs _ y hI₂ hI₁, ng, e₁, e₂] at this
    refine (Units.mul_right_inj _).1 (this.trans ?_)
    exact units_mul_pow_mul_inv_cancel _ _ _ _) θ hθ c u hc hW Z (ρ ≫ g.left) z J₁ hJ₁
  have e₁ : (ρ ≫ (translT B (c ≫ e.inv)).left) ≫ g.left = (ρ ≫ g.left) ≫ (translT A c).left := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, gt]
  have e₂ : (ρ ≫ (translT B (c ≫ e.inv)).left) ≫ (snd (Over.mk p) B ≫ b).left =
      ρ ≫ (snd (Over.mk p) B ≫ b).left := by
    rw [Category.assoc, ← Over.comp_left, tb]
  have e₃ : (ρ ≫ g.left) ≫ (fst (Over.mk p) A).left = ρ ≫ (fst (Over.mk p) B).left := by
    rw [Category.assoc, ← Over.comp_left, g₁]
  rw [e₃] at E
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, hv _ _ z J J₁ hJ hJ₁, hv _ _ z J J₁ hJ hJ₁,
    sval_of_isoRelM h₂ _ z hJ hJ₁, sval_of_isoRelM h₂ _ z hJ hJ₁, e₁, e₂]
  simp only [Units.val_mul]
  exact ring_relation_transfer_identity E _ _ _

theorem eigen_equation_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (φ : G ⟶ G) (a : A.A ⟶ A.A), IsMonHom a → (Over.pullback (jK R)).map φ ≫ U.gen.hom = U.gen.hom ≫ a → ∀ (N k : ℕ) (mu : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 G.left, φ.left] ![(N : ℤ), -1])), mu.IsGen → ∀ (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w.IsGen → ∀ (σ₀ : U.SecGF F k) (σ' τ : U.SecGF F (k * N)) (t' t : LB.Sec (LPow A.A A.L ((k * N : ℕ) : ℤ) (TFK (R := R) F))), (∀ (y : (UnifPre.GF (G := G) F).left) (J), Good U.LG.L y J → sval σ' (𝟙 _) y J = sval σ₀ (TFK (R := R) F ◁ (Over.pullback (jK R)).map φ).left y J * (val mu (UnifPre.gFK (G := G) F) y J).val ^ k) → GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (k * N) (snd (TFK (R := R) F) A.A).left (U.genF F).left t' (UnifPre.gFK (G := G) F) (𝟙 _) σ' → GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (k * N) (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) τ → ∀ θ : ThetaGrp A.A A.L ((k * N : ℕ) : ℤ) (TFK (R := R) F), IsActOf A.A A.L ((k * N : ℕ) : ℤ) θ t' t → ∀ (z₀ : TFK (R := R) F ⟶ A.A) (ε : Fˣ), z₀ ≫ a = 1 → WeilIs A.A A.L ((k * N : ℕ) : ℤ) z₀ θ.pt (unitOn ε) → ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (UnifPre.GF (G := G) F).left) (z : Z) (J), Good U.LG.L z J → sval τ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) (z₀ ≫ U.gen.inv)).left) z J * (val mu (ρ ≫ UnifPre.gFK (G := G) F) z J).val ^ k = constVal (ρ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) z (ε : F) * (sval τ ρ z J * (val mu ((ρ ≫ (translT ((Over.pullback (jK R)).obj G) (z₀ ≫ U.gen.inv)).left) ≫ UnifPre.gFK (G := G) F) z J).val ^ k) := by
  intro R _ _ I D A G _ _ U F _ _ φ a ha hφ N k mu hmu w hw σ₀ σ' τ t' t h₀ h₁ h₂ θ hθ z₀ ε hz hW Z ρ z J hJ
  haveI := U.gen_hom
  exact eigen_transfer U.gen A.isLB U.LG.isLB (pullback.fst G.hom (jK R)) (jFK (R := R) F) φ.left
    ((Over.pullback (jK R)).map φ) (pullback.lift_fst _ _ _) a ha hφ N k mu hmu w hw σ₀ σ' τ t' t h₀ h₁ h₂ θ hθ
    z₀ (unitOn ε) hz hW Z ρ z J hJ

end GlobalTheory.Jets
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLevelPointEqOfKilledByHalfLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelPoint_eq_of_killedByHalfLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra c.F F] (yF : FrPt Xo c F) (t : ptO Xo yF.x ⟶ Xo.univ.t.G), KilledBy Xo l.Mb t → ∃ a : Dw.La, levPt Xo yF.x a = t := by
  first | exact @GlobalTheory.exists_levPt_eq_of_killedBy | exact GlobalTheory.exists_levPt_eq_of_killedBy | (intros; apply GlobalTheory.exists_levPt_eq_of_killedBy <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLiftPointTranslationFieldPointStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_point_translation_fieldPoint : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (T : Over (Spec (CommRingCat.of R))) (e : T.left ⟶ Spec (CommRingCat.of F)) (r g : T ⟶ G), g.left = e ≫ x.left ≫ pullback.fst G.hom (jK R) → ∃ ρ : T.left ⟶ (UnifPre.GF (G := G) F).left, ρ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = e ∧ ρ ≫ UnifPre.gFK (G := G) F = r.left ∧ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) x).left) ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = e ∧ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) x).left) ≫ UnifPre.gFK (G := G) F = (r * g).left := by
  first | exact @GlobalTheory.exists_lift_translT | exact GlobalTheory.exists_lift_translT | (intros; apply GlobalTheory.exists_lift_translT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMulEquivUniformisedPointsUniversalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mulEquiv_uniformisedPoints_universal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (F : Type) [Field F] [Algebra T.Fr F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) → ∃ e : (TFK (R := T.V) F ⟶ P.A.A) ≃* (ptO Xo xF ⟶ Xo.univ.t.G), (∀ x b, PtTieF I P F xF x b ↔ b = e x) ∧ ∀ (a : 𝓞 E) x, e (x ≫ P.oA.act a) = e x ≫ Xo.univ.t.act.act a := by
  first | exact @GlobalTheory.PtTie.exists_mulEquiv_ptTieF | exact GlobalTheory.PtTie.exists_mulEquiv_ptTieF | (intros; apply GlobalTheory.PtTie.exists_mulEquiv_ptTieF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupMomentClosureStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wedge_raising_scalar_sq_mul_degree_ratio_le : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν + (r + 1) * (r + 2) ≤ q0 → ∀ io pr ep, TensH (cmp (r + 1)) (cmp (r + 1) (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) (r + 1) => R (ν + eZ I.1)) io pr ep → NzOn (R ν) (l ν) → ∀ (I : Sub (2 * r + k + 1) (r + 1)) (κ₀ : ℂ), NzOn (R (ν + eZ I.1)) (l (ν + eZ I.1)) → (∀ v ∈ (R ν).sm, l (ν + eZ I.1) (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec k r z)) v c)) = κ₀ • l ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν + eZ I.1) ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ (r + 1) := by
  first | exact @GlobalTheory.WedgeKappa.kappa_bound | exact GlobalTheory.WedgeKappa.kappa_bound | (intros; apply GlobalTheory.WedgeKappa.kappa_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FirstRowsBoundAndSizesBounds
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FirstRows

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

theorem sum_ite_le {ι β : Type} [Fintype ι] (φ : ι → β) (hφ : Function.Injective φ) (y : β)
    [∀ t, Decidable (y = φ t)] (g : ι → ℝ) (B : ℝ) (hB : 0 ≤ B) (hg : ∀ t, g t ≤ B) :
    (∑ t, if y = φ t then g t else 0) ≤ B := by
  classical
  by_cases h : ∃ t, y = φ t
  · obtain ⟨t, rfl⟩ := h
    rw [Finset.sum_eq_single t]
    · simpa using hg t
    · intro t' _ ht'
      rw [if_neg fun h => ht' (hφ h).symm]
    · simp
  · rw [Finset.sum_eq_zero fun t _ => if_neg fun h' => h ⟨t, h'⟩]
    exact hB

theorem tauEmb_injective (D : D7) : Function.Injective (DV.tauEmb D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem conj_tauEmb_injective (D : D7) :
    Function.Injective fun t => ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (DV.tauEmb D t) := by
  intro s t h
  apply tauEmb_injective D
  ext x
  have := RingHom.congr_fun h x
  exact (starRingEnd ℂ).injective this

theorem mul_wtA_le {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (T A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (i : ℕ)
    (hP : ∀ t, T * (ext0 (w.aP t) i : ℝ) ≤ A) (hM : ∀ t, T * (ext0 (w.aM t) i : ℝ) ≤ B) (τ : D.host.E →+* ℂ) :
    T * wtA w (τ, i) ≤ A + B := by
  classical
  unfold wtA
  push_cast
  rw [Finset.mul_sum]
  simp only [mul_add, mul_ite, mul_zero]
  rw [Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · convert sum_ite_le (DV.tauEmb D) (tauEmb_injective D) τ _ A hA hP
  · convert sum_ite_le _ (conj_tauEmb_injective D) τ _ B hB hM

theorem b'_pos (s : Scale) : 0 < s.b' := by
  unfold Scale.b' Scale.a Scale.X' Scale.b
  have : 0 < s.x := by linarith [s.one_lt_alt]
  positivity

theorem w''_le (s : Scale) (n : ℕ) (hn : 1 ≤ n) (hx : 3 ≤ s.x) : s.w'' n ≤ s.b' / 3 := by
  unfold Scale.w''
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_le_div_of_nonneg_left (b'_pos s).le (by norm_num) (by nlinarith)

theorem first_rows_and_sizes : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b →
  (∀ τ : D.host.E →+* ℂ, (Tp.TO : ℝ) * wtA (lR Tp hK j) (τ, 0) ≤ 3 * L.sc.b) ∧ ∀ z : RPl D.R, L.sc.w'' D.R.n ≤ (numOf D L).w j z ∧ (numOf D L).w j z ≤ 2 * L.sc.b := by
  intro D L Pm Tp hK j hj hx hkb
  obtain ⟨-, hsz⟩ := GlobalTheory.RunDepth.sizes_le_two_mul D L Pm hx hkb
  obtain ⟨hw, -, hnum⟩ := hsz j hj
  have hb' := b'_pos L.sc
  have hn : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
  have hw3 := w''_le L.sc D.R.n hn hx
  have hk5 : 5 ≤ D.R.k := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  have hk : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk5
  have hbb : L.sc.b' ≤ L.sc.b := by nlinarith
  have hSc : L.Sc ≤ L.sc.b' / 3 := by nlinarith [Pm.kS_le, L.Sc_pos]
  have heta : L.etaSz ≤ L.sc.b' / 3 := by
    have h1 := Pm.teta
    have h2 := L.t_win.1
    have h3 := L.etaSz_pos
    have h0 : 0 ≤ L.sc.w'' D.R.n := by nlinarith [Pm.kS_le, L.Sc_pos]
    have h4 : L.sc.w'' D.R.n / L.sc.x ≤ L.sc.w'' D.R.n := div_le_self h0 L.sc.one_lt_alt.le
    nlinarith
  have hScp := L.Sc_pos
  have hetap := L.etaSz_pos
  refine ⟨fun τ => ?_, fun z => ⟨?_, ?_⟩⟩
  · have := mul_wtA_le (lR Tp hK j) (Tp.TO : ℝ) (2 * L.sc.b + L.Sc) L.etaSz (by linarith) hetap.le 0 ?_ ?_ τ
    · linarith
    · intro t
      unfold ext0
      split_ifs with h
      · have h1 := (GlobalTheory.RunDepth.mul_rows_lR_le_kaR D L Pm Tp hK j t).1 ⟨0, h⟩
        have h2 := (GlobalTheory.WeightRows.kappa_entries_le D L Pm Tp hK j hj t).1 ⟨0, h⟩ (by show 0 < D.R.k - 1; omega)
        have h3 : (Tp.TO : ℝ) * ((lR Tp hK j).aP t ⟨0, h⟩ : ℝ) ≤ ((kaR Tp hK j).aP t ⟨0, h⟩ : ℝ) := by exact_mod_cast h1
        linarith [(hw t).2]
      · simp only [Nat.cast_zero, mul_zero]; linarith
    · intro t
      unfold ext0
      split_ifs with h
      · have h1 := (GlobalTheory.RunDepth.mul_rows_lR_le_kaR D L Pm Tp hK j t).2.1 ⟨0, h⟩
        have h2 := (GlobalTheory.WeightRows.kappa_entries_le D L Pm Tp hK j hj t).2.2 ⟨0, h⟩
        have h3 : (Tp.TO : ℝ) * ((lR Tp hK j).aM t ⟨0, h⟩ : ℝ) ≤ ((kaR Tp hK j).aM t ⟨0, h⟩ : ℝ) := by exact_mod_cast h1
        linarith
      · simp only [Nat.cast_zero, mul_zero]; linarith
  · rw [hnum z]
    set τ := plOf D z
    by_cases htop : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · classical
      unfold Host.topPlaces at htop
      obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 htop
      have h1 := (L.win_top j hj.1 hj.2 τ ⟨t, ht⟩ hte.symm).1
      have h2 := L.bT_ge ⟨t, ht⟩
      have h3 : 0 ≤ L.sc.b' / L.sc.x := div_nonneg hb'.le (by linarith)
      linarith
    · by_cases hth : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
      · have h1 := (L.win_thick j hj.1 hj.2 τ hth).1
        linarith
      · exact (L.win_thin j hj.1 hj.2 τ ⟨(D.eTau τ).2, htop, hth⟩).1
  · rw [hnum z]
    exact (hw _).2

end GlobalTheory.FirstRows
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueNormalisedPullbackChainRuleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_value_normalised_pullback_chain_rule : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (F : Type) [Field F] [Algebra c.F F] (yF : FrPt Xo c F) (β : 𝓞 E) (N k : ℕ) (z : ℤ), β * star β = (N : 𝓞 E) → z = ((k * N : ℕ) : ℤ) → ∀ (n : ℕ) (hh : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo yF.x))) (hh' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L z (ptO Xo yF.x))), (∀ i, IsNormPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act β) z (k : ℤ) (hh i) (hh' i)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∑ m ∈ Pp.support, algebraMap c.F F (Pp.coeff m) * ∏ i, nab yF z (hh' i) (colOf m i) = algebraMap c.F F (nrm Dw c a β) * ∑ m ∈ Pp.support, algebraMap c.F F (Pp.coeff m) * ∏ i, nab yF (k : ℤ) (hh i) (colOf m i) := by
  first | exact @GlobalTheory.ChainRule.harmonic_value_normPull | exact GlobalTheory.ChainRule.harmonic_value_normPull | (intros; apply GlobalTheory.ChainRule.harmonic_value_normPull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesLthPowerOfPderivVanishModMaximalStatement
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_lthPower_of_pderiv_vanish_mod_maximal : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (σ : Type) [Fintype σ], (∀ b : MvPowerSeries σ C, IntS V b → (∀ i μ, V.MM (MvPowerSeries.coeff μ (MvPowerSeries.pderiv (R := C) i b))) → ∃ b' : MvPowerSeries σ C, IntS V b' ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ (b - b' ^ V.l))) ∧ (∀ f g : MvPowerSeries σ C, IntS V f → IntS V g → (∀ μ, V.MM (MvPowerSeries.coeff μ (f ^ V.l - g ^ V.l))) → ∀ μ, V.MM (MvPowerSeries.coeff μ (f - g))) ∧ ∀ f g : MvPowerSeries σ C, IntS V f → IntS V g → ∀ μ, V.MM (MvPowerSeries.coeff μ ((f + g) ^ V.l - f ^ V.l - g ^ V.l)) ∧ V.MM (MvPowerSeries.coeff μ ((f - g) ^ V.l - (f ^ V.l - g ^ V.l))) := by
  first | exact @GlobalTheory.SeriesFrobRoot.main | exact GlobalTheory.SeriesFrobRoot.main | (intros; apply GlobalTheory.SeriesFrobRoot.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonDegenerateFormalBiextensionSquareStatement
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonDegenerate_formalBiextension_square : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), NDG Y → NonDeg (Y.rawSelf p) V := by
  first | exact @GlobalTheory.NonDegSquare.nonDeg_rawSelf | exact GlobalTheory.NonDegSquare.nonDeg_rawSelf | (intros; apply GlobalTheory.NonDegSquare.nonDeg_rawSelf <;> assumption)
end

