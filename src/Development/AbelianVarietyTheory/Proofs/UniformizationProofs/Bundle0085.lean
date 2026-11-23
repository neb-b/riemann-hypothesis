module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfIsMinInClassTwoOfSameClassFour
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUOfIntegralTorsionPoint
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOneDim
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.OneDim

theorem gs_zero {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  by_cases h : f y ∈ U
  · rw [gs_eq f y U h, map_zero, map_zero]
  · exact dif_neg h

def zeroSec {Y : Scheme.{0}} (M : LB Y) : LB.Sec M :=
  ⟨fun _ => 0, fun i j => by rw [map_zero, map_zero, mul_zero]⟩

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem expF_zero (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) :
    U.ExpF F k (zeroSec _) (fun _ => zeroSec _) := by
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, ?_, ?_⟩
  · intro Z rA y rG _ _ z JA JG _ _
    rw [Fin.sum_univ_zero]
    exact (congrArg (_ * ·) (gs_zero _ _ _)).trans (mul_zero _)
  · intro α Z rF rB _ z J _
    rw [Fin.sum_univ_zero]
    exact gs_zero _ _ _

theorem appTop_injective (F : Type) [Field F] [Algebra (FractionRing R) F] :
    Function.Injective (toUnit (TF (R := R) F)).left.appTop.hom := by
  have e₂ : (toUnit (TF (R := R) F)).left =
      Spec.map (CommRingCat.ofHom ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))) := by
    have a := Over.w (toUnit (TF (R := R) F))
    exact ((Category.comp_id _).symm.trans a).trans (Spec.map_comp _ _).symm
  rw [e₂]
  have n := Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))))
  have i : Function.Injective ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
      CommRingCat.ofHom ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))).hom :=
    ((algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R (FractionRing R))).comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
  rw [← n] at i
  exact Function.Injective.of_comp (f := (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom) i

theorem eq_zero_of_pullG (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
    (σ : U.SecGT (𝟙_ _) k) (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)))
    (h : U.PullG F (toUnit _) k σ t) (ht : ∀ j, t.f j = 0) (j) : σ.f j = 0 := by
  have hs : Smooth G.hom := U.semi.smooth
  have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (TF (R := R) F).left := inferInstanceAs (IsAffine (Spec _))
  refine GlobalTheory.sec_eq_zero_of_sval_whiskerRight_eq_zero _ G (𝟙_ _) (TF (R := R) F) (toUnit _) (appTop_injective F)
    _ U.P.L.L U.P.L.isLB _ _ _ σ (fun z J hJ => ?_) j
  have w : (snd (TF (R := R) F) G).left ≫ G.hom =
      ((fst (TF (R := R) F) G).left ≫ jFK (R := R) F) ≫ jK R :=
    (Over.w (snd (TF (R := R) F) G)).trans ((Over.w (fst (TF (R := R) F) G)).symm.trans (Category.assoc _ _ _).symm)
  let y : (TF (R := R) F ⊗ G).left ⟶ ((Over.pullback (jK R)).obj G).left := pullback.lift _ _ w
  have e₄ : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
  have w' : (fst (TF (R := R) F) G).left ≫ jFK (R := R) F = (y ≫ U.gen.hom.left) ≫ A.A.hom := by
    rw [Category.assoc, e₄]
    exact (pullback.lift_snd _ _ _).symm
  let rA : (TF (R := R) F ⊗ G).left ⟶ (TFK (R := R) F ⊗ A.A).left := pullback.lift _ _ w'
  obtain ⟨JA, hJA⟩ := exists_good_pt A.isLB z
  refine (h _ rA y (toUnit (TF (R := R) F) ▷ G).left (pullback.lift_snd _ _ _) ?_ ?_ z JA J hJA hJ).symm.trans ?_
  · exact (congrArg CommaMorphism.left (whiskerRight_snd (toUnit (TF (R := R) F)) G)).trans
      (pullback.lift_fst _ _ w).symm
  · refine (congrArg CommaMorphism.left (whiskerRight_fst (toUnit (TF (R := R) F)) G)).trans ?_
    rw [← Category.assoc]
    exact congrArg (· ≫ (toUnit (TF (R := R) F)).left) (pullback.lift_fst _ _ w').symm
  · exact (congrArg (_ * ·) ((congrArg (gs rA z _) (ht _)).trans (gs_zero _ _ _))).trans (mul_zero _)

end

theorem exists_smul_of_finrank_one {F B M : Type} [Field F] [CommRing B] [AddCommGroup M] [Module B M]
    (e : F ≃+* B) (h : Module.finrank B M = 1) {v : M} (hv : v ≠ 0) (w : M) : ∃ c : F, e c • v = w := by
  letI : Field B := (e.symm.toMulEquiv.isField (Field.toIsField F)).toField
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (K := B) v hv).1 h w
  exact ⟨e.symm c, by rw [e.apply_symm_apply]; exact hc⟩

theorem expF_one_dim : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ (th : LB.Sec (LPow A.A A.L ((1 : ℕ) : ℤ) (TFK (R := V) (Kbar V)))) (s₀ : Raw D (Kbar V) 1), U.PullG (Kbar V) (toUnit _) 1 θ th → PullB D (Kbar V) (toUnit _) 1 f s₀ → (∃ j, th.f j ≠ 0) ∧ U.ExpF (Kbar V) 1 th s₀ ∧ ∀ t s, U.ExpF (Kbar V) 1 t s → ∃ c : (Kbar V), ∀ α j, (s α).f j = DegPre.constBF D (Kbar V) c _ * (s₀ α).f j) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U θ f hθ th s₀ hG hB
  have hne : ∃ j, th.f j ≠ 0 := by
    by_contra hn
    obtain ⟨j, hj⟩ := hθ.2
    exact hj (eq_zero_of_pullG U (Kbar V) 1 θ th hG (fun j => by_contra fun h => hn ⟨j, h⟩) j)
  have hE := GlobalTheory.expF_of_pull V D _ A G U (Kbar V) 1 θ f th s₀ hθ.1 hG hB
  refine ⟨hne, hE, fun t s hts => ?_⟩
  obtain ⟨-, -, hr, -⟩ := GlobalTheory.ThetaRep.exists_projective_rep hL hL2 _ A (Kbar V) (jFK (R := V) (Kbar V)) 1
    (by rw [Nat.cast_one]; exact one_ne_zero)
  rw [one_pow] at hr
  have hv : SecM.ofSec A.A th ≠ 0 := fun h => by
    obtain ⟨j, hj⟩ := hne
    exact hj (congrFun (congrArg Subtype.val h) j)
  obtain ⟨c, hc⟩ := exists_smul_of_finrank_one
    (Scheme.ΓSpecIso (CommRingCat.of (Kbar V))).symm.commRingCatIsoToRingEquiv hr hv (SecM.ofSec A.A t)
  let s' : Raw D (Kbar V) 1 := fun α =>
    ⟨fun j => DegPre.constBF D (Kbar V) c _ * (s₀ α).f j, fun i j => by
      rw [map_mul, map_mul, (s₀ α).compat i j, mul_left_comm]
      congr 2
      exact fn_ext fun x hx => (gs_res _ x _ hx _).trans ((gs_res _ x _ hx.1 _).trans
        ((gs_res _ x _ hx _).trans (gs_res _ x _ hx.2 _)).symm)⟩
  have hs' : U.ExpF (Kbar V) 1 t s' :=
    GlobalTheory.UU.ExpLin.expF_linear V hV D A G U (Kbar V) 1 th (zeroSec _) t s₀ (fun _ => zeroSec _) s' c hE
      (expF_zero U _ 1) (fun j => ((congrFun (congrArg Subtype.val hc) j).symm).trans (add_zero _).symm)
      (fun α j => (add_zero _).symm)
  have e : s = s' := (_root_.GlobalTheory.UU.ExpFUniq.main V hV D A G U (Kbar V) 1 t t s s' hts hs').1 rfl
  exact ⟨c, fun α j => by rw [e]⟩

end GlobalTheory.UU.OneDim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteSublevel
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefVal
open TWM TWO SectionScalarValuation

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem isPullback_jO : IsPullback (jO hϖ hv (D := D)).left (fst (TF (R := V) F) D.toPre.P.A).left
    (fst (TO hϖ hv) D.toPre.P.A).left (Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F))) := by
  have H₁ : IsPullback (snd (TO hϖ hv) D.toPre.P.A).left (fst (TO hϖ hv) D.toPre.P.A).left D.toPre.P.A.hom
      (TO hϖ hv).hom := (IsPullback.of_hasPullback (TO hϖ hv).hom D.toPre.P.A.hom).flip
  have H₀ : IsPullback (DegPre.prB D.toPre F).left (fst (TF (R := V) F) D.toPre.P.A).left D.toPre.P.A.hom
      (TF (R := V) F).hom := (IsPullback.of_hasPullback (TF (R := V) F).hom D.toPre.P.A.hom).flip
  rw [← jO_snd hϖ hv, ← Over.w (ιS hϖ hv)] at H₀
  exact H₀.of_right (jO_fst hϖ hv) H₁


include hϖ hv in
theorem exists_vge (hTW : TwistBCSpanStatement) {k : ℕ} (hk : 1 ≤ k) {α : D.toPre.X}
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))) : ∃ r : ℚ, VGe D F v k α s r := by
  have hL := D.toPre.P.isLB
  have := D.toPre.P.isAb.proper
  have hp : IsProper (fst (TO hϖ hv) D.toPre.P.A).left :=
    inferInstanceAs (IsProper (pullback.fst (TO hϖ hv).hom D.toPre.P.A.hom))
  have : CompactSpace (TO hϖ hv).left := inferInstanceAs (CompactSpace (Spec (CommRingCat.of (Ov v))))
  have : QuasiSeparatedSpace (TO hϖ hv).left := inferInstanceAs (QuasiSeparatedSpace (Spec (CommRingCat.of (Ov v))))
  have : CompactSpace (TO hϖ hv ⊗ D.toPre.P.A).left :=
    QuasiCompact.compactSpace_of_compactSpace (fst (TO hϖ hv) D.toPre.P.A).left
  have : QuasiSeparatedSpace (TO hϖ hv ⊗ D.toPre.P.A).left :=
    (quasiSeparated_iff_quasiSeparatedSpace (fst (TO hϖ hv) D.toPre.P.A).left).mp inferInstance
  obtain ⟨s₁, hs₁⟩ := exists_sec hL (φ' := fun i => (jO hϖ hv (D := D)).left ≫
      (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α i) (ε' := DegPre.famε k)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      rw [GC.famφ_eq, ← jO_snd hϖ hv, Category.assoc]) s
  obtain ⟨t, ht, S, hS⟩ := TwistLoc.exists_clear_denominator (nonZeroDivisors (Ov v)) (isPullback_jO hϖ hv (D := D)) hL
    (fun i => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k) s₁
  obtain ⟨n, rr, σ, hσ⟩ := hTW V D.toPre k hk α (Ov v) (fO v hϖ hv) inferInstance S
  choose σF hσF using fun i => FamInt.exists_pull (D := D) (F := F) (σ i)
  have ht0 : (t : F) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := F) ht
  obtain ⟨r, hr⟩ := wt_coe_of_ne (v := v) (inv_ne_zero ht0)
  refine ⟨r, n, fun i => (t : F)⁻¹ * ιr (v := v) (rr i), σ, σF, hσF, fun i => ?_, fun j => ?_⟩
  · rw [AddValuation.map_mul, hr]
    exact le_add_of_nonneg_right (v_ιr _)
  refine (sec_ext_val hL (s' := FamInt.secLin (fun i => gF D.toPre F ((t : F)⁻¹ * ιr (v := v) (rr i))) σF)
    (fun y J hJ => ?_) j).trans rfl
  rw [sval_lin (s := FamInt.secLin _ _) (fun i => gF D.toPre F ((t : F)⁻¹ * ιr (v := v) (rr i))) σF (fun _ => rfl) _ y hJ]
  have e₁ : sval S (𝟙 _ ≫ (jO hϖ hv (D := D)).left) y J = gs (𝟙 _) y ⊤ (gF D.toPre F t) * sval s (𝟙 _) y J := by
    rw [← hs₁ _ _ y J hJ, sval_of S (𝟙 _ ≫ (jO hϖ hv (D := D)).left) y J (fun a => J (𝟙 _ ≫ (jO hϖ hv (D := D)).left ≫
      (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α a)) (fun a => by rw [Category.assoc])]
    refine (hS _ (𝟙 _) y _ (hJ.mem (fun a => (jO hϖ hv (D := D)).left ≫
      (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α a) (𝟙 _))).trans (congrArg₂ (· * ·) ?_ rfl)
    have e := gs_jO hϖ hv (D := D) (𝟙 _) y ((Scheme.ΓSpecIso (CommRingCat.of (Ov v))).inv.hom t)
    rw [show ιr (v := v) ((Scheme.ΓSpecIso (CommRingCat.of (Ov v))).inv.hom t) = (t : F) by simp [ιr]] at e
    rw [← e, ← Category.assoc]
    exact (gs_pull _ _ y ⊤ trivial _).symm
  have e₂ := sval_lin (fun l => (fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom (rr l))
      (fun l => pullSec D.toPre.P.L _ _ (σ l) (snd (TO hϖ hv) D.toPre.P.A).left) (fun j => hσ j)
      (𝟙 _ ≫ (jO hϖ hv).left) y hJ
  have g : ∀ a b : F, gs (𝟙 _) y ⊤ (gF D.toPre F (a * b)) =
      gs (𝟙 _) y ⊤ (gF D.toPre F a) * gs (𝟙 _) y ⊤ (gF D.toPre F b) := fun a b => by
    rw [map_mul, gs_mul _ y ⊤ trivial]
  have g₁ : gs (𝟙 _) y ⊤ (gF D.toPre F (t : F)⁻¹) * gs (𝟙 _) y ⊤ (gF D.toPre F t) = 1 := by
    rw [← g, inv_mul_cancel₀ ht0, map_one, gs_eq _ _ ⊤ trivial, map_one, map_one]
  rw [← _root_.one_mul (sval s _ y J), ← g₁, _root_.mul_assoc, ← e₁, e₂, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [g, gs_jO, sval_pullSec _ _ _ _ _ y hJ, Category.assoc, jO_snd, secScal_sval (hσF i) _ y hJ, _root_.mul_assoc]


include hϖ hv in
theorem exists_nuGe (hTW : TwistBCSpanStatement) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) {k : ℕ} (hk : 1 ≤ k)
    (s : Fam D.toPre F k) : ∃ r : ℚ, NuGe D Q F v k s r := by
  classical
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul D.toPre.X k hk
  choose r hr using fun i => exists_vge hϖ hv hTW hk (s.s (e i))
  obtain ⟨m, hm⟩ := (Set.finite_range fun i => (Q (e i) : ℚ) / k - r i).bddAbove
  refine ⟨-m, ?_⟩
  rw [n1a V ϖ hϖ D Q hQ _ _ hv k hk (Finset.univ.image e) (fun χ => by
    obtain ⟨i, hi, -⟩ := he χ
    exact ⟨e i, Finset.mem_image_of_mem _ (Finset.mem_univ i), hi⟩) s]
  intro α hα
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hα
  have := hm ⟨i, rfl⟩
  exact VGe.mono (hr i) (by linarith)


include hϖ in
theorem finite_sublevel {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) {k : ℕ} (hk : 1 ≤ k) (l : D.toPre.X →+ ℚ)
    (q : ℚ) : {χ | (Q χ : ℚ) / k + l χ ≤ q}.Finite := by
  let β : LinearMap.BilinForm ℤ D.toPre.X := LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ D hQ a b)
    (fun a a' b => by simp) (fun c a b => by simp) (fun a b b' => by simp) (fun c a b => by simp)
  have hβ : ∀ a, β a a = 2 * Q a := fun a => (QForm.two_Q_eq hϖ D hQ a).symm
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine (ClassMin.finite_affine_sublevel (ClassMin.realExtension_ofIntBilin_posDef (β := β)
    (fun a b => QForm.bOf_comm D a b) (fun a ha => by have := QForm.Q_pos hϖ D hQ ha; rw [hβ]; omega))
    (inv_pos.2 hk') ((Rat.castHom ℝ).toAddMonoidHom.comp l) q).subset fun χ hχ => ?_
  have h : (((Q χ : ℚ) / k + l χ : ℚ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hχ
  show (k : ℝ)⁻¹ * ClassMin.ofIntBilin β χ + (l χ : ℝ) ≤ q
  rw [ClassMin.ofIntBilin_apply, hβ]
  push_cast at h ⊢
  refine le_of_eq_of_le ?_ h
  field_simp

end GlobalTheory.UT.CoefVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInMaximalIdealOfNeZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem psiIn_maximalIdeal_of_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V), D.TauBimult → D.PsiEven → {χ : D.X | ¬ D.PsiIn χ (IsLocalRing.maximalIdeal V ^ 1)}.Finite → ∀ χ : D.X, χ ≠ 0 → D.PsiIn χ (IsLocalRing.maximalIdeal V) := by
  intro V _ _ _ hV D hT hE hfin χ hχ
  have : IsDiscreteValuationRing V := hV.1
  obtain ⟨ga, a, ha⟩ := exists_psiScal V D
  have hc := GlobalTheory.T.psiScalars_relations_up_to_baseUnits V D ga a ha
  have hm : IsLocalRing.maximalIdeal V ≠ ⊥ := IsDiscreteValuationRing.not_a_field V
  have hiff := fun x => psiIn_iff_scalar_mem V D ga a ha x _ hm
  rw [hiff]
  refine cubeRel_scalars_mem_maximalIdeal V D.X a (hc.1 hT) (hc.2 hE) ?_ χ hχ
  refine hfin.subset ?_
  intro x hx
  show ¬ _
  rw [pow_one, hiff]
  exact hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiTendstoZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem psi_tendsto_zero : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → (∃ j, (f 0).f j ≠ 0) → PsiRel D (𝟙_ _) f → ∀ n : ℕ, {χ : D.X | ¬ D.PsiIn χ (IsLocalRing.maximalIdeal V ^ n)}.Finite) := by
  intro V _ _ _ hV D A G _ _ U θ f hθ h0 hR n
  haveI := hV.1
  obtain ⟨ga, a, hS⟩ := exists_psiScal V D
  obtain ⟨m, hm⟩ := exists_order_translates V hV D 1 (f 0) h0
  obtain ⟨s, hs⟩ := LevelVanishing.main V hV D A G U 1 θ f hθ.1 (m + n)
  refine s.finite_toSet.subset fun χ hχ => ?_
  by_contra hn
  apply hχ
  have hne : IsLocalRing.maximalIdeal V ^ n ≠ ⊥ := pow_ne_zero n (IsDiscreteValuationRing.not_a_field V)
  refine (psiIn_iff_scalar_mem V D ga a hS χ _ hne).2 ?_
  obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors V) (a χ).val
  obtain ⟨z, J, hJ, hz⟩ := hm χ
  have hq : (q : V) ≠ 0 := nonZeroDivisors.coe_ne_zero q
  have e := PsiInt.psiRel_integral V D ga a f hS hR χ p q (by rw [mul_comm]; exact hpq) (𝟙_ _ ⊗ D.P.A) (snd _ _) z J hJ
  have e₁ : lift (toUnit (𝟙_ _ ⊗ D.P.A)) (snd (𝟙_ _) D.P.A) = 𝟙 _ := by
    ext1
    · exact toUnit_unique _ _
    · simp
  have e₂ : toUnit (𝟙_ _ ⊗ D.P.A) = fst (𝟙_ _) D.P.A := toUnit_unique _ _
  haveI : Flat D.P.A.hom := by
    haveI := D.P.isAb.smooth
    infer_instance
  haveI : Flat (𝟙_ _ ⊗ D.P.A).hom := by
    have h : (𝟙_ _ ⊗ D.P.A).hom = (λ_ D.P.A).hom.left ≫ D.P.A.hom := (Over.w _).symm
    haveI : IsIso (λ_ D.P.A).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (λ_ D.P.A).hom))
    rw [h]
    infer_instance
  let io := (((𝟙_ _ ⊗ D.P.A).left.presheaf.germ ⊤ z trivial).hom.comp (((𝟙_ _ ⊗ D.P.A).hom.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom))
  have hio : ∀ v : V, gs (𝟙 _) z ⊤ (scal (𝟙_ _ ⊗ D.P.A).hom v) = io v := fun v => gs_eq _ _ ⊤ trivial _
  have hio' : ∀ v : V, cst (𝟙_ _ ⊗ D.P.A).hom z v = io v := fun v => gs_eq _ _ ⊤ trivial _
  rw [hio, hio, e₁] at e
  have hf := hs χ hn z J hJ
  have hf' := Ideal.map_mono (f := io) (Ideal.pow_le_pow_right (Nat.le_succ (m + n))) hf
  obtain ⟨r, hr, hp⟩ := exists_mem_pow_of_ratio_of_torsionFree V _ io
    (fun v hv x hx => by
      have := cst_regular (𝟙_ _ ⊗ D.P.A).hom z hv
      rw [hio'] at this
      exact this (hx.trans (mul_zero _).symm))
    _ _ p q m n hq e hf' (fun h => hz (by
      rw [← e₂]
      exact (Ideal.unit_mul_mem_iff_mem _ (Units.isUnit _)).1 h))
  refine ⟨r, hr, ?_⟩
  have hq' : algebraMap V (FractionRing V) q ≠ 0 := (IsLocalization.map_units _ q).ne_zero
  apply mul_right_cancel₀ hq'
  rw [← map_mul, ← hp]
  exact hpq.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUOfIntegralTorsionPointStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qkToAkU_of_integral_torsion_point : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (k : ℕ), 1 ≤ k → ∀ (x : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) (gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))), x ^ k = 1 → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (p : QkPt D.toPre F k) (xF : TFK (R := R) F ⟶ A.A), p.y = 0 → GtPt.IsPullF F (toUnit (TF (R := R) F)).left gp p.g → xF.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = (toUnit (TF (R := R) F) ≫ x).left → QkToAkU U.toUnifPre F k p xF := by
  first | exact @GlobalTheory.qkToAkU_of_integral_torsion | exact GlobalTheory.qkToAkU_of_integral_torsion | (intros; apply GlobalTheory.qkToAkU_of_integral_torsion <;> assumption)
end

