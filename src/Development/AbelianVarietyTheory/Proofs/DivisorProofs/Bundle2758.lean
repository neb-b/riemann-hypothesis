module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2734
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpandsFScale
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2721
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0668
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2424
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2735
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0523
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0544

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataTorsionIsometryOnto
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

theorem GlobalTheory.Mum.TensTor.zpow_sum_tens {M κ : Type} [CommGroup M] (a : M) (s : Finset κ) (f : κ → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

theorem GlobalTheory.Mum.TensTor.tate_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → (letI := H.starRing; TraceFormTwistIso D'.toPre o H.w0) → ∀ (Dm : Datum H) (g : ℕ) (e : Dm.La ≃+ (Fin r → (Fin g → ℤ) × (Fin g → ℤ))), g = D.toPre.P.g + Module.finrank ℤ D.toPre.X → (∀ (a : 𝓞 E) x i, e (a • x) i = ∑ j, ρ a i j • e x j) → (∀ x y, Dm.EF x y = ∑ i, ∑ j, (W + W.transpose) i j * ((e x i).1 ⬝ᵥ (e y j).2 - (e x i).2 ⬝ᵥ (e y j).1)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (ζ : ℕ → Fˣ), (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) → ∀ ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n, (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) → (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) → (∀ n, 0 < n → ∀ p, ∃ a, QkPt.Equiv D.toPre F (ev n a) p) → (∀ n m, 0 < n → 0 < m → ∀ a, ∃ q : QkPt D.toPre F n, q.y = (ev (n * m) a).y ∧ GtPtF.IsNsmul m (ev (n * m) a).g q.g ∧ QkPt.Equiv D.toPre F q (ev n a)) → (∀ n, 0 < n → ∀ a b, WeilQkIs D.toPre F n (ev n a) (ev n b) ((ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) : Fˣ) : F)) → ∃ I : TateIsoQ Dm D'.toPre o F, I.ζ = ζ := by
  intro R _ _ _ hB E _ _ _ H D D' r W _ hdet T ρ hρ _ _ o hact _ Dm g e _ he hEF F _ _ _ ζ hprim hpow ev hadd hker
    honto htow hweil

  obtain ⟨N, ⟨ν⟩⟩ := _root_.GlobalTheory.MumValues.exists_values R hB D F
  obtain ⟨N', ⟨ν'⟩⟩ := _root_.GlobalTheory.MumValues.exists_values R hB D' F
  choose P hP using fun (n : ℕ) (a : Dm.La) =>
    _root_.GlobalTheory.Mum.TensTor.exists_ptRel R hB D D' W T F N N' ν ν' n (fun j => ev n (e a j))
  refine ⟨⟨ζ, hprim, hpow, P, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  ·
    intro n hn a b
    have hs := hP n (a + b)
    simp only [map_add (f := _), Pi.add_apply] at hs
    exact _root_.GlobalTheory.Mum.TensTor.qkAdd_of_components R hB D D' W T F N N' ν ν' n (P n a) (P n b) (P n (a + b)) _ _ _ (hP n a) (hP n b) hs
      (fun i => hadd n hn (e a i) (e b i))
  ·
    intro n hn x a
    have hs := hP n (x • a)
    simp only [he] at hs
    exact GlobalTheory.T.tensorQuotientTorsion_orderAction_matrix R hB D D' W T F N N' ν ν' E H ρ hρ o hact g ev hadd hker n hn x (fun j => e a j)
      (P n a) (P n (x • a)) (hP n a) hs
  ·
    intro n hn a b
    rw [_root_.GlobalTheory.Mum.TensTor.qkPt_equiv_iff_components R hB D D' W T F N N' ν ν' hdet n (P n a) (P n b) _ _ (hP n a) (hP n b)]
    simp only [hker n hn]
    constructor
    · intro h
      choose c hc using h
      refine ⟨e.symm c, e.injective ?_⟩
      rw [map_add (f := _), map_nsmul, e.apply_symm_apply]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, hc i]
    · rintro ⟨c, rfl⟩ i
      exact ⟨e c i, by simp only [map_add (f := _), map_nsmul, Pi.add_apply, Pi.smul_apply]⟩
  ·
    intro n hn p
    obtain ⟨ps, hps⟩ := _root_.GlobalTheory.Mum.TensTor.exists_components_of_unimodular R hB D D' W T F N N' ν ν' hdet n p
    choose a ha using fun i => honto n hn (ps i)
    refine ⟨e.symm a, ?_⟩
    rw [_root_.GlobalTheory.Mum.TensTor.qkPt_equiv_iff_components R hB D D' W T F N N' ν ν' hdet n (P n (e.symm a)) p _ ps (hP n (e.symm a)) hps]
    intro i
    simpa only [e.apply_symm_apply] using ha i
  ·
    intro n m hn hm a
    exact _root_.GlobalTheory.Mum.TensTower.tower R hB D D' W T F N N' ν ν' n m hn hm (P (n * m) a) _ (P n a) _ (hP (n * m) a) (hP n a)
      (fun i => htow n m hn hm (e a i))
  ·

    intro n hn a b
    have h := _root_.GlobalTheory.Mum.TensTor.weilQk_tens R hB D D' W T F N N' ν ν' n hn (P n a) (P n b) _ _ (hP n a) (hP n b)
      (fun i j => ζ n ^ ((e a i).1 ⬝ᵥ (e b j).2 - (e a i).2 ⬝ᵥ (e b j).1)) (fun i j => hweil n hn (e a i) (e b j))
    have key : (∏ i, ∏ j, (ζ n ^ ((e a i).1 ⬝ᵥ (e b j).2 - (e a i).2 ⬝ᵥ (e b j).1)) ^ (W + W.transpose) i j) =
        ζ n ^ Dm.EF a b := by
      rw [hEF a b, zpow_sum_tens]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [zpow_sum_tens]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← zpow_mul, mul_comm ((W + W.transpose) i j)]
    beta_reduce at h
    rwa [key] at h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTwoLevelsPrimitiveAtTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstants_two_levels_primitive_at_trait : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (y : Sp (FractionRing V) ⟶ S) (P : PolAV (Sp (FractionRing V))) (α : P.A.left ⟶ G.left), IsGrpPullback P.A G y α → LBIso P.L (L.pull α) → (letI := P.isAb.comm; HypS P.A P.L) → ∀ (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing V →+* K) (m m' N N' : ℕ) (d : Fin N → K) (d' : Fin N' → K), Odd m → 3 ≤ m → IsUnit (m : V) → Odd m' → 3 ≤ m' → IsUnit (m' : V) → HasTh₂ G L ρ m m' (spMap io ≫ y) d d' → ∃ a : K, a ≠ 0 ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d b / a) ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d' b / a) := by
  first | exact @GlobalTheory.SiegCmp.theta_two_levels_prim | exact GlobalTheory.SiegCmp.theta_two_levels_prim | (intros; apply GlobalTheory.SiegCmp.theta_two_levels_prim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyTermsEqUpToNormalisingThetaConst
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.Sep.TermsCompare

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (F : Type) [Field F] [Algebra (FractionRing R) F]


open GlobalTheory.FieldBaseChange GlobalTheory.ExpFieldCompare in
theorem exists_expandsF_pow {w w' : W0 U} (hw : w.IsGen) (hw' : w'.IsGen) : ∃ d : F, d ≠ 0 ∧
    ∀ (k : ℕ) t s, U.ExpandsF F k w' t s → U.ExpandsF F k w t (d ^ k • s) := by
  obtain ⟨u, hu⟩ := exists_isoVal_ratio A.isLB U.LG.isLB hw' hw
  obtain ⟨c₀, hc₀, huc⟩ := BoxExpansion.unit_const GlobalTheory.firstFiveLaws.1.globalFns A U.gen u
  refine ⟨algebraMap (FractionRing R) F c₀, (map_ne_zero _).2 hc₀, fun k t s h => ?_⟩
  obtain ⟨v, h₁, h₂⟩ := h
  have z : U.ExpandsG F k (0 : GroupSec U F k) 0 := (expandsG_iff U F k _ _).2
    ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, (Fin.sum_univ_zero _).symm,
      fun α => (map_zero _).trans (Fin.sum_univ_zero _).symm⟩
  have h₃ := expandsG_lin U F k (algebraMap (FractionRing R) F c₀ ^ k) h₂ z
  rw [add_zero, add_zero] at h₃
  refine ⟨_, ?_, h₃⟩
  refine (isoRelM_iff w (prGK G F) k (U.genF F).left h₁.1 (𝟙 _) h₁.2.1 t _).2 fun y a b ha hb => ?_
  have e := (isoRelM_iff w' (prGK G F) k (U.genF F).left h₁.1 (𝟙 _) h₁.2.1 t v).1 h₁ _ (𝟙 _) y a b ha hb
  have e₃ : (𝟙 _ ≫ prGK G F) ≫ ((Over.pullback (jK R)).obj G).hom =
      ((𝟙 _ ≫ 𝟙 _) ≫ groupBase G F) ≫ jFK (R := R) F := by
    simp only [Category.id_comp]
    exact (isPullback_groupBase F).w
  have e₄ : (gm (𝟙 _ ≫ prGK G F) y ⊤ u).val = BoxExpansion.constHomVal ((𝟙 _ ≫ 𝟙 _) ≫ groupBase G F) y
      (algebraMap (FractionRing R) F c₀) :=
    ((gs_unit (𝟙 _ ≫ prGK G F) y ⊤ trivial u).symm.trans
      (congrArg (gs _ y ⊤) huc)).trans ((gs_scal _ _ y c₀).trans ((congrArg (fun q => constVal q y c₀) e₃).trans
        ((constVal_specMap _ _ y c₀).trans (BoxExpansion.constVal_eq _ _ _))))
  refine (powVal_smul (π := groupBase G F) _ v (𝟙 _ ≫ 𝟙 _) y (i := a) ha).trans ?_
  rw [e, hu _ (𝟙 _ ≫ prGK G F) y a b ha hb, mul_zpow, Units.val_mul, BoxExpansion.constVal_eq, map_pow, ← e₄,
    zpow_natCast (gm _ _ _ _), Units.val_pow_eq_pow_val, _root_.mul_assoc]


variable {F} in
theorem valAt_congr {k : ℕ} {t : SecA A F k} {x : TFK (R := R) F ⟶ A.A} {e e' : FrAt x} {c : F}
    (h : ∀ z J, Good A.L z J → val e (𝟙 _) z J = val e' (𝟙 _) z J) (H : ValAt t x e c) : ValAt t x e' c := fun z J hJ => by
  refine (H z J hJ).trans ?_
  rw [GlobalTheory.FrameMove.val_powFrame, GlobalTheory.FrameMove.val_powFrame, h z J hJ]


variable {F} in
theorem sec_eq_of_valAt (hT : SecTwistSt) {t t' : SecA A F 1} {x : TFK (R := R) F ⟶ A.A} {e : FrAt x} {c : F} (hc : c ≠ 0)
    (H : ValAt t x e c) (H' : ValAt t' x e c) : t = t' := by
  obtain ⟨b, hb⟩ := GlobalTheory.PowBasis.exists_basis_pow_field hT R A F 1 le_rfl
  have hq : Subsingleton (Fin (1 ^ A.g)) := by rw [one_pow]; infer_instance
  obtain ⟨i₀⟩ : Nonempty (Fin (1 ^ A.g)) := by rw [one_pow]; infer_instance
  obtain ⟨r, hr, -⟩ := hb t
  obtain ⟨r', hr', -⟩ := hb t'
  simp only [Fintype.sum_subsingleton _ i₀] at hr hr'
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' A.isLB z
  have a := (GlobalTheory.ThetaCompare.sval_smul hr x hJ).symm.trans (H z J hJ)
  have a' := (GlobalTheory.ThetaCompare.sval_smul hr' x hJ).symm.trans (H' z J hJ)
  obtain ⟨q, hq'⟩ := CoefBasic.cstH_surj (R := R) z (sA (b i₀) (ptSecT A.A x).left z J)
  have b₁ : CoefBasic.cstH (R := R) z (r i₀) * CoefBasic.cstH (R := R) z q =
      CoefBasic.cstH (R := R) z c * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (powFrame A.A A.L x e (1 : ℕ)) (𝟙 _) z J)).val := by
    rw [hq', ← CoefBasic.cst_eq, ← CoefBasic.cst_eq]; exact a
  have b₂ : CoefBasic.cstH (R := R) z (r' i₀) * CoefBasic.cstH (R := R) z q =
      CoefBasic.cstH (R := R) z c * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (powFrame A.A A.L x e (1 : ℕ)) (𝟙 _) z J)).val := by
    rw [hq', ← CoefBasic.cst_eq, ← CoefBasic.cst_eq]; exact a'
  have q0 : q ≠ 0 := fun h => by
    rw [h, map_zero, mul_zero] at b₁
    exact hc (CoefBasic.cstH_inj z (((Units.mul_left_eq_zero _).1 b₁.symm).trans (map_zero _).symm))
  have e₀ : r i₀ = r' i₀ := by
    have := b₁.trans b₂.symm
    rw [← map_mul, ← map_mul] at this
    exact mul_right_cancel₀ q0 (CoefBasic.cstH_inj z this)
  have e₁ : ∀ j, t.f j = t'.f j := fun j => by
    have := hr j
    have e₂ : r = r' := funext fun i => by rw [Subsingleton.elim i i₀]; exact e₀
    rw [e₂] at this
    exact this.trans (hr' j).symm
  obtain ⟨f, _⟩ := t
  obtain ⟨f', _⟩ := t'
  obtain rfl : f = f' := funext e₁
  rfl

variable {F} in
theorem coef_smul {k : ℕ} (g : GtPtF D.toPre F) {w : Frm D.toPre F k g.b} (hw : w.IsGen) (c : F) (s : Fam D.toPre F k) (χ) :
    coef (c • s) g w χ = c * coef s g w χ := by
  have h₁ := ((CoefBasic.coef_basic R D.toPre F k g).2.2 w hw).2.1
  have h₂ : coef (0 : Fam D.toPre F k) g w χ = 0 := by
    have := h₁ 0 0 1 χ
    rw [one_smul, add_zero, _root_.one_mul] at this
    exact left_eq_add.1 this
  have := h₁ s 0 c χ
  rwa [add_zero, h₂, add_zero] at this


variable {U F} in
theorem liesOver_change {w₀ w₀' : W0 U} {d : F}
    (hd : ∀ (k : ℕ) t s, U.ExpandsF F k w₀ t s → U.ExpandsF F k w₀' t (d ^ k • s)) {g : GtPtF D.toPre F}
    {w w' : Frm D.toPre F 1 g.b} (hw' : w'.IsGen)
    (hv : ∀ z J, Good D.toPre.P.L z J → (val w (𝟙 _) z J).val = cst F z d * (val w' (𝟙 _) z J).val)
    {x : TFK (R := R) F ⟶ A.A} {e e' : FrAt x} (he : ∀ z J, Good A.L z J → val e (𝟙 _) z J = val e' (𝟙 _) z J)
    (H : LiesOver U w₀' g w' x e') : LiesOver U w₀ g w x e := by
  intro k hk wk hwk _ s s' v hs hval
  obtain ⟨W, hW, hWv⟩ := TorsionValue.exists_frm_pow w' hw' k
  have a := H k hk W hWv hW s _ v (hd k s s' hs) (valAt_congr he hval)
  have sc := TorsionValue.coef_scale (w' := wk) hW (c := d ^ k) (fun z J hJ => by
    rw [hwk z J hJ, hWv z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hv z J hJ, mul_pow,
      CoefBasic.cst_eq, CoefBasic.cst_eq, map_pow]) s'
  convert a using 1
  funext χ
  rw [sc, coef_smul g hW]

end

theorem terms_eq : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x x' : X₁.S.Gam) (C C' : Type) (lab : C → X₁.S.Gam) (lab' : C' → X₁.S.Gam) (T : (Fin 8 → X) → C → V) (T' : (Fin 8 → X) → C' → V), 𝔪.Terms x lab T → 𝔪.Terms x' lab' T' → ∀ (c : C) (c' : C'), lab c = lab' c' → ∀ mu, algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x, X₁.S.th_mem x⟩ = algebraMap V (FractionRing V) (T' mu c') * 𝔪.yK ⟨X₁.S.th x', X₁.S.th_mem x'⟩ := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 x₀ x₀' C C' lab lab' T T' hT hT' c c' hc mu
  obtain ⟨x, fr, th, w₀, s, p, w, hx, hfr, hth, hw₀, hs, hg, hT⟩ := hT
  obtain ⟨x', fr', th', w₀', s', p', w', hx', hfr', hth', hw₀', hs', hg', hT'⟩ := hT'
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain rfl : x = x' := funext fun a => Over.OverMorphism.ext
    (𝔪.cart.1.hom_ext ((hx a).trans (hx' a).symm) ((Over.w (x a)).trans (Over.w (x' a)).symm))
  have hf : ∀ a z J, Good 𝔪.A.L z J → val (fr a) (𝟙 _) z J = val (fr' a) (𝟙 _) z J := fun a z J hJ => by
    obtain ⟨J₀, hJ₀⟩ := CoefBasic.exists_good' X₁.ρ.P.isLB z
    exact mul_left_cancel (((hfr a).2 z J₀ J hJ₀ hJ).trans ((hfr' a).2 z J₀ J hJ₀ hJ).symm)
  obtain ⟨a, ha⟩ := GlobalTheory.ThetaGeneric.exists_th_ne_zero hL.1 hL.2.1 _ _ X₁.S X₁.ρ (FractionRing V) 𝔪.yK
  obtain rfl : th = th' := sec_eq_of_valAt hL.2.1.secTwist ha (valAt_congr (hf a) (hth a)) (hth' a)
  obtain ⟨d, hd0, hd⟩ := exists_expandsF_pow 𝔪.U.toUnifPre (FractionRing V) hw₀' hw₀
  have hbij := (expBijF_and_expandsF_lin hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U).1 (FractionRing V) 1 le_rfl w₀' hw₀'
  obtain rfl : s' = d ^ 1 • s := (hbij.1 th).unique hs' (hd 1 th s hs)
  obtain ⟨h₁, h₂, h₃⟩ := hg c
  obtain ⟨h₁', h₂', h₃'⟩ := hg' c'
  rw [hT, hT']
  rw [← hc] at h₃'
  obtain ⟨w₁, hw₁, hv₁⟩ := TorsionValue.exists_frm_scale (w' c') h₂' hd0
  have h₄ : LiesOver 𝔪.U.toUnifPre w₀ (p' c') w₁ (x (lab c)) (fr (lab c)) :=
    liesOver_change hd h₂' hv₁ (hf _) h₃'
  obtain ⟨e, ev⟩ := GlobalTheory.T.framedTorsionPoint_torusExtension_eq_of_liesOver V 𝔪.cn 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ _ hk _ _ _ _ _ _ h₁ h₁' h₂ hw₁ (hfr _).1 h₃ h₄
  rw [coef_smul _ h₂', pow_one]
  generalize w c = om at h₂ ev
  generalize p c = q at om h₂ e ev
  subst e
  exact TorsionValue.coef_scale h₂' (fun z J hJ => by rw [ev z J hJ, hv₁ z J hJ]) s _

end GlobalTheory.Poinc.Sep.TermsCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridAlphaBetaRestrictQuadraticPowRank
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareResChars

theorem resEta_mul_pow {D : D7} {c η : (AE D)ˣ →* Circle} (hc : ResEta D c 0) (hη : ResEta D η 1) {n k : ℕ}
    (h : n % 2 = k % 2) : ResEta D (c * η ^ (n % 2)) k := by
  rcases Nat.mod_two_eq_zero_or_one n with e | e
  · rw [e, pow_zero, mul_one]
    exact resEta_parity hc (by omega)
  · rw [e, pow_one]
    exact resEta_parity (resEta_mul hc hη) (by omega)

theorem resEta_alpha_beta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), GlobalTheory.LFun.ResEta D.host.F D.host.E (alpha G t i j) (spW₁ G i j).rank ∧
      GlobalTheory.LFun.ResEta D.host.F D.host.E (beta G i j) (spW G i j).rank := by
  intro D T L sc G μ₀ hL t i j
  have hi := i.2
  have hj := j.2
  have hη := GlobalTheory.HeckeCharacterRestriction.resEta_eta hL
  have hμ := GlobalTheory.HeckeCharacterRestriction.resEta_mu hL t j
  have hχ : ResEta D (G.ch.chi (D.R.m - i)) 0 := ⟨hη.1, fun η _ a => by
    rw [pow_zero]
    exact GlobalTheory.GridWeil.triv_base (G.ch.chi_eq _ (by omega) (by omega)) (G.ch.triv _ (by omega) (by omega)) a⟩
  have r : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b :=
    fun a b ha hb => (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank
  have hpar : (spW₁ G i j).rank % 2 = (spW G i j).rank % 2 := by
    have e : (spW G i j).rank = (spW₁ G i j).rank + D.R.t + sLen D := by
      show (G.V (.grid (i + 1) (j + 1))).rank = (G.V (.grid i j)).rank + _ + _
      rw [r _ _ (by omega) (by omega), r _ _ (by omega) (by omega)]
      simp only [rankV]
      ring
    obtain ⟨p, hp⟩ := D.R.t_odd
    obtain ⟨q, hq⟩ := odd_sLen D
    omega
  have h1 : ResEta D (alpha G t i j) (spW₁ G i j).rank := resEta_mul_pow hμ hη rfl
  have h2 : ResEta D (beta G i j) (spW G i j).rank := resEta_mul_pow hχ hη hpar
  exact ⟨h1, h2⟩

end GlobalTheory.SquareResChars
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMapAbelianSchemeNormalCharZeroBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ThetaMapGen

theorem agree_at_geom : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen →
    ∀ (g m n : ℕ) (o K : Type) [CommRing o] [Field K] [IsAlgClosed K] (z : Sp K ⟶ S) (f₁ f₂ : Sp K ⟶ PSpace o n),
    Odd m → IsUnit (m : o) → n + 1 = m ^ (4 * g) → PolFib G L g z → f₁ ≫ PSpace.str o n = f₂ ≫ PSpace.str o n →
    (∀ c : Fin (n + 1) → K, HasTh G L ρ m z c → PCrd f₁ (symTup c)) → (∀ c : Fin (n + 1) → K, HasTh G L ρ m z c → PCrd f₂ (symTup c)) → f₁ = f₂ := by
  intro S G _ _ L ρ hL hρ g m n o K _ _ _ z f₁ f₂ hm hu hn hP hs h₁ h₂
  obtain ⟨⟨θ, hθ⟩, -⟩ := _root_.GlobalTheory.UMin.gen_of_polFib S G L hL g K z hP
  have hmK : (m : K) ≠ 0 := by
    let φ : o →+* K := (Spec.preimage (f₁ ≫ PSpace.str o n)).hom
    have := hu.map φ
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨pt, c, hc⟩ := _root_.GlobalTheory.UMin.exists_thList S G L ρ hL hρ g m (n + 1) K z θ hm hmK hn hP
  have hH : HasTh G L ρ m z c := ⟨θ, pt, hθ, hc⟩
  exact (_root_.GlobalTheory.UMin.CrdUniq.main).1 o K n f₁ f₂ (symTup c) hs (h₁ c hH) (h₂ c hH)

theorem main : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m n : ℕ) (o : Type) [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (q : X ⟶ S), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * g) → Geo.Tor.IsNormalScheme X → IsLocallyNoetherian X → (∀ x : X, CharZero (X.residueField x)) → (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), PolFib G L g (x ≫ q)) → ∃ f : X ⟶ PSpace o n, f ≫ PSpace.str o n = s ∧ ThMap G L ρ m q f := by
  intro S G _ _ L ρ hL hρ g m n o _ X s q hm h3 hu hn hN hLN h0 hP
  have loc : ∀ x : X, ∃ (W : X.Opens) (h : W.toScheme ⟶ PSpace o n), x ∈ W ∧ h ≫ PSpace.str o n = W.ι ≫ s ∧
      ThMap G L ρ m (W.ι ≫ q) h := by
    intro x
    obtain ⟨U, hxU, h1, h2, h3', h4⟩ := GlobalTheory.T.exists_affineOpen_normal_noetherian_charZero X hN hLN h0 x
    exact _root_.GlobalTheory.UMin.exists_nbhd_thetaMap S G L ρ hL hρ g m n o X s q hm h3 hu hn hP U h1 h2 h3' h4 x hxU
  choose W h hxW hs hT using loc
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    haveI := (hN x).1; infer_instance
  haveI : IsReduced X := isReduced_of_isReduced_stalk X
  have hcov : (⨆ x, W x) = ⊤ := by
    rw [eq_top_iff]; intro x _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩
  obtain ⟨f, hf, hfW⟩ := _root_.GlobalTheory.ThetaGlue.glue_geom o n X s X W h hcov hs (by
    intro i j K _ _ y y' hyy
    refine agree_at_geom S G L ρ hL hρ g m n o K (y ≫ (W i).ι ≫ q) _ _ hm hu hn (by rw [← Category.assoc]; exact hP K _) ?_ ?_ ?_
    · rw [Category.assoc, hs, Category.assoc, hs, ← Category.assoc, hyy, Category.assoc]
    · intro c hc; exact hT i K y c hc
    · intro c hc
      have := hT j K y' c (by rwa [← Category.assoc, ← hyy, Category.assoc])
      exact this)
  refine ⟨f, hf, ?_⟩
  intro K _ x c hc
  let p0 : Sp K := IsLocalRing.closedPoint K
  let i := x.base p0
  have hr : Set.range x.base ⊆ Set.range (W i).ι.base := by
    rintro _ ⟨y, rfl⟩
    have : y = p0 := Subsingleton.elim _ _
    subst this
    rw [Scheme.Opens.range_ι]; exact hxW i
  let x' := IsOpenImmersion.lift (W i).ι x hr
  have hx' : x' ≫ (W i).ι = x := IsOpenImmersion.lift_fac _ _ _
  have := hT i K x' c (by rw [← Category.assoc, hx']; exact hc)
  rw [← hx', Category.assoc, hfW i]; exact this

end GlobalTheory.UMin.ThetaMapGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointFrameMulEqIntegralGeneratorsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPointFrame_mul_eq_integralGenerators : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (g : GtPtF D.toPre (FractionRing V)) (w : Frm D.toPre (FractionRing V) 1 g.b) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (fr : FrAt x), (∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) → w.IsGen → fr.IsGen → LiesOver U.toUnifPre w₀ g w x fr → ∀ (h : (𝟙_ (Over (Sp V))) ⟶ G) (g' : GtPt D.toPre (𝟙_ (Over (Sp V)))) (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => (h).left) (fun _ => 1))) (t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, (g'.b).left] (DegPre.lineε 1))), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre h g' → IntTerm.Ext U.toUnifPre x h → GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g' g → f.IsGen → t.IsGen → (∀ e : ℕ, GlobalTheory.Poinc.IntEval.TRel U.toUnifPre h g'.b f t e) → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι) (JB : ((TF (R := V) (FractionRing V)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good A.L z JA → Good U.LG.L z JG → Good D.toPre.P.L z JB → Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h).left) (fun _ => JA (x).left) * val (Z := (TF (R := V) (FractionRing V)).left) fr (𝟙 _) z JA * val w (𝟙 _) z JB = val f (toUnit (TF (R := V) (FractionRing V))).left z JG * val t (toUnit (TF (R := V) (FractionRing V))).left z JB := by
  first | exact @GlobalTheory.Poinc.IntEval.frames_mul_eq_integral | exact GlobalTheory.Poinc.IntEval.frames_mul_eq_integral | (intros; apply GlobalTheory.Poinc.IntEval.frames_mul_eq_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivialStrictHenselisationOrigin
section
open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginCut

theorem keyOrigin : GlobalTheory.LocAcyc.KeyOrigin := by
  have h₁ := GlobalTheory.T.strict_henselisation_prime_eq
  have h₂ := GlobalTheory.T.exists_noetherian_model_torsor_origin
  have h₃ := GlobalTheory.T.torsor_point_over_strictHenselisation_noetherianNormal
  unfold GlobalTheory.LocAcyc.KeyOrigin GlobalTheory.LocAcyc.KeyLocalWith GlobalTheory.LocAcyc.TorsorsTrivial
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hPm hS q hq hqu D _ _ hfin hproj hff act hbij
  obtain ⟨E, _, _, _, _, _, Q, _, hQ, j, hj, ψ, hψ, D₁, _, _, act₁, htors₁, hpull₁⟩ :=
    h₁ T O hT P φ hφ hsh hS q hq hqu D act ⟨hfin, hproj, hff, hbij⟩
  obtain ⟨A, _, _, _, _, _, _, i, hi, hil, hqA, EA, _, _, _, _, _, QA, _, hQA, jA, hjA, ψA, hψA,
    DA, _, _, actA, htorsA, hpullA⟩ := h₂ T O hT q hq hqu E Q hQ j hj ψ hψ D₁ act₁ htors₁
  obtain ⟨σ, hσ⟩ :=
    h₃ T O hT P φ hφ hsh hS q hq hqu A i hi hil hqA EA QA hQA jA hjA ψA hψA DA actA htorsA
  obtain ⟨σ₁, hσ₁⟩ := hpullA σ hσ
  exact hpull₁ σ₁ hσ₁

end GlobalTheory.KeyOriginCut
end

