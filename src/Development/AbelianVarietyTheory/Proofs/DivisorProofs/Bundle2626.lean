module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThValAtAndNotIsThValue
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2555
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2559
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2571

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsPrimitiveAtUniformisedTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.PrimTrait

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := by
  simp [spMap]

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left}

theorem heq_pullS {R : Type} [CommRing R] {x₁ x₂ : Sp R ⟶ S} (h : x₁ = x₂) {T : Over S}
    (f₁ : Over.mk x₁ ⟶ T) (f₂ : Over.mk x₂ ⟶ T) (hf : f₁.left = f₂.left)
    (s : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) :
    HEq (VVRank.pullS G _ f₁ s) (VVRank.pullS G _ f₂ s) := by
  subst h
  obtain rfl : f₁ = f₂ := Over.OverMorphism.ext hf
  rfl

theorem thList_of_eq (ρ : LB.Gen (L.pull (eSec G))) (m : ℕ) {K : Type} [Field K] {x₁ x₂ : Sp K ⟶ S}
    (h : x₁ = x₂) {θ₁ : SecAt G L x₁} {θ₂ : SecAt G L x₂} (hθ : HEq θ₁ θ₂) {N : ℕ}
    {pt : Fin N → (Over.mk x₁ ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m x₁ θ₁ pt c) :
    ∃ pt₂ : Fin N → (Over.mk x₂ ⟶ G), (∀ a, (pt₂ a).left = (pt a).left) ∧ ThList G L ρ m x₂ θ₂ pt₂ c := by
  subst h
  cases hθ
  exact ⟨pt, fun _ => rfl, H⟩

theorem pt_of_eq {R : Type} [CommRing R] {x₁ x₂ : Sp R ⟶ S} (h : x₁ = x₂) (p : Over.mk x₁ ⟶ G) :
    ∃ p₂ : Over.mk x₂ ⟶ G, p₂.left = p.left ∧ ∀ n : ℕ, p ^ n = 1 → p₂ ^ n = 1 := by
  subst h
  exact ⟨p, rfl, fun _ h => h⟩

theorem thG_unique [IsCommMonObj G] (ρ : LB.Gen (L.pull (eSec G))) (hL : L.IsLB) (hρ : ρ.IsGen) {g m : ℕ}
    {K : Type} [Field K] {x : Sp K ⟶ S} (θ : SecAt G L x) (p : Over.mk x ⟶ G) {c c' : K} (hm : Odd m)
    (hm0 : (m : K) ≠ 0) (hP : PolFib G L g x) (h₁ : ThG G L ρ m θ p (GlobalTheory.ZH.fn c))
    (h₂ : ThG G L ρ m θ p (GlobalTheory.ZH.fn c')) : c' = c := by
  have := (_root_.GlobalTheory.UMin.thG_smul_iff S G L ρ hL hρ g m K x θ θ p 1 c c' hm hm0 hP (by simp) h₁).1 h₂
  simpa using this
end

theorem isIntegralElem_of_sq {V F K Kb : Type} [CommRing V] [Field F] [Field K] [Field Kb] (φ : V →+* F) (i : V →+* K)
    (i' : K →+* Kb) (j : F →+* Kb) (hsq : i'.comp i = j.comp φ) {z : F} {w : K} (h : j z = i' w)
    (hz : φ.IsIntegralElem z) : i.IsIntegralElem w := by
  obtain ⟨p, hp, hp0⟩ := hz
  refine ⟨p, hp, i'.injective ?_⟩
  rw [Polynomial.hom_eval₂, ← h, hsq, ← Polynomial.hom_eval₂, hp0, map_zero, map_zero]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (t' : SAB H (Sp V)), Nonempty (SABMap t' t χ) → Nonempty (PELUnif (IsLocalRing.maximalIdeal V) t') → ∀ (σ : SecAt t.G t.PP.L χ), NZ t.G t.PP.L χ σ → ∀ (m N : ℕ), Odd m → 3 ≤ m → IsUnit (m : V) → ∀ (K : Type) [Field K] (i : V →+* K) (pt : Fin N → (Over.mk (spMap i ≫ χ) ⟶ t.G)) (c : Fin N → K), Function.Injective i → ThList t.G t.PP.L t.PP.rig m (spMap i ≫ χ) (SecAt.pull t.G t.PP.L σ i) pt c → Prim i c := by
  intro E _ _ _ H S t V _ _ _ hV χ t' ⟨hm⟩ ⟨P⟩ σ hσ m N hodd h3 hmu K _ i pt c hi hL
  haveI : IsDiscreteValuationRing V := hV.1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let F := AlgebraicClosure (FractionRing V)
  obtain ⟨v, hv⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_valOver hϖ F
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.UMin.UnifPolFib.polFib_of_unif E H S t V hV χ t' ⟨hm⟩ ⟨P⟩
  set x' : Sp F ⟶ S := (jFK (R := V) F ≫ jK V) ≫ χ with hx'
  set θF : SecAt t.G t.PP.L x' :=
    VVRank.pullS t.G _ (Over.homMk (jFK (R := V) F ≫ jK V) rfl : Over.mk x' ⟶ Over.mk χ) σ with hθF
  obtain ⟨hA, x0, c0, hx0, hv0⟩ := (GlobalTheory.Ex.OneGen.theta_at_trait GlobalTheory.lawsAndExpansions E H S t V hV χ t' hm P σ
    hσ).2 ϖ hϖ F v hv m hodd hmu h3 x' (Over.homMk (jFK (R := V) F ≫ jK V) rfl) rfl
  let φF : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
  have hPF : PolFib t.G t.PP.L g x' := by
    have := hg F (algebraMap (FractionRing V) F)
    simpa only [hx', Category.assoc] using this
  have hmF : (m : F) ≠ 0 := by
    have := hmu.map φF
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨ptF, cF, hLF⟩ := _root_.GlobalTheory.UMin.exists_thList S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen g m (m ^ (4 * g)) F x' θF hodd
    hmF rfl hPF
  let Kb := AlgebraicClosure K
  let i' : K →+* Kb := algebraMap K Kb
  have hii : Function.Injective (i'.comp i) := i'.injective.comp hi
  let e : FractionRing V →+* Kb := IsFractionRing.lift hii
  letI : Algebra (FractionRing V) Kb := e.toAlgebra
  let j : F →+* Kb := (IsAlgClosed.lift : F →ₐ[FractionRing V] Kb).toRingHom
  have hsq : i'.comp i = j.comp φF := by
    ext r
    change _ = (IsAlgClosed.lift : F →ₐ[FractionRing V] Kb) (algebraMap (FractionRing V) F _)
    rw [AlgHom.commutes]
    exact (IsFractionRing.lift_algebraMap hii r).symm
  have hy : spMap i' ≫ spMap i ≫ χ = spMap j ≫ x' := by
    change _ = spMap j ≫ (spMap (algebraMap (FractionRing V) F) ≫ spMap (algebraMap V (FractionRing V))) ≫ χ
    rw [← Category.assoc, spMap_comp', spMap_comp', ← Category.assoc, spMap_comp', hsq]

  have hPy : PolFib t.G t.PP.L g (spMap j ≫ x') := by
    have := hg Kb (j.comp (algebraMap (FractionRing V) F))
    rw [← spMap_comp'] at this
    simpa only [hx', Category.assoc] using this
  have hmKb : (m : Kb) ≠ 0 := by
    have := hmu.map (i'.comp i)
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨pt1, hpt1, hL1⟩ := _root_.GlobalTheory.UMin.ThPull.thList_pull S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen m N K Kb i' (spMap i ≫ χ)
    (SecAt.pull t.G t.PP.L σ i) pt c hL
  have hθ : HEq (SecAt.pull t.G t.PP.L (SecAt.pull t.G t.PP.L σ i) i') (SecAt.pull t.G t.PP.L θF j) := by
    simp only [SecAt.pull, hθF, GlobalTheory.ThetaRuleCompare.pullS_comp]
    refine heq_pullS hy _ _ ?_ σ
    simp only [Over.comp_left, Over.homMk_left]
    change spMap i' ≫ spMap i = spMap j ≫ (spMap (algebraMap (FractionRing V) F) ≫ spMap (algebraMap V (FractionRing V)))
    rw [spMap_comp', spMap_comp', spMap_comp', hsq]
  obtain ⟨ptK, hptK, hLK⟩ := thList_of_eq t.PP.rig m hy hθ hL1
  obtain ⟨ptF', hptF', hLF'⟩ := _root_.GlobalTheory.UMin.ThPull.thList_pull S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen m (m ^ (4 * g)) F Kb j x' θF
    ptF cF hLF
  have hint : ∀ b, φF.IsIntegralElem (cF b) := fun b =>
    _root_.GlobalTheory.IntOverCdvr.isIntegralElem_of_val_nonneg V hV ϖ hϖ F v hv (cF b) (hA (ptF b) (cF b) (hLF.2.1 b))
  refine ⟨fun a => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hLF.2.2 Kb j (ptK a) (hLK.2.1 a).1
    have heq : ptK a = ptF' b := Over.OverMorphism.ext (hb.trans (hptF' b).symm)
    have h1 := hLK.2.1 a
    rw [heq] at h1
    have hab : j (cF b) = i' (c a) :=
      thG_unique t.PP.rig t.PP.isLB t.PP.rigGen _ (ptF' b) hodd hmKb hPy h1 (hLF'.2.1 b)
    exact isIntegralElem_of_sq φF i i' j hsq hab (hint b)
  · obtain ⟨x0', hx0'l, hx0't⟩ := pt_of_eq (show x' = spMap (RingHom.id F) ≫ x' by rw [spMap_id', Category.id_comp]) x0
    obtain ⟨b0, hb0⟩ := hLF.2.2 F (RingHom.id F) x0' (hx0't _ hx0.1)
    have hx0b : x0 = ptF b0 := Over.OverMorphism.ext (by rw [← hx0'l, hb0, spMap_id', Category.id_comp])
    subst hx0b
    have hc0b : cF b0 = c0 :=
      thG_unique t.PP.rig t.PP.isLB t.PP.rigGen θF (ptF b0) hodd hmF hPF hx0 (hLF.2.1 b0)
    obtain ⟨q, hql, hqt⟩ := pt_of_eq hy.symm (ptF' b0)
    obtain ⟨a0, ha0⟩ := hL.2.2 Kb i' q (hqt _ (hLF'.2.1 b0).1)
    have heq : ptK a0 = ptF' b0 := Over.OverMorphism.ext (by rw [hptK, hpt1, ← ha0, hql])
    have h1 := hLK.2.1 a0
    rw [heq] at h1
    have hab : j c0 = i' (c a0) := by
      rw [← hc0b]
      exact thG_unique t.PP.rig t.PP.isLB t.PP.rigGen _ (ptF' b0) hodd hmKb hPy h1 (hLF'.2.1 b0)
    have hc0 : c0 ≠ 0 := by
      rintro rfl
      simp at hv0
    have hca : c a0 ≠ 0 := by
      intro h
      rw [h, map_zero] at hab
      exact hc0 (j.injective (hab.trans (map_zero j).symm))
    refine ⟨a0, hca, isIntegralElem_of_sq φF i i' j hsq (z := c0⁻¹) (by rw [map_inv₀, map_inv₀, hab]) ?_⟩
    refine _root_.GlobalTheory.IntOverCdvr.isIntegralElem_of_val_nonneg V hV ϖ hϖ F v hv _ ?_
    have h01 : v c0 + v c0⁻¹ = 0 := by
      rw [← AddValuation.map_mul, mul_inv_cancel₀ hc0, AddValuation.map_one]
    rw [hv0, zero_add] at h01
    rw [h01]

end GlobalTheory.UMin.PrimTrait
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupActionPullbackThetaSectionsGaloisTwist
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

variable {R : Type} [CommRing R] [IsDomain R]

theorem twK_comp_eq_id {σ τ : Kb R →ₐ[FractionRing R] Kb R} (h : σ.comp τ = AlgHom.id _ _) :
    twK σ ≫ twK τ = 𝟙 _ := by
  apply Over.OverMorphism.ext
  show spMap σ.toRingHom ≫ spMap τ.toRingHom = 𝟙 _
  rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have e : σ.toRingHom.comp τ.toRingHom = RingHom.id _ := congrArg AlgHom.toRingHom h
  rw [e]
  exact Spec.map_id _

theorem mTw_comp_eq_id (A : PolAV (Sp (FractionRing R))) {σ τ : Kb R →ₐ[FractionRing R] Kb R}
    (h : σ.comp τ = AlgHom.id _ _) : mTw A σ ≫ mTw A τ = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, mTw_fst, ← Category.assoc, mTw_fst, Category.assoc, twK_comp_eq_id h, Category.comp_id,
      Category.id_comp]
  · rw [Category.assoc, mTw_snd, mTw_snd, Category.id_comp]

theorem mTw_translT (A : PolAV (Sp (FractionRing R))) {σ τ : Kb R →ₐ[FractionRing R] Kb R}
    (h : σ.comp τ = AlgHom.id _ _) (x : TFK (R := R) (Kb R) ⟶ A.A) :
    mTw A σ ≫ translT A.A (twK τ ≫ x) = translT A.A x ≫ mTw A σ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [translT]
    rw [Category.assoc, Category.assoc, lift_fst, mTw_fst, ← Category.assoc, lift_fst]
  · simp only [translT]
    rw [Category.assoc, Category.assoc, lift_snd, mTw_snd, lift_snd]
    simp only [translPt]
    rw [← Category.assoc, comp_lift, ← Category.assoc (mTw A σ), mTw_fst, mTw_snd, Category.assoc,
      ← Category.assoc (twK σ), twK_comp_eq_id h, Category.id_comp]

theorem isActOf_secTw : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ τ : Kb R →ₐ[FractionRing R] Kb R), σ.comp τ = AlgHom.id _ _ → ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))) (a b : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), IsActOf A.A A.L N (thTw A N τ θ) a b → IsActOf A.A A.L N θ (secTw A N σ a) (secTw A N σ b) := by
  intro R _ _ A N σ τ hστ θ a b H
  refine twist_of_val A.isLB θ.isGen fun z J hJ => ?_
  have e1 : (𝟙 _ ≫ (mTw A σ).left) ≫ (mTw A τ).left = 𝟙 _ := by
    rw [Category.id_comp, ← Over.comp_left, mTw_comp_eq_id A hστ, Over.id_left]
  have e2 : (𝟙 _ ≫ (mTw A σ).left) ≫ (translT A.A (twK τ ≫ θ.pt)).left =
      (𝟙 _ ≫ (translT A.A θ.pt).left) ≫ (mTw A σ).left := by
    simp only [Category.id_comp, ← Over.comp_left, mTw_translT A hστ]
  have hv : val (thTw A N τ θ).φ (𝟙 _ ≫ (mTw A σ).left) z J = val θ.φ (𝟙 _) z J :=
    (val_genCast _ _ _ z J).trans ((val_pull hJ _ _ _).trans (congrArg (fun r => val θ.φ r z J) e1))
  have H' := twist_val H (𝟙 _ ≫ (mTw A σ).left) z hJ
  rw [hv] at H'
  have hb : sval (secTw A N σ b) (𝟙 _) z J = sval b (𝟙 _ ≫ (mTw A σ).left) z J :=
    GlobalTheory.FieldBaseChange.sval_pullOver _ _ b _ hJ
  have ha : sval (secTw A N σ a) (𝟙 _ ≫ (translT A.A θ.pt).left) z J =
      sval a ((𝟙 _ ≫ (translT A.A θ.pt).left) ≫ (mTw A σ).left) z J :=
    GlobalTheory.FieldBaseChange.sval_pullOver _ _ a _ hJ
  refine hb.trans (H'.trans ?_)
  rw [ha]
  exact congrArg (fun r => (val θ.φ (𝟙 _) z J).val * sval a r z J) e2

end GlobalTheory.Mum.Conj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupSymmetricLiftActionFieldExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGroup_symmetricLift_action_fieldExtension : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), Odd N → ∀ (x : TFK (R := R) (Kb R) ⟶ A.A) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))) (θ' : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → SymLift A.A A.L N N (baseEm em ≫ x) θ' → ∀ t t' : SecF A (Kb R) N, IsActOf A.A A.L N θ t t' → IsActOf A.A A.L N θ' (secExt A em N t) (secExt A em N t') := by
  first | exact @GlobalTheory.Mum.Desc.isActOf_secExt | exact GlobalTheory.Mum.Desc.isActOf_secExt | (intros; apply GlobalTheory.Mum.Desc.isActOf_secExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupSymmetryValueEqOfConjugateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGroup_symmetryValue_eq_of_conjugate : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] [IsCommMonObj A'] {L : LB A.left} {L' : LB A'.left} {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) (k : ℤ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (ν : LB.Gen (negLB A L k T)) (ν' : LB.Gen (negLB A' L' k T')) (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : f ≫ (translT A θ.pt⁻¹).left = (translT A' θ'.pt⁻¹).left ≫ f) (hneg : f ≫ (negT A T).left = (negT A' T').left ≫ f) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (Hν : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (snd T' A' ≫ (GrpObj.inv : A' ⟶ A')).left]) (ε := ![k, -k]) ν' q z J' * (Ψ (q ≫ (negT A' T').left) z J J' ^ k)⁻¹) (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J' (hJ : Good L z J) (hJ' : Good L' z J'), val (symGen A L k θ ν) (q ≫ f) z J = val (symGen A' L' k θ' ν') q z J' := by
  first | exact @GlobalTheory.ThetaSymTransport.val_symGen_eq | exact GlobalTheory.ThetaSymTransport.val_symGen_eq | (intros; apply GlobalTheory.ThetaSymTransport.val_symGen_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSpanVanishingEqUniformiserMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.ModPi

theorem gp_comp_cst (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (p : X ⟶ Sp R) :
    gp X ≫ p = spMap (GlobalTheory.Desc.cst p) := by
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso _).hom, Scheme.ΓSpecIso_naturality, Scheme.Hom.comp_appTop, gp,
    Scheme.fromSpecStalk_appTop]
  ext r
  simp [GlobalTheory.Desc.cst, fnOf, Scheme.functionField]

theorem cst_reg_zero (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp R) (x : X)
    (hx : p x = closedPoint R) (r : R) :
    GlobalTheory.Cartier.RegAt x (GlobalTheory.Desc.cst p r) ∧ (r ∈ maximalIdeal R → GlobalTheory.Cartier.ZeroAt x (GlobalTheory.Desc.cst p r)) := by
  have hreg : GlobalTheory.Cartier.RegAt x (GlobalTheory.Desc.cst p r) := regAt_fnOf (U := ⊤) trivial trivial _
  refine ⟨hreg, fun hr => zeroAt_iff.2 ⟨hreg, fun hu => ?_⟩⟩
  have h1 := (unitAt_fnOf_iff (U := ⊤) trivial trivial _).1 hu
  have h2 : x ∈ p ⁻¹ᵁ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
    rw [Scheme.Hom.preimage_basicOpen]; exact h1
  have h3 : p x ∈ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := h2
  rw [basicOpen_eq_of_affine, hx] at h3
  exact (PrimeSpectrum.mem_basicOpen _ _).1 h3 hr

theorem span_add {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁] (c : R₁ →+* F₁) {S : Set F₁} {v w : F₁}
    (hv : v ∈ spanBy c S) (hw : w ∈ spanBy c S) : v + w ∈ spanBy c S := by
  obtain ⟨n, r, t, ht, rfl⟩ := hv
  obtain ⟨m, r', t', ht', rfl⟩ := hw
  refine ⟨n + m, Fin.append r r', Fin.append t t', fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact ht i
    · rw [Fin.append_right]; exact ht' i
  · rw [Fin.sum_univ_add]; simp

theorem regAt_npow {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField} (h : GlobalTheory.Cartier.RegAt x f) (n : ℕ) :
    GlobalTheory.Cartier.RegAt x (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact (unitAt_one x).regAt
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem modPi : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → ∀ ϖ : T, maximalIdeal T = Ideal.span {ϖ} → ∀ z ∈ spanBy (GlobalTheory.Desc.cst H'.hom) (θ '' regSet y), GlobalTheory.Cartier.ZeroAt y' z → ∃ z₁ ∈ spanBy (GlobalTheory.Desc.cst H'.hom) (θ '' regSet y), z = GlobalTheory.Desc.cst H'.hom (a ϖ) * z₁ := by
  intro T D _ _ _ _ _ _ a ha hm H _ _ H' _ _ π θ hH hpb hff y y' hy hy' hdy hdy' ϖ hmT
  have hmD : maximalIdeal D = Ideal.span {a ϖ} := by rw [← hm, hmT, Ideal.map_span, Set.image_singleton]
  have hcomp : θ.comp (cst H.hom) = (cst H'.hom).comp a := by
    obtain ⟨l, hl1, hl2⟩ := hff
    have e1 := gp_comp_cst H.left T H.hom
    have e2 := gp_comp_cst H'.left D H'.hom
    have hl : l = gp H'.left := by simpa using hl1
    have key : spMap (θ.comp (cst H.hom)) = spMap ((cst H'.hom).comp a) := by
      calc spMap (θ.comp (cst H.hom)) = spMap θ ≫ spMap (cst H.hom) := by simp [spMap, CommRingCat.ofHom_comp]
        _ = spMap θ ≫ gp H.left ≫ H.hom := by rw [e1]
        _ = l ≫ π ≫ H.hom := by rw [← Category.assoc, ← hl2, Category.assoc]
        _ = gp H'.left ≫ H'.hom ≫ spMap a := by rw [hpb.w, hl]
        _ = spMap (cst H'.hom) ≫ spMap a := by rw [← Category.assoc, e2]
        _ = spMap ((cst H'.hom).comp a) := by simp [spMap, CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)
  have hθc : ∀ t, θ (cst H.hom t) = cst H'.hom (a t) := fun t => by
    rw [← RingHom.comp_apply, hcomp, RingHom.comp_apply]
  set c := cst H'.hom with hc
  have hreg : ∀ u, GlobalTheory.Cartier.RegAt y u → GlobalTheory.Cartier.RegAt y' (θ u) := by
    intro u hu
    have hpt := _root_.GlobalTheory.Desc.GaussBC.apply_eq_of_closedFibre_dim_one T D a ha hm H H' π θ hH hpb ⟨_, hff.choose_spec⟩ y y' hy hy' hdy hdy'
    exact GlobalTheory.T.regularAtPoint_functionField_map_of_genericPoint_comp H.left H'.left π θ ⟨_, hff.choose_spec⟩ y' u (hpt ▸ hu)
  have hcreg : ∀ d, GlobalTheory.Cartier.RegAt y' (c d) := fun d => (cst_reg_zero D H'.left H'.hom y' hy' d).1
  have hc0reg : ∀ t, GlobalTheory.Cartier.RegAt y (cst H.hom t) := fun t => (cst_reg_zero T H.left H.hom y hy t).1
  have hϖz : GlobalTheory.Cartier.ZeroAt y (cst H.hom ϖ) :=
    (cst_reg_zero T H.left H.hom y hy ϖ).2 (by rw [hmT]; exact Ideal.subset_span rfl)
  obtain ⟨hϖ0, hfac⟩ := _root_.GlobalTheory.Desc.GenFibre.unif T H hH y hy hdy ϖ hmT

  have hdiv : ∀ x, GlobalTheory.Cartier.ZeroAt y x → ∃ w, GlobalTheory.Cartier.RegAt y w ∧ x = cst H.hom ϖ * w := by
    intro x hx
    by_cases hx0 : x = 0
    · exact ⟨0, regAt_zero y, by rw [hx0, mul_zero]⟩
    obtain ⟨k, w, hw, rfl⟩ := hfac x hx0
    rcases le_or_gt 1 k with hk | hk
    · refine ⟨cst H.hom ϖ ^ (k - 1).toNat * w, (regAt_npow (hc0reg ϖ) _).mul hw.regAt, ?_⟩
      rw [← _root_.mul_assoc, ← pow_succ', ← zpow_natCast]
      congr 2; omega
    · exfalso
      have hk' : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have e : cst H.hom ϖ ^ k * w * cst H.hom ϖ ^ (-k).toNat = w := by
        rw [mul_comm _ (cst H.hom ϖ ^ (-k).toNat), ← _root_.mul_assoc, ← zpow_natCast, hk',
          ← zpow_add₀ hϖ0, neg_add_cancel, zpow_zero, _root_.one_mul]
      exact (zeroAt_iff.1 (e ▸ hx.mul (regAt_npow (hc0reg ϖ) _))).2 hw
  have hgeo := _root_.GlobalTheory.Desc.ResInj.residue_linearIndependent T D a ha hm H H' π θ hH hpb hff y y' hy hy' hdy hdy'
  set S := spanBy c (θ '' regSet y) with hS

  have hyes : ∀ (n : ℕ) (d : Fin n → D) (u : Fin n → H.left.functionField), (∀ i, GlobalTheory.Cartier.RegAt y (u i)) →
      (∀ cc : Fin n → T, GlobalTheory.Cartier.ZeroAt y (∑ i, cst H.hom (cc i) * u i) → ∀ i, cc i ∈ maximalIdeal T) →
      GlobalTheory.Cartier.ZeroAt y' (∑ i, c (d i) * θ (u i)) → ∃ z₁ ∈ S, ∑ i, c (d i) * θ (u i) = c (a ϖ) * z₁ := by
    intro n d u hu hind hz
    have hd := hgeo n u hu hind d hz
    choose e he using fun i => Ideal.mem_span_singleton'.1 (hmD ▸ hd i)
    refine ⟨∑ i, c (e i) * θ (u i), ⟨n, e, fun i => θ (u i), fun i => ⟨u i, hu i, rfl⟩, rfl⟩, ?_⟩
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← he i, map_mul]; ring
  have hmain : ∀ (n : ℕ) (d : Fin n → D) (u : Fin n → H.left.functionField), (∀ i, GlobalTheory.Cartier.RegAt y (u i)) →
      GlobalTheory.Cartier.ZeroAt y' (∑ i, c (d i) * θ (u i)) → ∃ z₁ ∈ S, ∑ i, c (d i) * θ (u i) = c (a ϖ) * z₁ := by
    intro n
    induction n with
    | zero => intro d u hu hz; exact hyes 0 d u hu (fun _ _ i => i.elim0) hz
    | succ n ih =>
      intro d u hu hz
      by_cases hind : ∀ cc : Fin (n + 1) → T, GlobalTheory.Cartier.ZeroAt y (∑ i, cst H.hom (cc i) * u i) → ∀ i, cc i ∈ maximalIdeal T
      · exact hyes _ d u hu hind hz
      push_neg at hind
      obtain ⟨cc, hZ, k, hk⟩ := hind
      obtain ⟨ν, hν⟩ : ∃ ν : T, ν * cc k = 1 := by
        obtain ⟨v, hv⟩ := IsLocalRing.notMem_maximalIdeal.1 hk
        exact ⟨↑v⁻¹, by rw [← hv, Units.inv_mul]⟩
      obtain ⟨w, hw, hrel⟩ := hdiv _ hZ
      rw [Fin.sum_univ_succAbove _ k] at hrel
      have hrel' := congrArg θ hrel
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sum, map_mul, hθc] at hrel'
      have hν' : c (a ν) * c (a (cc k)) = 1 := by rw [← map_mul, ← map_mul, hν, map_one, map_one]
      set d' : Fin n → D := fun j => d (k.succAbove j) - d k * a ν * a (cc (k.succAbove j)) with hd'
      set u' : Fin n → H.left.functionField := fun j => u (k.succAbove j) with hu'
      have hsplit : ∑ i, c (d i) * θ (u i) = c (a ϖ) * (c (d k * a ν) * θ w) + ∑ j, c (d' j) * θ (u' j) := by
        rw [Fin.sum_univ_succAbove _ k]
        have : ∑ j, c (d' j) * θ (u' j) = ∑ j, c (d (k.succAbove j)) * θ (u (k.succAbove j)) -
            c (d k) * c (a ν) * ∑ j, c (a (cc (k.succAbove j))) * θ (u (k.succAbove j)) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [hd', hu', map_sub, map_mul]; ring
        rw [this, map_mul]
        linear_combination (c (d k) * c (a ν)) * hrel' - (c (d k) * θ (u k)) * hν'
      have hz' : GlobalTheory.Cartier.ZeroAt y' (∑ j, c (d' j) * θ (u' j)) := by
        have e : ∑ j, c (d' j) * θ (u' j) = ∑ i, c (d i) * θ (u i) + c (a ϖ) * (c (-(d k * a ν)) * θ w) := by
          rw [hsplit, map_neg]; ring
        rw [e]
        refine hz.add (ZeroAt.mul ?_ ((hcreg _).mul (hreg w hw)))
        exact (cst_reg_zero D H'.left H'.hom y' hy' (a ϖ)).2 (by rw [hmD]; exact Ideal.subset_span rfl)
      obtain ⟨z₁, hz₁, e₁⟩ := ih d' u' (fun j => hu _) hz'
      refine ⟨c (d k * a ν) * θ w + z₁, span_add c ⟨1, fun _ => d k * a ν, fun _ => θ w, fun _ => ⟨w, hw, rfl⟩, by simp⟩ hz₁, ?_⟩
      rw [hsplit, e₁]; ring
  intro z hz hzy
  obtain ⟨n, r, t, ht, rfl⟩ := hz
  choose u hu hut using ht
  have e : ∑ i, c (r i) * t i = ∑ i, c (r i) * θ (u i) := Finset.sum_congr rfl fun i _ => by rw [hut i]
  rw [e] at hzy ⊢
  exact hmain n r u hu hzy

end GlobalTheory.Desc.ModPi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDensityHermitianFormsEqZeroOffDegree
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
namespace GlobalTheory.ChernCalc

noncomputable def linPoly {n : ℕ} (α : V n → V n → ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  ∑ a, ∑ b, C (α (coordVec a) (coordVec b)) * X (a, b)

theorem linPoly_isHomogeneous {n : ℕ} (α : V n → V n → ℂ) : (linPoly α).IsHomogeneous 1 := by
  unfold linPoly
  refine IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ => ?_
  simpa using (isHomogeneous_C (Fin n × Fin n) (α (coordVec a) (coordVec b))).mul (isHomogeneous_X ℂ (a, b))

theorem aeval_sym_linPoly {n : ℕ} (α : V n → V n → ℂ) : aeval sym (linPoly α) = ofValues α := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [linPoly, ofValues, map_sum, Algebra.smul_def]

theorem degree_permMono {n : ℕ} (w : Equiv.Perm (Fin n)) :
    Finsupp.degree (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ) = n := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]; simp [Finsupp.degree_single]

theorem topCoeff_eq_zero_of_isHomogeneous {n d : ℕ} {Q : MvPolynomial (Fin n × Fin n) ℂ} (hQ : Q.IsHomogeneous d)
    (hd : d ≠ n) : topCoeff Q = 0 := by
  unfold topCoeff
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [hQ.coeff_eq_zero (by rw [degree_permMono]; exact fun h => hd h.symm), mul_zero]

theorem dens_aeval_ofValues_offDeg : ∀ (n : ℕ) (κ : Type) (α : κ → V n → V n → ℂ) (d : ℕ) (P : MvPolynomial κ ℝ),
    P.IsHomogeneous d → d ≠ n →
      dens ((aeval (fun i => ofValues (α i)) (P.map (algebraMap ℝ ℂ)) : Ev n) : Alt n) = 0 := by
  intro n κ α d P hP hd
  have h1 : (aeval (fun i => ofValues (α i)) (P.map (algebraMap ℝ ℂ)) : Ev n) =
      aeval sym (bind₁ (fun i => linPoly (α i)) (P.map (algebraMap ℝ ℂ))) := by
    rw [aeval_bind₁]; simp only [aeval_sym_linPoly]
  have hQ : (bind₁ (fun i => linPoly (α i)) (P.map (algebraMap ℝ ℂ))).IsHomogeneous d := by
    simpa using (hP.map (algebraMap ℝ ℂ)).aeval (fun i => linPoly (α i)) fun i => linPoly_isHomogeneous (α i)
  rw [h1, _root_.GlobalTheory.ChernCalc.DensTop.dens_aeval_sym, topCoeff_eq_zero_of_isHomogeneous hQ hd, zero_div]

end GlobalTheory.ChernCalc
end

