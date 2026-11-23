module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0050
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0064

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicSumRel
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

set_option autoImplicit false

namespace GlobalTheory.UU

theorem finsum_rel {A : Type*} [CommRing A] {Ix Ix' : Type*} (σ : Ix ≃ Ix') (f : Ix → A) (g : Ix' → A)
    (a b v : A) (s : Finset Ix) (s' : Finset Ix') (hf : ∀ i ∉ s, f i = 0) (hg : ∀ i ∉ s', g i = 0)
    (h : ∀ i, a * g (σ i) = b * (f i * v)) :
    a * ∑ i ∈ s', g i = b * ((∑ i ∈ s, f i) * v) := by
  classical
  have h1 : ∑ i ∈ s, f i = ∑ i ∈ s ∪ s'.map σ.symm.toEmbedding, f i :=
    Finset.sum_subset Finset.subset_union_left (fun i _ hi => hf i hi)
  have h2 : ∑ i ∈ s', g i = ∑ i ∈ s'.map σ.symm.toEmbedding, g (σ i) := by
    rw [Finset.sum_map]; simp
  have h3 : ∑ i ∈ s'.map σ.symm.toEmbedding, g (σ i) = ∑ i ∈ s ∪ s'.map σ.symm.toEmbedding, g (σ i) :=
    Finset.sum_subset Finset.subset_union_right (fun i _ hi => hg _ (fun hm => hi (by
      rw [Finset.mem_map]; exact ⟨σ i, hm, by simp⟩)))
  rw [h1, h2, h3, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => h i)

theorem adicSum_rel : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y Y₂ : Over (Spec (CommRingCat.of R))) (τ : Y ⟶ Y₂) (X : Scheme.{0}) (L : LB X) (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y₂.left ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y.left ⟶ X)) (ε' : K' → ℤ) (φu : K'' → (Y.left ⟶ X)) (εu : K'' → ℤ) (u : LB.Gen (LB.LinComb L φu εu)) (c c' : Γ(Y.left, ⊤)) (Ix Ix' : Type) (σ : Ix ≃ Ix') (p : Ix → LB.Sec (LB.LinComb L φ ε)) (p' : Ix' → LB.Sec (LB.LinComb L φ' ε')) (S S'), AdicSum I p S → AdicSum I p' S' → (∀ i (Z : Scheme.{0}) (r : Z ⟶ Y.left) (z : Z) (J), Good L z J → gs r z ⊤ c' * sval (p' (σ i)) r z J = gs r z ⊤ c * (sval (p i) (r ≫ τ.left) z J * (val u r z J).val)) → ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Y.left), Lvl I e (r ≫ Y.hom) → ∀ (z : Z) (J), Good L z J → gs r z ⊤ c' * sval S' r z J = gs r z ⊤ c * (sval S (r ≫ τ.left) z J * (val u r z J).val) := by
  intro R _ I Y Y₂ τ X L K K' K'' _ _ _ φ ε φ' ε' φu εu u c c' Ix Ix' σ p p' S S' hS hS' h e Z r hr z J hJ
  obtain ⟨s, hs⟩ := hS e
  obtain ⟨s', hs'⟩ := hS' e
  have hr2 : Lvl I e ((r ≫ τ.left) ≫ Y₂.hom) := by
    rw [Category.assoc, Over.w τ]; exact hr
  obtain ⟨a1, a2⟩ := hs Z (r ≫ τ.left) hr2 z J hJ
  obtain ⟨b1, b2⟩ := hs' Z r hr z J hJ
  rw [a2, b2]
  exact finsum_rel σ _ _ _ _ _ s s' a1 b1 (fun i => h i Z r z J hJ)

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardQuotientKTorsionPairs
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT
open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem card_qk_eq_mul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (hB : D.TauBimult) {k : ℕ} (hk : k ≠ 0)
    (hd : ∀ y : D.X, ∃ g : GtPtF D F, k • g = iota hB F y) :
    Nat.card (Quot (QkPt.Equiv D F (k := k))) = k ^ D.rank * Nat.card {g : GtPtF D F // k • g = 0} := by
  choose r hr using hd
  let K : AddSubgroup D.X := (nsmulAddMonoidHom k : D.X →+ D.X).range
  have hK : Nat.card (D.X ⧸ K) = k ^ D.rank := AddSubgroup.index_range_nsmul D.X k
  let f : (D.X ⧸ K) × {g : GtPtF D F // k • g = 0} → Quot (QkPt.Equiv D F (k := k)) := fun x =>
    Quot.mk _ (qkMk hB x.1.out (r x.1.out + x.2.1) (by rw [nsmul_add, hr, x.2.2, add_zero]))
  rw [← hK, ← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
  · rintro ⟨c, t⟩ ⟨c', t'⟩ h
    obtain ⟨z, hy, hg⟩ := (equiv_iff hB _ _).1 ((equiv_equivalence hB).eqvGen_iff.1 (Quot.eqvGen_exact h))
    simp only [qkMk_y, qkMk_g] at hy hg
    obtain rfl : c = c' := by
      rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' c', QuotientAddGroup.eq]
      exact ⟨z, by rw [hy, neg_add_cancel_left]; rfl⟩
    have hz : z = 0 := by
      have h0 : (k : ℤ) • z = 0 := by rw [natCast_zsmul]; exact left_eq_add.1 hy
      exact (smul_eq_zero.1 h0).resolve_left (by exact_mod_cast hk)
    rw [hz, map_zero, add_zero, add_right_inj] at hg
    exact Prod.ext rfl (Subtype.ext hg.symm)
  · rintro ⟨p⟩
    obtain ⟨z, hz⟩ : -p.y + (QuotientAddGroup.mk p.y : D.X ⧸ K).out ∈ K := by
      rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
    have hy : (QuotientAddGroup.mk p.y : D.X ⧸ K).out = p.y + k • z := by
      rw [show k • z = _ from hz, add_neg_cancel_left]
    refine ⟨⟨QuotientAddGroup.mk p.y, p.g + iota hB F z - r (QuotientAddGroup.mk p.y : D.X ⧸ K).out, ?_⟩,
      (Quot.sound ((equiv_iff hB _ _).2 ⟨z, hy, ?_⟩)).symm⟩
    · rw [nsmul_sub, hr, hy, nsmul_add, qk_nsmul hB, map_add (f := _), map_nsmul, sub_self]
    · exact add_sub_cancel _ _

theorem card_qk : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → Nat.card (Quot (QkPt.Equiv D.toPre F (k := k))) = k ^ (2 * (D.toPre.rank + D.toPre.P.g)) := by
  intro hL R _ _ _ I hA D F _ _ _ k hk
  have : IsNoetherianRing R := hA.1
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  have h₁ := (GlobalTheory.GtCount.card_gtTors hL.1 hL.2.1 R D.toPre F k (Nat.cast_ne_zero.2 (by omega))).1
  simp only [GlobalTheory.GtCount.gtTors_iff] at h₁
  have h₂ := (gt_onto_divisible_kernel hL R I hA D F).2.1 k hk
  rw [card_qk_eq_mul D.tau_bimult (by omega) fun y => (h₂ _).imp fun _ e => ((isNsmul_iff_eq _ _ _).1 e).symm, h₁,
    ← pow_add]
  congr 1
  ring

end GlobalTheory.UT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ChartExpansionOfValueExpansion
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.ExpFrac

def sc {F : Type} [CommRing F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) :
    F →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ ⊤ z trivial).hom.comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)

theorem gs_inv {F : Type} [CommRing F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (a : F) :
    gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom a) = sc p z a := by
  rw [gs_eq p z ⊤ trivial]; rfl

theorem gs_scal {F : Type} [CommRing F] {Y Z : Scheme.{0}} (r : Z ⟶ Y) (p : Y ⟶ Spec (CommRingCat.of F)) (z : Z)
    (a : F) : gs r z ⊤ (scal p a) = sc (r ≫ p) z a :=
  (gs_pull r p z ⊤ trivial _).trans (gs_inv _ z a)

theorem sc_map {F F' : Type} [CommRing F] [CommRing F'] (φ : F →+* F') {Z : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of F')) (z : Z) (a : F) :
    sc (p ≫ Spec.map (CommRingCat.ofHom φ)) z a = sc p z (φ a) := by
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [sc, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, e]

theorem jFK_self (R : Type) [CommRing R] [IsDomain R] :
    jFK (R := R) (FractionRing R) = 𝟙 (Spec (CommRingCat.of (FractionRing R))) := by
  show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))) = _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

theorem clear_sum {R S : Type} [CommRing R] [IsDomain R] [CommRing S] (χ : FractionRing R →+* S) {n : ℕ} (r : R)
    (a : Fin n → R) (c : Fin n → FractionRing R) (h : ∀ i, algebraMap R (FractionRing R) (a i) = r • c i)
    (v : Fin n → S) :
    ∑ i, χ (algebraMap R _ (a i)) * v i = χ (algebraMap R _ r) * ∑ i, χ (c i) * v i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h i, Algebra.smul_def, map_mul, _root_.mul_assoc]

theorem expands_of_expF : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : U'.SecK k) (σ₀) (t) (s : Fam D.toPre (FractionRing R) k), HEq σ σ₀ → U.SameK (k := k) σ₀ t → U.ExpF (FractionRing R) k t s.s → U'.Expands k σ s := by
  intro R _ _ I D A G _ _ U U' hM k σ σ₀ t s hσ hK hE
  obtain ⟨n, c, σs, fs, hT, hA, hB⟩ := hE
  obtain ⟨⟨r, hr⟩, ha⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) c
  choose a ha using ha
  obtain ⟨σ', f', hT', hσ', hf'⟩ := ExpLin.expT_linear R I D.toPre A G U (𝟙_ _) k n
    (fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a i)) σs fs hT
  obtain ⟨-, e₁, -, e₂⟩ := UnitSec.same_exists R D.toPre G U.P.L.L U.P.L.isLB k
  obtain ⟨τ, hτ⟩ := e₁ σ'
  obtain ⟨f, hf⟩ := e₂ f'
  have hAt := fun τ' => expandsAt_of_expT R I D A G U U' hM k τ' τ σ' f f'
  have hG : GeneratorPullback.SecScal U.P.L.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)) σ₀
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) τ (pullback.fst G.hom (jK R))
      (scal (pullback.snd G.hom (jK R) ≫ jK R) r) := by
    refine BoxFamScalar.secScal_of_pointwise U.P.L.isLB fun y J hJ => ?_
    obtain ⟨rG, hG₁, hG₂⟩ := exists_lift_unit_tensor G (𝟙 _ ≫ pullback.fst G.hom (jK R))
    choose JA hJA using fun ψ : pullback G.hom (jK R) ⟶ A.A.left => exists_chart A.isLB (ψ y)
    have w : pullback.snd G.hom (jK R) ≫ (TFK (R := R) (FractionRing R)).hom = U.gen.hom.left ≫ A.A.hom :=
      ((congrArg (pullback.snd G.hom (jK R) ≫ ·) (jFK_self R)).trans (Category.comp_id _)).trans
        (Over.w U.gen.hom).symm
    obtain ⟨rA, hA₁, hA₂⟩ : ∃ rA : pullback G.hom (jK R) ⟶ (TFK (R := R) (FractionRing R) ⊗ A.A).left,
        rA ≫ (fst _ A.A).left = pullback.snd G.hom (jK R) ∧ rA ≫ (snd _ A.A).left = 𝟙 _ ≫ U.gen.hom.left :=
      ⟨pullback.lift _ _ w, pullback.lift_fst _ _ w, (pullback.lift_snd _ _ w).trans (Category.id_comp _).symm⟩
    have e₃ := (hK _ rA (𝟙 _) hA₂ y JA J hJA hJ).symm.trans (hA _ rA (𝟙 _) rG hA₂ hG₁ y JA J hJA hJ)
    have e₄ : rG ≫ (fst _ G).left = pullback.snd G.hom (jK R) ≫ jK R :=
      hG₂.trans ((congrArg (· ≫ G.hom) (Category.id_comp _)).trans pullback.condition)
    refine ((congrArg (fun q => sval τ q y J) hG₁).symm.trans (hτ _ rG y J hJ).symm).trans
      ((hσ' _ rG y J hJ).trans ?_)
    refine Eq.trans ?_ (congrArg (_ * ·) e₃).symm
    refine Eq.trans ?_ ((clear_sum (sc (pullback.snd G.hom (jK R)) y) r a c ha (fun i => sval (σs i) rG y J)).trans ?_)
    · refine Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_
      exact (gs_inv _ y _).trans ((congrArg (fun q => sc q y (a i)) e₄).trans (sc_map _ _ y _))
    · refine congrArg₂ (· * ·) ?_ (Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_)
      · rw [gs_scal, Category.id_comp, sc_map]
      · exact ((gs_scal _ _ y _).trans (congrArg (fun q => sc q y (c i)) hA₁)).symm
  have hF : ∀ α : D.toPre.X,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (s.s α)
        (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left
        (scal (DegPre.BF D.toPre (FractionRing R)).hom r) := by
    intro α
    refine BoxFamScalar.secScal_of_pointwise D.toPre.P.isLB fun y J hJ => ?_
    obtain ⟨rB, hB₁, hB₂⟩ := exists_lift_unit_tensor D.toPre.P.A (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing R)).left)
    have e₃ := hB α _ (𝟙 _) rB hB₁ y J hJ
    have e₅ : (DegPre.BF D.toPre (FractionRing R)).hom =
        (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jK R :=
      (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)).symm.trans (congrArg
        ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ ·)
        ((congrArg (· ≫ jK R) (jFK_self R)).trans (Category.id_comp _)))
    have e₄ : rB ≫ (fst _ D.toPre.P.A).left = (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jK R :=
      hB₂.trans ((congrArg (· ≫ D.toPre.P.A.hom) (Category.id_comp _)).trans
        ((Over.w (DegPre.prB D.toPre (FractionRing R))).trans e₅))
    refine ((congrArg (fun q => sval (f α) q y J) hB₁).symm.trans (hf α _ rB y J hJ).symm).trans
      ((hf' α _ rB y J hJ).trans ?_)
    refine Eq.trans ?_ (congrArg (_ * ·) e₃).symm
    refine Eq.trans ?_ ((clear_sum (sc (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left y) r a c ha
      (fun i => sval (fs i α) rB y J)).trans ?_)
    · refine Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_
      exact (gs_inv _ y _).trans ((congrArg (fun q => sc q y (a i)) e₄).trans (sc_map _ _ y _))
    · refine congrArg₂ (· * ·) ?_ (Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_)
      · exact ((gs_scal _ _ y _).trans ((congrArg (fun q => sc q y r) ((Category.id_comp _).trans e₅)).trans
          (sc_map _ _ y _))).symm
      · exact ((gs_scal _ _ y _).trans (congrArg (fun q => sc q y (c i)) (Category.id_comp _))).symm
  obtain ⟨semi, gen, gen_hom, P, wA, wA_gen, gt, gt_q, gt_t, w, w_gen, w_vals, w_compat⟩ := U
  cases P
  have hL := hM.LG
  dsimp only at hL
  subst hL
  obtain rfl := eq_of_heq hσ
  exact ⟨r, nonZeroDivisors.ne_zero hr, τ, f, hG, hF, hAt τ HEq.rfl hτ hf hT'⟩

end GlobalTheory.UU.ExpFrac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CompOneLeft
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.UU.TorMul

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def germScal {W : Type} [CommRing W] {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of W)) (z : Z) :
    W →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ ⊤ z trivial).hom.comp (r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom)

theorem gs_scal {W : Type} [CommRing W] {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of W)) (z : Z) (c : W) :
    gs (𝟙 Z) z ⊤ (scal (R := W) r c) = germScal r z c :=
  gs_eq (𝟙 Z) z ⊤ trivial _

def push (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ G) :=
  pushHom (isGrpPullback_pullback G (thick R I e)) T

theorem push_inj (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    Function.Injective (push I e G T) := fun y y' h =>
  Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) h) ((Over.w y).trans (Over.w y').symm))

theorem push_surj (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    Function.Surjective (push I e G T) := fun x =>
  ⟨Over.homMk (pullback.lift x.left T.hom (Over.w x)) (pullback.lift_snd _ _ _),
    Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩

def Coord {e : ℕ} (g : GtCoord I D e G) {W : Type} [CommRing W]
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (r : T.left ⟶ Spec (CommRingCat.of W))
    (a : Multiplicative D.X →* Wˣ) (y : T ⟶ thickObj R I e G) : Prop :=
  GlobalTheory.TorusCoord.im g y = 1 ∧ ∀ (χ : D.X) (z : T.left) (J), Good D.P.L z J →
    val (g.t χ) y.left z J = Units.map (germScal r z : W →* _) (a (Multiplicative.ofAdd χ))

section
variable {e : ℕ} (g : GtCoord I D e G) {W : Type} [CommRing W]
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (r : T.left ⟶ Spec (CommRingCat.of W))

theorem coord_one : Coord g r 1 (1 : T ⟶ thickObj R I e G) :=
  ⟨GlobalTheory.TorusCoord.im_one g, fun χ z J hJ => (GlobalTheory.TorusCoord.val_unit g χ hJ).trans (map_one _).symm⟩

theorem val_mul_of (hG : GlobalFnsSt) {y y' : T ⟶ thickObj R I e G} (h : GlobalTheory.TorusCoord.im g y = 1)
    (χ : D.X) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val (g.t χ) (y * y').left z J = val (g.t χ) y.left z J * val (g.t χ) y'.left z J := by
  have k := GlobalTheory.TorusCoord.val_t_mul_points g hG χ y y' z J hJ
  have c : GlobalTheory.TorusCoord.cubeVal g χ z J y y' = 1 := by
    unfold GlobalTheory.TorusCoord.cubeVal
    rw [h]
    exact (isCub_cubV D.cub (T := (Over.map (thick R I e)).obj T) hJ).face₂ _ _
  rwa [c, _root_.mul_one] at k

theorem coord_mul (hG : GlobalFnsSt) {a a' : Multiplicative D.X →* Wˣ} {y y' : T ⟶ thickObj R I e G}
    (h : Coord g r a y) (h' : Coord g r a' y') : Coord g r (a * a') (y * y') := by
  refine ⟨by rw [GlobalTheory.TorusCoord.im_mul, h.1, h'.1, _root_.mul_one], fun χ z J hJ => ?_⟩
  exact (val_mul_of g hG h.1 χ z J hJ).trans
    ((congrArg₂ (· * ·) (h.2 χ z J hJ) (h'.2 χ z J hJ)).trans (map_mul _ _ _).symm)

theorem coord_inv (hG : GlobalFnsSt) {a : Multiplicative D.X →* Wˣ} {y : T ⟶ thickObj R I e G}
    (h : Coord g r a y) : Coord g r a⁻¹ y⁻¹ := by
  refine ⟨?_, fun χ z J hJ => ?_⟩
  · have := GlobalTheory.TorusCoord.im_mul g y y⁻¹
    rw [mul_inv_cancel, GlobalTheory.TorusCoord.im_one, h.1, _root_.one_mul] at this
    exact this.symm
  · have k := (((GlobalTheory.TorusCoord.val_unit g χ hJ).symm.trans
      (GlobalTheory.TorusCoord.val_congr g χ (mul_inv_cancel y).symm z J)).trans (val_mul_of g hG h.1 χ z J hJ)).symm
    exact ((eq_inv_of_mul_eq_one_right k).trans (congrArg (·⁻¹) (h.2 χ z J hJ))).trans (map_inv _ _).symm
end

theorem comp_one_left {S : Scheme.{0}} (B : Over S) [GrpObj B] {T T' : Over S} (ρ : T' ⟶ T) :
    ρ.left ≫ (1 : T ⟶ B).left = (1 : T' ⟶ B).left :=
  congrArg (fun q : T' ⟶ B => q.left) (MonObj.comp_one ρ)

theorem torPt_iff (U : PreU I D A G) {W : Type} [CommRing W] [Algebra R W] (a : Multiplicative D.X →* Wˣ)
    (x : TA R W ⟶ G) : U.TorPt a x ↔ ∀ (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (ρ : (Over.map (thick R I e)).obj T ⟶ TA R W) (y : T ⟶ thickObj R I e G),
      push I e G T y = ρ ≫ x → Coord (U.gt e) ρ.left a y := by
  constructor
  · intro h e T ρ y hy
    obtain ⟨h₁, h₂⟩ := h e T.left ρ.left y.left (congrArg (fun q => q.left) hy)
    refine ⟨Over.OverMorphism.ext (h₁.trans (comp_one_left D.P.A ρ)),
      fun χ z J hJ => Units.ext ((h₂ χ z J hJ).trans (gs_scal _ _ _))⟩
  · intro h e Z r xe hx
    let T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (xe ≫ (thickObj R I e G).hom)
    have hw : r ≫ (TA R W).hom = (xe ≫ (thickObj R I e G).hom) ≫ thick R I e := by
      rw [← Over.w x, ← Category.assoc, ← hx, Category.assoc, Category.assoc]
      exact congrArg (xe ≫ ·) (Over.w (fstG I e G))
    let ρ : (Over.map (thick R I e)).obj T ⟶ TA R W := Over.homMk r hw
    let y : T ⟶ thickObj R I e G := Over.homMk xe rfl
    obtain ⟨h₁, h₂⟩ := h e T ρ y (Over.OverMorphism.ext hx)
    exact ⟨(congrArg (fun q => q.left) h₁).trans (comp_one_left D.P.A ρ).symm,
      fun χ z J hJ => (congrArg Units.val (h₂ χ z J hJ)).trans (gs_scal _ _ _).symm⟩

section
variable (U : PreU I D A G) {W : Type} [CommRing W] [Algebra R W]

theorem torPt_one : U.TorPt (1 : Multiplicative D.X →* Wˣ) 1 := by
  refine (torPt_iff U _ _).2 fun e T ρ y hy => ?_
  obtain rfl : y = 1 := push_inj e T (hy.trans ((MonObj.comp_one ρ).trans (map_one _).symm))
  exact coord_one _ _

theorem torPt_mul (hG : GlobalFnsSt) {a a' : Multiplicative D.X →* Wˣ} {x x' : TA R W ⟶ G}
    (h : U.TorPt a x) (h' : U.TorPt a' x') : U.TorPt (a * a') (x * x') := by
  refine (torPt_iff U _ _).2 fun e T ρ y hy => ?_
  obtain ⟨p, hp⟩ := push_surj e T (ρ ≫ x)
  obtain ⟨p', hp'⟩ := push_surj e T (ρ ≫ x')
  obtain rfl : y = p * p' := push_inj e T (by rw [hy, map_mul, hp, hp', MonObj.comp_mul])
  exact coord_mul _ _ hG ((torPt_iff U _ _).1 h e T ρ p hp) ((torPt_iff U _ _).1 h' e T ρ p' hp')

theorem torPt_inv (hG : GlobalFnsSt) {a : Multiplicative D.X →* Wˣ} {x : TA R W ⟶ G}
    (h : U.TorPt a x) : U.TorPt a⁻¹ x⁻¹ := by
  refine (torPt_iff U _ _).2 fun e T ρ y hy => ?_
  obtain ⟨p, hp⟩ := push_surj e T (ρ ≫ x)
  obtain rfl : y = p⁻¹ := push_inj e T (by rw [hy, map_inv, hp]; exact map_inv (preHom ρ) x)
  exact coord_inv _ _ hG ((torPt_iff U _ _).1 h e T ρ p hp)

theorem torPt_pow (hG : GlobalFnsSt) {a : Multiplicative D.X →* Wˣ} {x : TA R W ⟶ G}
    (h : U.TorPt a x) (k : ℕ) : U.TorPt (a ^ k) (x ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact torPt_one U
  | succ k ih => rw [pow_succ, pow_succ]; exact torPt_mul U hG ih h
end

end GlobalTheory.UU.TorMul

theorem GlobalTheory.UU.torPt_group : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (W : Type) [CommRing W] [Algebra R W], U.TorPt (1 : Multiplicative D.X →* Wˣ) 1 ∧ ∀ (a a' : Multiplicative D.X →* Wˣ) (x x' : TA R W ⟶ G), U.TorPt a x → (U.TorPt a' x' → U.TorPt (a * a') (x * x')) ∧ U.TorPt a⁻¹ x⁻¹ ∧ ∀ k : ℕ, U.TorPt (a ^ k) (x ^ k) :=
  fun hG _ _ _ _ _ _ _ _ _ U _ _ _ => ⟨TorMul.torPt_one U, fun _ _ _ _ h =>
    ⟨fun h' => TorMul.torPt_mul U hG h h', TorMul.torPt_inv U hG h, TorMul.torPt_pow U hG h⟩⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalBundleOfSymmetricSemiAbelian
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_cp_of_isSymmetric :
    Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (L : RigLB G) (c : CubicalStr G L), L.IsSymmetric → ∃ P : CP G, P.L = L ∧ HEq P.c c := by
  intro hL R _ _ _ A G _ _ hS gen _ L c hsym
  obtain ⟨s, hs, hr⟩ := GlobalTheory.SymmetricBundle.gen_of_isSymmetric L hsym
  have := hS.smooth
  have : Flat (G3 G).hom := by
    show Flat (pullback.fst G.hom (pullback.fst G.hom G.hom ≫ G.hom) ≫ G.hom)
    infer_instance
  exact ⟨⟨L, c, s, hs, hr, GlobalTheory.ValueForm.sym_cub_of_baseChange (jK R) (GlobalTheory.ValueForm.app_generic_injective _)
    (GlobalTheory.ValueForm.surjective_cube_baseChange hL.globalFns _ A.isAb gen) c s hs hr⟩, rfl, HEq.rfl⟩

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOfPull
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem expF_of_pull : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (I : Ideal R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α) (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) (s : Raw D F k), U.ExpT (𝟙_ _) k σ f → U.PullG F (toUnit _) k σ t → PullB D F (toUnit _) k f s → U.ExpF F k t s :=
  fun R _ _ D I A G _ _ U F _ _ k σ f t s hE hG hB =>
    GlobalTheory.UU.IntExp.expF_of_expT R I D A G U F k σ f t s hE hG hB

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultPsiEvenOverExtensionFieldStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.tau_bimult_psi_even_over_extension_field : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F], ((∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ a b m : D.X, val (Z := (TF (R := R) F).left) (D.psi (a + b + m)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (a)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (m)) (jFK (R := R) F) z J * rigV D z J * cubV D.cub z J (cT D _ a) (cT D _ b) (cT D _ m) = val (Z := (TF (R := R) F).left) (D.psi (a + b)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (a + m)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b + m)) (jFK (R := R) F) z J) ↔ D.TauBimult) ∧ ((∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ m : D.X, val (Z := (TF (R := R) F).left) (D.psi (-m)) (jFK (R := R) F) z J * val D.sym (cT D (TF (R := R) F) m).left z J = val (Z := (TF (R := R) F).left) (D.psi (m)) (jFK (R := R) F) z J) ↔ D.PsiEven) := by
  first | exact @GlobalTheory.TauValues.main | exact GlobalTheory.TauValues.main | (intros; apply GlobalTheory.TauValues.main <;> assumption)
end

