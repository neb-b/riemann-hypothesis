module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0104
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SiegelOfPolarised

open PrimNorm

section Bundle

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

theorem prod_lam {T : Over S} (x y : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ A.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h ((lift x y).left ≫ (psum A (x2 A) I.down).left) ^
      ((-1 : ℤ) ^ (2 - I.down.card)) = diff₂ (fun q : T ⟶ A => h q.left) x y :=
  (prod_square (lift x y) (fst A A) (snd A A) h).trans (by rw [lift_fst, lift_snd])

theorem hasGen_lam_pull (hL : L.IsLB) {T : Over S} (x y : T ⟶ A) (h : diff₂ (ptCls L T) x y = 1) :
    ∃ t : ((abelian₂ A L).pull (lift x y).left).Gen, t.IsGen :=
  hasGen_nested hL _ _ _ _ (by
    rw [Fintype.prod_unique, zpow_one]
    exact (prod_lam x y (cls L)).trans h)

theorem lbIso_lam_pull (hL : L.IsLB) (x y : A ⊗ A ⟶ A)
    (h : diff₂ (ptCls L _) x y = diff₂ (ptCls L _) (fst A A) (snd A A)) :
    LBIso (abelian₂ A L) ((abelian₂ A L).pull (lift x y).left) :=
  LBIso.symm (lbIso_nested hL _ _ _ _ _ _ (by
    rw [Fintype.prod_unique, zpow_one]
    exact (prod_lam x y (cls L)).trans (h.trans (prod_square_id _ _ (cls L)).symm)))

theorem eq_one_of_lam (hL : L.IsLB) (hK : Out.KTriv A L) {T : Over S} (x : T ⟶ A)
    (h : ∃ t : ((abelian₂ A L).pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) : x = 1 := by
  have H := ((KerPow.pull_iff _ _ _).1 h).pull (β_ T A).hom.left
    (φ' := fun I : ULift.{0} (Finset (Fin 2)) => (lift (fst T A ≫ x) (snd T A)).left ≫ (psum A (x2 A) I.down).left)
    (fun I => by
      rw [← Category.assoc, ← Over.comp_left, comp_lift, braiding_hom_snd_assoc, braiding_hom_fst])
  have H₁ : KerPow.LocGen L (fst T A).left
      (fun I : ULift.{0} (Finset (Fin 2)) => (lift (fst T A ≫ x) (snd T A)).left ≫ (psum A (x2 A) I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) := fun p => ⟨⊤, trivial, H.pull _ fun _ => rfl⟩
  have H₂ := BoxKernel.locGen_base hL (fst T A).left (K := Fin 2) ![(1 : T ⟶ A).left, x.left] ![1, -1]
  refine KerPow.eq_one_of_locGen hK x (H₁.comb hL H₂ fun U _ g => ?_)
  rw [prod_lam, Fin.prod_univ_two, Fin.prod_univ_two]
  show _ * (g (fst T A ≫ (1 : T ⟶ A)).left ^ (1 : ℤ) * g (fst T A ≫ x).left ^ (-1 : ℤ))⁻¹ =
    g ((fst T A ≫ x) * snd T A).left ^ (1 : ℤ) * g (snd T A).left ^ (-1 : ℤ)
  rw [MonObj.comp_one, diff₂]
  apply Additive.ofMul.injective
  simp only [zpow_neg, zpow_one, ofMul_mul, ofMul_inv]
  abel

end Bundle

theorem lbIso_diag (hL : Out.Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) :
    LBIso (lbPow P.L 2) ((abelian₂ P.A P.L).pull (lift (𝟙 P.A) (𝟙 P.A)).left) := by
  refine LBIso.symm (lbIso_nested P.isLB _ _ _ _ _ _ ?_)
  rw [Fintype.prod_unique, zpow_one]
  refine (prod_lam _ _ (cls P.L)).trans ?_
  rw [Fintype.prod_unique]
  have a := (hasGen_iff P.isLB _ _).1 (hL.mulPull S P 2)
  have b := (hasGen_iff P.isLB _ _).1 (MulPull.HasGen.pull (K := PUnit) P.rigid (toUnit P.A).left)
  rw [Fin.prod_univ_two] at a
  rw [Fintype.prod_unique, zpow_one] at b
  have a' : cls P.L (𝟙 P.A.left) ^ (4 : ℤ) * cls P.L (𝟙 P.A ^ 2).left ^ (-1 : ℤ) = 1 := a
  have b' : cls P.L (1 : P.A ⟶ P.A).left = 1 := b
  rw [pow_two, zpow_neg, zpow_one, mul_inv_eq_one] at a'
  show cls P.L (𝟙 P.A * 𝟙 P.A).left * (cls P.L (𝟙 P.A.left))⁻¹ * (cls P.L (𝟙 P.A.left))⁻¹ *
    cls P.L (1 : P.A ⟶ P.A).left = cls P.L (𝟙 P.A.left) ^ (2 : ℤ)
  rw [← a', b']
  group

theorem weilIs_of_lbIso_pow (hG : Out.GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L N : LB A.left} (hL : L.IsLB) (hN : N.IsLB) {d : ℕ} (hw : LBIso (lbPow L d) N) {n : ℤ} {T : Over S}
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs A L n x y c) : Out.WeilIs A N n x y (c ^ d) := by
  have e : CechPic.cls N hN = d • CechPic.cls L hL :=
    ((CechPic.cls_eq_iff (LB.isLB_linComb hL _ _) hN).2 hw).symm.trans (CechPic.cls_lbPow hL d _)
  have up : ∀ {Z : Over S} (θ : Out.ThetaGrp A L n Z), ∃ θ' : Out.ThetaGrp A N n Z, θ'.pt = θ.pt := fun {Z} θ => by
    have z := (CechPic.cls_eq_zero_iff (N := Out.thetaLB A L n θ.pt) (LB.isLB_linComb hL _ _)).2 ⟨θ.φ, θ.isGen⟩
    have z' := (CechPic.cls_linComb hL _ _ _).symm.trans z
    obtain ⟨t, ht⟩ := (CechPic.cls_eq_zero_iff (N := Out.thetaLB A N n θ.pt) (LB.isLB_linComb hN _ _)).1
      ((CechPic.cls_linComb hN _ _ _).trans (by
        simp only [e, map_nsmul, smul_comm _ d]
        rw [← Finset.smul_sum, z', smul_zero]))
    exact ⟨⟨θ.pt, t, ht⟩, rfl⟩
  obtain ⟨c', hc'⟩ := CommutatorPairing.exists_weilIs (k := n) (x := x) (y := y) hG hA hN
    (fun p => by
      obtain ⟨V, hV, ⟨θ, -, eθ, -⟩, -⟩ := h p
      obtain ⟨θ', e'⟩ := up θ
      exact ⟨V, hV, θ', e'.trans eθ⟩)
    (fun p => by
      obtain ⟨V, hV, ⟨θ₀, θ, -, eθ⟩, -⟩ := h p
      obtain ⟨θ', e'⟩ := up θ
      exact ⟨V, hV, θ', e'.trans eθ⟩)
  have hw' : LBIso (lbPow L d) (N.pull (𝟙 A : A ⟶ A).left) :=
    (CechPic.cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hN _ _)).1
      (((CechPic.cls_eq_iff _ hN).2 hw).trans (CechPic.pull_id _).symm)
  have := (weilIs_along_hom hG S A A (𝟙 A) L N d n T x y c c' hA hA hL hN inferInstance hw'
    (by rwa [Category.comp_id, Category.comp_id])).2 h
  rwa [← this]

theorem unitOn_inj {k : Type} [CommRing k] : Function.Injective (unitOn (R := k)) := fun _ _ h =>
  Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).1 (congrArg Units.val h))

theorem exists_smul_of_dvd {h k : ℕ} {a : Fin h ⊕ Fin h → ℤ} (H : ∀ b, (k : ℤ) ∣ omegaStd a b) : ∃ b, a = k • b := by
  have d : ∀ i, (k : ℤ) ∣ a i := by
    rintro (i | i)
    · simpa [omegaStd, Pi.single_apply] using H (Pi.single (.inr i) 1)
    · simpa [omegaStd, Pi.single_apply] using H (Pi.single (.inl i) 1)
  choose b hb using d
  exact ⟨b, funext fun i => by simpa using hb i⟩

theorem onto_torsion {I G : Type} [Fintype I] [Group G] {k : ℕ} (hk : k ≠ 0) (f : (I → ℤ) → G)
    (add : ∀ a b, f (a + b) = f a * f b) (tors : ∀ a, f a ^ k = 1) (ker : ∀ a, f a = 1 → ∃ b, a = k • b)
    (card : Nat.card {g : G // g ^ k = 1} = k ^ Fintype.card I) (g : G) (hg : g ^ k = 1) : ∃ a, f a = g := by
  haveI : NeZero k := ⟨hk⟩
  let F : (I → ZMod k) → {g : G // g ^ k = 1} := fun c => ⟨f fun i => (c i).val, tors _⟩
  have hF : Function.Injective F := fun c c' e => by
    have e₁ : f (fun i => (c i).val) = f fun i => (c' i).val := congrArg Subtype.val e
    have e₂ := add ((fun i => ((c i).val : ℤ)) - fun i => ((c' i).val : ℤ)) fun i => (c' i).val
    rw [sub_add_cancel, e₁] at e₂
    obtain ⟨b, hb⟩ := ker _ (mul_eq_right.1 e₂.symm)
    funext i
    have := congrArg (fun z : ℤ => (z : ZMod k)) (congrFun hb i)
    simpa [sub_eq_zero] using this
  have : Finite {g : G // g ^ k = 1} := Nat.finite_of_card_ne_zero (by rw [card]; exact pow_ne_zero _ hk)
  obtain ⟨c, hc⟩ := (hF.bijective_of_nat_card_le (by rw [card, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card])).2 ⟨g, hg⟩
  exact ⟨_, congrArg Subtype.val hc⟩

end GlobalTheory.SiegelOfPolarised

namespace GlobalTheory


open SiegelOfPolarised PrimNorm in
theorem exists_siegPre_of_polAV : Out.Laws → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (o : Type) [CommRing o] (K : Type) [Field K] (em : o →+* K) (h k : ℕ) (ζ : o) (ze : Kˣ) (P : Out.PolAV (Sp K)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp K)) ⟶ P.A)), P.g = h → (k : K) ≠ 0 → (ze : K) = em ζ → IsPrimitiveRoot ze k → (∀ x y, lev (x + y) = lev x * lev y) → (∀ x, lev x ^ k = 1) → (∀ x y, Out.WeilIs P.A P.L k (lev x) (lev y) (unitOn (ze ^ omegaStd x y))) → ∃ (c : SiegPre h k ζ (spMap em)) (φ : c.A ≅ P.A), IsMonHom φ.hom ∧ c.Principal ∧ LBIso c.P ((abelian₂ P.A P.L).pull (lift (fst c.A c.A ≫ φ.hom) (snd c.A c.A ≫ φ.hom)).left) ∧ ∀ x, c.lev x ≫ φ.hom = lev x := by
  intro hL _ o _ K _ em h k ζ ze P lev hg hk hze hprim add tors weil
  have lam : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  have dg : ((abelian₂ P.A P.L).pull (lift (𝟙 P.A) (𝟙 P.A)).left).IsLB := LB.isLB_linComb lam _ _
  have lev0 : lev 0 = 1 := mul_eq_left.1 ((add 0 0).symm.trans (by rw [add_zero]))
  let c : SiegPre h k ζ (spMap em) :=
    { A := P.A
      ab := P.isAb
      P := abelian₂ P.A P.L
      isLB := lam
      rig₁ := hasGen_lam_pull P.isLB _ _ (by simp [diff₂])
      rig₂ := hasGen_lam_pull P.isLB _ _ (by simp [diff₂])
      symm := lbIso_lam_pull P.isLB _ _ (diff₂_comm _ _)
      lev := lev
      lev_add := add
      lev_tors := tors
      geom := by
        intro k' _ _ x β z hx hz
        obtain ⟨φ₀, rfl⟩ := Spec.map_surjective x
        let φ : K →+* k' := φ₀.hom
        have hβ : φ.comp em = β := by
          have : CommRingCat.ofHom em ≫ φ₀ = CommRingCat.ofHom β := by
            rw [← Spec.map_inj, Spec.map_comp]; exact hx
          exact congrArg (fun q => q.hom) this
        obtain rfl : z = Units.map φ.toMonoidHom ze := Units.ext (by rw [hz, ← hβ]; simp [hze])
        have hz' : IsPrimitiveRoot (Units.map φ.toMonoidHom ze) k :=
          hprim.map_of_injective (Units.map_injective φ.injective)
        have hk' : (k : k') ≠ 0 := by rw [← map_natCast φ]; exact (map_ne_zero φ).2 hk
        have hk₀ : k ≠ 0 := fun e => hk (by simp [e])
        have W : ∀ a b, Out.WeilIs P.A P.L k (toUnit (Over.mk (Spec.map φ₀)) ≫ lev a) (toUnit _ ≫ lev b)
            (unitOn (Units.map φ.toMonoidHom ze ^ omegaStd a b)) := fun a b => by
          have H := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB (toUnit (Over.mk (Spec.map φ₀))) (weil a b)
          have e : Units.map (toUnit (Over.mk (Spec.map φ₀))).left.appTop.hom.toMonoidHom
              (unitOn (ze ^ omegaStd a b)) = unitOn (Units.map φ.toMonoidHom (ze ^ omegaStd a b)) :=
            Units.ext (congrArg (fun q => q.hom (ze ^ omegaStd a b).val) (Scheme.ΓSpecIso_inv_naturality φ₀)).symm
          rw [e, map_zpow] at H
          exact H
        have ker : ∀ a, toUnit (Over.mk (Spec.map φ₀)) ≫ lev a = 1 → ∃ b, a = k • b := fun a ha =>
          exists_smul_of_dvd fun b => by
            have w₁ := W a b
            have w₀ := W 0 b
            rw [ha] at w₁
            rw [lev0, MonObj.comp_one] at w₀
            have e := unitOn_inj (CommutatorPairing.weilIs_unique hL.globalFns P.isAb P.isLB w₁ w₀)
            rw [show omegaStd 0 b = 0 by simp [omegaStd], zpow_zero] at e
            exact (hz'.zpow_eq_one_iff_dvd _).1 e
        refine ⟨fun a => ⟨ker a, ?_⟩, onto_torsion hk₀ _ (fun a b => by rw [add, MonObj.comp_mul])
          (fun a => by rw [← MonObj.comp_pow, tors, MonObj.comp_one]) ker ?_, fun a b => ?_⟩
        · rintro ⟨b, rfl⟩
          have pw : ∀ n : ℕ, lev (n • b) = lev b ^ n := fun n => by
            induction n with
            | zero => rw [zero_smul, pow_zero, lev0]
            | succ n ih => rw [succ_nsmul, add, ih, pow_succ]
          rw [pw, tors, MonObj.comp_one]
        · rw [(hL.mulN _ P k (Nat.pos_of_ne_zero hk₀)).2.2.2.2 k' _ hk', hg]
          simp [two_mul]
        · have H := weilIs_of_lbIso_pow hL.globalFns P.isAb P.isLB dg (lbIso_diag hL P) (W a b)
          have e : unitOn (Units.map φ.toMonoidHom ze ^ (2 * omegaStd a b)) =
              unitOn (Units.map φ.toMonoidHom ze ^ omegaStd a b) ^ 2 := by
            rw [mul_comm, zpow_mul, zpow_ofNat]
            exact map_pow _ _ _
          rw [e]
          exact H }
  refine ⟨c, Iso.refl _, inferInstanceAs (IsMonHom (𝟙 P.A)), ⟨?_, fun T x hx => eq_one_of_lam P.isLB P.ktriv x hx⟩,
    lbIso_lam_pull P.isLB _ _ (congrArg₂ _ (Category.comp_id _) (Category.comp_id _)), fun x => Category.comp_id _⟩
  have R := relAmple_finite_pow_iso _ P.A P.A (𝟙 _) P.L 2 two_pos P.isAb P.isAb P.isLB (inferInstanceAs (IsFinite (𝟙 P.A.left)))
  have R' := relAmple_finite_pow_iso _ P.A P.A (𝟙 _) (lbPow P.L 2) 2 two_pos P.isAb P.isAb
    (LB.isLB_linComb P.isLB _ _) (inferInstanceAs (IsFinite (𝟙 P.A.left)))
  exact R'.2.2.2 _ dg (lbIso_diag hL P) (R.2.1.2 P.ample)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FibresSplitOfOpenImmersionCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory

theorem splitFibre_of_isOpenImmersion {Y Z : Scheme.{0}} (f : Y ⟶ Z) [IsOpenImmersion f] (G : Over Z) [GrpObj G]
    (G' : Over Y) [GrpObj G'] (φ : G'.left ⟶ G.left) (hφ : IsGrpPullback G' G f φ) (h : SplitFib G') (y : Y) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra (Z.residueField (f y)) k), FiniteDimensional (Z.residueField (f y)) k ∧
      Algebra.IsSeparable (Z.residueField (f y)) k ∧ ∃ S : SplitExt (Sp k),
        S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField (f y)) k)) ≫
          Z.fromSpecResidueField (f y))).obj G) := by
  obtain ⟨k, _, _, hfin, hsep, S, hGt⟩ := h y
  let ε : Z.residueField (f y) ≃+* Y.residueField y := (asIso (f.residueFieldMap y)).commRingCatIsoToRingEquiv
  let A : Algebra (Z.residueField (f y)) k :=
    ((algebraMap (Y.residueField y) k).comp (f.residueFieldMap y).hom).toAlgebra
  have hc : (algebraMap (Z.residueField (f y)) k).comp (ε.symm : Y.residueField y →+* Z.residueField (f y)) =
      ((RingEquiv.refl k : k ≃+* k) : k →+* k).comp (algebraMap (Y.residueField y) k) := by
    ext a
    exact congrArg (algebraMap (Y.residueField y) k) (ε.apply_symm_apply a)
  refine ⟨k, inferInstance, A, Module.Finite.of_equiv_equiv ε.symm (RingEquiv.refl k) hc,
    Algebra.IsSeparable.of_equiv_equiv ε.symm (RingEquiv.refl k) hc, S, ?_⟩
  have key : (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k)) ≫ Y.fromSpecResidueField y) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField (f y)) k)) ≫ Z.fromSpecResidueField (f y) := by
    have a₁ : Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField (f y)) k)) =
        Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k)) ≫ Spec.map (f.residueFieldMap y) := by
      rw [← Spec.map_comp]
      rfl
    rw [a₁, Category.assoc, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rw [← key]
  obtain ⟨e, he, -⟩ := grpPullback_iso hφ (isGrpPullback_pullback G f)
  have : IsMonHom ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k)) ≫
      Y.fromSpecResidueField y)).mapIso e).hom := by
    rw [Functor.mapIso_hom]
    infer_instance
  have h₀ := isGt_of_iso ((Over.pullback _).mapIso e) hGt
  have : IsMonHom (pullCompIso (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k)) ≫
      Y.fromSpecResidueField y) f G).symm.hom := by
    show IsMonHom (pullCompIso _ _ _).inv
    infer_instance
  exact isGt_of_iso (pullCompIso _ f G).symm h₀

theorem splitFib_of_openCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, SplitFib (u i).G) → SplitFib t.G := by
  intro E _ _ _ H Z t I Y f u m ho hc hs z
  obtain ⟨i, y, rfl⟩ := hc z
  have := ho i
  exact splitFibre_of_isOpenImmersion (f i) t.G (u i).G _ (m i).cart (hs i) y

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelObjectOfCoveringPullbacks
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.FullDescent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {n N : ℕ}

theorem exists_lift {S S' : Scheme.{0}} (f : S' ⟶ S) {k : Type} [Field k] (x : Sp k ⟶ S) (p : Sp k)
    (hp : x p ∈ Set.range f) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (i : k →+* Ω) (y : Sp Ω ⟶ S'), spMap i ≫ x = y ≫ f := by
  obtain ⟨q, hq⟩ := hp
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := x) (g := f) p q hq.symm
  let Ω : Type := AlgebraicClosure ((pullback x f).residueField z)
  let u : Sp Ω ⟶ pullback x f :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback x f).residueField z) Ω)) ≫ (pullback x f).fromSpecResidueField z
  refine ⟨Ω, inferInstance, inferInstance, (Spec.preimage (u ≫ pullback.fst x f)).hom, u ≫ pullback.snd x f, ?_⟩
  have e : spMap (Spec.preimage (u ≫ pullback.fst x f)).hom = u ≫ pullback.fst x f := Spec.map_preimage _
  rw [e]
  exact (Category.assoc _ _ _).trans ((congrArg (u ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)

theorem tate_push {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (ν : SABMap t' t f)
    {k : Type} [Field k] {y : Sp k ⟶ S'} {x : Sp k ⟶ S} (hx : x = y ≫ f)
    (I : TateIso D k (Over.mk y ⟶ t'.G) (fun a g => g ≫ t'.act.act a)
        (fun m g g' c => Out.WeilIs t'.G t'.PP.L m g g' (unitOn c))) :
    ∃ J : TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun m g g' c => Out.WeilIs t.G t.PP.L m g g' (unitOn c)),
      J.ζ = I.ζ ∧ ∀ m a, (J.ev m a).left = (I.ev m a).left ≫ ν.φ := by
  subst hx
  have hL : LBIso t'.PP.L (t.PP.L.pull ν.cm.F) := by
    obtain ⟨w, hw, -⟩ := ν.lin
    exact ⟨w, hw⟩
  refine ⟨ObjPull.tateMove (ObjPull.pushEquiv ν.cart (Over.mk y)).symm (fun c g => ?_) (fun m g g' c hc => ?_) I,
    rfl, fun _ _ => rfl⟩
  · obtain ⟨g, rfl⟩ := (ObjPull.pushEquiv ν.cart (Over.mk y)).surjective g
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_eq]
    apply Over.OverMorphism.ext
    show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
    rw [Category.assoc, ← ν.act, Category.assoc]
  · exact (weilIs_iff_of_isGrpPullback_comm S S' t.G t'.G f ν.cm.F t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB ν.cart hL
      (Over.mk y) m _ _ g g' _ (ObjPull.pushEquiv_symm_left ν.cart (Over.mk y) g).symm
      (ObjPull.pushEquiv_symm_left ν.cart (Over.mk y) g').symm).1 hc

theorem torsion_ext (hL : Out.Laws) {S : Scheme.{0}} (t : SAB H S) (hp : IsProper t.G.hom)
    (ha : Out.RelAmple t.G t.PP.L) (hk : Out.KTriv t.G t.PP.L) {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed K]
    [CharZero K] (i : K →+* Ω) (x : Sp K ⟶ S) :
    Function.Injective (TateIsoFieldExt.precomp
        (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) t.G) ∧
      ∀ m, 0 < m → ∀ z : Over.mk (spMap i ≫ x) ⟶ t.G, z ^ m = 1 → ∃ y : Over.mk x ⟶ t.G, y ^ m = 1 ∧
        TateIsoFieldExt.precomp (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) t.G y = z := by
  obtain ⟨P, φ, -, hφ, -⟩ := exists_polAV_pullback_of_isLocalRing E H S t hp ha hk K x
  obtain ⟨hinj, honto⟩ := torsion_points_field_extension hL (Sp K) P K Ω i (𝟙 _)
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hφ (𝟙 _) x (Category.id_comp _).symm
  obtain ⟨e', he'⟩ := exists_mulEquiv_of_isGrpPullback hφ (spMap i ≫ 𝟙 _) (spMap i ≫ x) (by simp)
  have key : ∀ y, TateIsoFieldExt.precomp (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) t.G (e y) =
      e' ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ 𝟙 (Sp K)) ⟶ Over.mk (𝟙 (Sp K))) ≫ y) := fun y => by
    apply Over.OverMorphism.ext
    rw [he']
    show spMap i ≫ (e y).left = (spMap i ≫ y.left) ≫ φ
    rw [he]
    exact (Category.assoc _ _ _).symm
  refine ⟨fun y y' h => ?_, fun m hm z hz => ?_⟩
  · obtain ⟨y, rfl⟩ := e.surjective y
    obtain ⟨y', rfl⟩ := e.surjective y'
    rw [key, key] at h
    exact congrArg e (hinj (e'.injective h))
  · obtain ⟨z, rfl⟩ := e'.surjective z
    rw [← map_pow, map_eq_one_iff _ e'.injective] at hz
    obtain ⟨y, hy, rfl⟩ := honto m z (Nat.cast_ne_zero.2 hm.ne') hz
    exact ⟨e y, by rw [← map_pow, hy, map_one], key y⟩

theorem fullObj_of_cover : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lv : D.La → (𝟙_ (Over S) ⟶ t.G)), 0 < N → IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ a c, lv (a + c) = lv a * lv c) → (∀ a, lv (N • a) = 1) → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (ν : SABMap t' t f) (lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)), p ∈ Set.range f ∧ (∀ a, (lv' a).left ≫ ν.φ = f ≫ (lv a).left) ∧ FullObj D (f ≫ s) t' lv') → FullObj D s t lv := by
  intro hL E _ _ _ H D n N S s t lv hN hp ha hk hadd hker hcov
  refine ⟨hp, ha, hk, hadd, hker, fun k _ _ _ x β hx => ?_⟩
  obtain ⟨S', f, t', ν, lv', hq, hl, o⟩ := hcov (x (default : PrimeSpectrum k))
  obtain ⟨Ω, _, _, i, y, hy⟩ := exists_lift f x _ hq
  have : CharZero Ω := (i.charZero_iff i.injective).1 inferInstance
  have hy' : y ≫ f ≫ s = spMap (i.comp β) := by
    rw [← Category.assoc, ← hy, Category.assoc, hx]
    exact (Spec.map_comp _ _).symm
  obtain ⟨hdet, I', hI', hA'⟩ := o.geom Ω y (i.comp β) hy'
  refine ⟨?_, ?_⟩
  · refine (detCond_iff_of_field_extension E H D S t.G k Ω i x t.act _ t.semi.smooth).1 ?_
    rw [hy]
    exact (detCond_iff_of_sabMap E H D S S' t t' f ⟨ν⟩ Ω y _).1 hdet
  obtain ⟨J, hJ, hJ'⟩ := tate_push ν hy I'
  obtain ⟨hinj, honto⟩ := torsion_ext hL t hp ha hk i x
  let g : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  obtain ⟨I, hI⟩ := TateIsoFieldExt.down D i (TateIsoFieldExt.precomp g t.G)
    (act := fun a z => z ≫ t.act.act a) (act' := fun a z => z ≫ t.act.act a)
    (e' := fun m z z' c => Out.WeilIs t.G t.PP.L m z z' (unitOn c))
    (e := fun m z z' c => Out.WeilIs t.G t.PP.L m z z' (unitOn c)) hinj honto
    (fun c z => (Category.assoc g z (t.act.act c)).symm)
    (fun c => by
      haveI := t.act.hom c
      exact MonObj.one_comp (t.act.act c))
    (fun m z z' c => weilIs_fieldExt_iff S t.G k Ω i x t.PP.L m z z' c
      ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩ t.PP.isLB) J
  obtain ⟨h₁, h₂⟩ := hI N hN
  refine ⟨I, i.injective ?_, fun a => hinj ?_⟩
  · rw [← h₁, hJ, hI']
    rfl
  · rw [← h₂]
    apply Over.OverMorphism.ext
    rw [hJ', ← hA', Over.comp_left, ObjPull.toUnit_left', Category.assoc, hl]
    show spMap i ≫ (toUnit (Over.mk x) ≫ lv a).left = y ≫ f ≫ (lv a).left
    rw [Over.comp_left, ObjPull.toUnit_left', ← Category.assoc y, ← hy]
    exact (Category.assoc _ _ _).symm

end GlobalTheory.FullDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullObjOfObj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem RZ.rt_coe (S A : ℕ) : ((RZ.rt H S A : RZ H S A) : ℂ) = H.rt0 := by
  have h2 : ((2 : RZ H S A) : ℂ) = 2 := map_ofNat (RZ H S A).subtype 2
  unfold RZ.rt
  push_cast
  rw [h2]
  ring

theorem fullObj_of_obj {D : Datum H} {l : Level H} {n : ℕ} {S : Scheme.{0}} (s : S ⟶ Sp (KA l))
    (o : Obj D l (baseKA l) s) (β : RZ H n l.A →+* KA l) (hβ : IsInc (RZ H n l.A).subtype (KA l).val.toRingHom β) :
    FullObj D (s ≫ spMap β) o.t o.etaA := by
  unfold IsInc at hβ
  have hρ : β (RZ.rt H n l.A) = (baseKA l).ρ := by
    apply Subtype.ext
    show ((β (RZ.rt H n l.A) : ℂ)) = H.rt0
    rw [← RZ.rt_coe (H := H) n l.A]
    exact hβ (RZ.rt H n l.A)
  have hze : β (RZ.ze H n l.A) = (baseKA l).ζ := by
    apply Subtype.ext
    show ((β (RZ.ze H n l.A) : ℂ)) = zeta l.A
    exact hβ (RZ.ze H n l.A)
  refine ⟨o.proper, o.ample, o.ktriv, o.etaA_add, o.etaA_ker, ?_⟩
  intro k _ _ _ x β' hx
  obtain ⟨g0, hg0⟩ : ∃ g0 : KA l →+* k, x ≫ s = spMap g0 := by
    refine ⟨(Spec.preimage (x ≫ s)).hom, ?_⟩
    unfold spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hb : β' = g0.comp β := by
    have h1 : Spec.map (CommRingCat.ofHom β') = Spec.map (CommRingCat.ofHom (g0.comp β)) := by
      unfold spMap at hx hg0
      rw [← hx, ← Category.assoc, hg0, ← Spec.map_comp, CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  subst hb
  obtain ⟨hdet, I, hI1, hI2, -⟩ := o.geom k x g0 hg0
  refine ⟨?_, I, ?_, hI2⟩
  · rw [RingHom.comp_apply, hρ]
    exact hdet
  · rw [RingHom.comp_apply, hze]
    exact hI1

end GlobalTheory.Models
end

