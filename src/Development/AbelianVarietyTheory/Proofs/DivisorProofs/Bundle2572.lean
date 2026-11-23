module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0161
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2488
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricTorsionMatchOfCharacterMapOnTorus
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.HomTorChar

theorem eq_torusMap_of_torusHomOf {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' →+ X)
    (t : splitTorus S X ⟶ splitTorus S X') (ht : GlobalTheory.Mum.Two.TorusHomOf h t) : t = GlobalTheory.SplitTorus.torusMap S h := by
  refine (GlobalTheory.SplitTorus.eq_torusMap_iff t h).2 fun b => ?_
  have e := congrArg Units.val (ht b)
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' b)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' b).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [this, GlobalTheory.SplitTorus.charUnit_val, GlobalTheory.SplitTorus.charUnit_val] at e
  exact e

theorem torMatch_of_onTorus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (p : G ⟶ G₀), IsMonHom p → ∀ h : D₀.toPre.X →+ D.toPre.X, GlobalTheory.Mum.Two.OnTorus U.toUnifPre U₀.toUnifPre p h → GlobalTheory.Poinc.Eq8.TorMatch U₀ U (RingHom.id R) p.left h := by
  intro R _ _ _ hR D' D A' A G' G _ _ _ _ hG' hG U' U p hpm ρ hon
  have hr : ∀ x ∈ maximalIdeal R ^ (0 + 1), residue R x = 0 := fun x hx =>
    (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx)
  have hp := isGrpPullback_pullback G (spMap (residue R))
  have hp' := isGrpPullback_pullback G' (spMap (residue R))
  have e : ((Over.pullback (spMap (residue R))).map p).left ≫ pullback.fst G.hom (spMap (residue R)) =
      pullback.fst G'.hom (spMap (residue R)) ≫ p.left := pullback.lift_fst _ _ _
  have hρ : GlobalTheory.TorusPart.gtTorus (U'.gt 0) hr hp' ≫ (Over.pullback (spMap (residue R))).map p =
      GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hr hp := by
    obtain ⟨t, ht, hi⟩ := hon 0
    have htm := eq_torusMap_of_torusHomOf ρ t ht
    have k := GlobalTheory.TorusPart.isGrpPullback_thickLift hr hp
    have k' := GlobalTheory.TorusPart.isGrpPullback_thickLift hr hp'
    have e' : ((Over.pullback (spMap (residue R))).map p).left ≫ GlobalTheory.TorusPart.thickLift hr hp =
        GlobalTheory.TorusPart.thickLift hr hp' ≫ ((Over.pullback (thick R (maximalIdeal R) 0)).map p).left := by
      apply pullback.hom_ext
      · rw [Category.assoc, GlobalTheory.TorusPart.thickLift_fst, e, Category.assoc]
        simp only [GlobalTheory.TorusPart.thickLift, Over.pullback_map_left, ← Category.assoc, pullback.lift_fst]
      · have w := Over.w ((Over.pullback (spMap (residue R))).map p)
        simp only [GlobalTheory.TorusPart.thickLift]
        rw [Category.assoc, pullback.lift_snd, Category.assoc, ← Category.assoc _ _ (GlobalTheory.TorusPart.thickPt 0 hr), w]
        simp only [Over.pullback_map_left]
        rw [pullback.lift_snd, pullback.lift_snd]
    have hc := GlobalTheory.TorusPart.pullTorus_comp k' k _ _ e' (U'.gt 0).i
    unfold GlobalTheory.TorusPart.gtTorus
    rw [← hc, hi, htm, GlobalTheory.TorusPart.pullTorus_torusMap_comp]
  intro F _ _ i₁ i₂ hF k hk τ τ' q q' a a' hτ'k hττ' hqy hq hq'y hq' ha ha'
  have hi : i₁ = i₂ := Algebra.algebra_ext _ _ fun x =>
    RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors R)
      (j := @algebraMap _ _ _ _ i₁) (k := @algebraMap _ _ _ _ i₂) (RingHom.ext hF)) x
  subst hi
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk
    · exact h
  obtain ⟨s, s1, s2, s3, s4⟩ := GlobalTheory.ToricTorsionUnif.main R hR G hG D A U k hk1
  obtain ⟨s', s1', s2', s3', s4'⟩ := GlobalTheory.ToricTorsionUnif.main R hR G' hG' D' A' U' k hk1
  let ρm := AddMonoidHom.toMultiplicative ρ
  have powc : ∀ {H : Type} [CommGroup H] (f : Multiplicative D'.toPre.X →* H), f ^ k = 1 → (f.comp ρm) ^ k = 1 :=
    fun f hf => MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hf]; rfl
  have hτ : τ = τ'.comp ρm := MonoidHom.ext fun x => hττ' (Multiplicative.toAdd x)
  have hτk : τ ^ k = 1 := by
    rw [hτ]; exact powc τ' hτ'k
  let c : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  rw [s4 F c τ hτk q a rfl hqy hq ha, ← Category.assoc, s4' F c τ' hτ'k q' a' rfl hq'y hq' ha']
  obtain ⟨O, hO, hloc⟩ := IsLocalRing.exists_factor_valuationRing c
  let φ : R →+* O := c.codRestrict O.toSubring hO
  haveI : IsLocalHom φ := hloc
  have hc : c = O.subtype.comp φ := rfl
  obtain ⟨τO, hτO⟩ := GlobalTheory.ToricTorsionCompare.units_of_pow_eq_one F O _ k hk1 τ' hτ'k
  have hτOk : τO ^ k = 1 := by
    refine MonoidHom.ext fun x => Units.ext (Subtype.ext ?_)
    have := congrArg (fun f => ((f x : Fˣ) : F)) hτ'k
    simp only [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one] at this ⊢
    rw [SubmonoidClass.coe_pow, hτO, this]; rfl
  let τR := τO.comp ρm
  have hτR : τR ^ k = 1 := powc τO hτOk
  have hkO : IsUnit (k : O) := by simpa using hk.map φ
  have hxy : s O φ τR hτR = s' O φ τO hτOk ≫ p := by
    refine GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) G hG.smooth O (spMap φ) k hkO _ _ ?_
      (ResidueField O) (residue O) inferInstance ?_
    · rw [s1, ← GlobalTheory.Poinc.HomTor.pow_comp_monHom, s1', MonObj.one_comp]
    · let τ₀ : Multiplicative D'.toPre.X →* (ResidueField O)ˣ := (Units.map (residue O).toMonoidHom).comp τO
      have h₀ : τ₀ ^ k = 1 := by
        rw [show τ₀ ^ k = (Units.map (residue O).toMonoidHom).comp (τO ^ k) by ext x; simp [τ₀]]
        rw [hτOk]; ext; simp
      let τ₁ := τ₀.comp ρm
      have h₁ : τ₁ ^ k = 1 := powc τ₀ h₀
      let z : Over.mk (spMap (ResidueField.map φ)) ⟶ splitTorus (Sp (ResidueField R)) D'.toPre.X :=
        (GlobalTheory.splitTorusPointsEquiv _ _ _).symm
          ((Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField O))).inv.hom.toMonoidHom).comp τ₀)
      have hz : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ₀ (Multiplicative.ofAdd χ)) := fun χ => by
        simp only [GlobalTheory.UU.chV, z, MulEquiv.apply_symm_apply]; rfl
      have hz₁ : ∀ χ, GlobalTheory.UU.chV (z ≫ GlobalTheory.SplitTorus.torusMap _ ρ) χ = unitOn (τ₁ (Multiplicative.ofAdd χ)) :=
        fun χ => by
          apply Units.ext
          rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.SplitTorus.val_eq,
            GlobalTheory.SplitTorus.val_comp_torusMap, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val,
            ← GlobalTheory.UU.chV_val, hz]
          rfl
      have hres : (residue O).comp φ = (ResidueField.map φ).comp (residue R) := by
        ext r; simp [ResidueField.map_residue]
      rw [Over.comp_left, ← Category.assoc,
        ← s2 O _ φ ((residue O).comp φ) (residue O) τR hτR τ₁ h₁ rfl (fun χ => rfl),
        ← s2' O _ φ ((residue O).comp φ) (residue O) τO hτOk τ₀ h₀ rfl (fun χ => rfl),
        s3 _ _ (residue R) hr _ (ResidueField.map φ) _ _ hp τ₁ h₁ _ hres hz₁,
        s3' _ _ (residue R) hr _ (ResidueField.map φ) _ _ hp' τ₀ h₀ z hres hz,
        Category.assoc z, ← hρ, Category.assoc _ _ p.left, ← e]
      simp only [Over.comp_left, Category.assoc]
  rw [s2 O F φ c O.subtype τR hτR τ hτk hc (fun χ => by simp [τR, hτ, hτO]),
    s2' O F φ c O.subtype τO hτOk τ' hτ'k hc (fun χ => by simp [hτO]), hxy, Over.comp_left, Category.assoc]

end GlobalTheory.Poinc.HomTorChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFramesSectionValuesRatioRootOfUnity
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.Poinc.TorsRatio

variable {V : Type} [CommRing V] [IsDomain V]

def cstK (z : (TFK (R := V) (FractionRing V)).left) :
    FractionRing V →+* (TFK (R := V) (FractionRing V)).left.presheaf.stalk z :=
  ((TFK (R := V) (FractionRing V)).left.presheaf.germ ⊤ z trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom

theorem cst_eq_cstK (z : (TFK (R := V) (FractionRing V)).left) (a : FractionRing V) :
    GlobalTheory.UT.cst (R := V) (FractionRing V) z a = cstK z a :=
  gs_eq (𝟙 _) z ⊤ trivial _

theorem pt_eq (z z' : (TFK (R := V) (FractionRing V)).left) : z = z' :=
  Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) z z'

theorem cstK_surj (z : (TFK (R := V) (FractionRing V)).left) : Function.Surjective (cstK (V := V) z) := by
  intro a
  obtain ⟨U, hU, s, rfl⟩ := (TFK (R := V) (FractionRing V)).left.presheaf.germ_exist a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => pt_eq z y ▸ hU
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv).2 s
  exact ⟨x, congrArg ((TFK (R := V) (FractionRing V)).left.presheaf.germ ⊤ z trivial).hom hx⟩

theorem frame_ratio {A : PolAV (Sp (FractionRing V))} {x : TFK (R := V) (FractionRing V) ⟶ A.A} {e e' : FrAt x}
    (he : e.IsGen) (he' : e'.IsGen) : ∃ l : FractionRing V, l ≠ 0 ∧ ∀ z J, Good A.L z J →
      (Geo.Tor.val e' (𝟙 _) z J).val = cstK z l * (Geo.Tor.val e (𝟙 _) z J).val := by
  let z : (TFK (R := V) (FractionRing V)).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  choose J' hJ' using fun χ : (TFK (R := V) (FractionRing V)).left ⟶ A.A.left => Geo.Tor.exists_chart A.isLB (χ z)
  replace hJ' : Good A.L z J' := hJ'
  obtain ⟨l, hl⟩ := cstK_surj z (Geo.Tor.val e' (𝟙 _) z J' * (Geo.Tor.val e (𝟙 _) z J')⁻¹).val
  refine ⟨l, fun h => ?_, fun z' J hJ => ?_⟩
  · rw [h, map_zero] at hl
    exact Units.ne_zero _ hl.symm
  · obtain rfl := pt_eq z z'
    have t₁ : Geo.Tor.val e (𝟙 _) z J = _ * Geo.Tor.val e (𝟙 _) z J' :=
      gen_trans he (𝟙 _) z (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have t₂ : Geo.Tor.val e' (𝟙 _) z J = _ * Geo.Tor.val e' (𝟙 _) z J' :=
      gen_trans he' (𝟙 _) z (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    rw [hl, t₁, t₂, ← Units.val_mul]
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

end GlobalTheory.Poinc.TorsRatio

namespace GlobalTheory.Poinc.TorsRatio

theorem valAt_torsFrame_ratio : ∀ (V : Type) [CommRing V] [IsDomain V] (A : PolAV (Sp (FractionRing V)))
    (ρA : LB.Gen (A.L.pull (eSec A.A))), ρA.IsGen → ∀ (N : ℕ), 1 ≤ N →
    ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e e' : FrAt x), IsTorsFrame A ρA N x e → IsTorsFrame A ρA N x e' →
    ∀ (th : SecA A (FractionRing V) 1) (c : FractionRing V), ValAt th x e c →
      ∃ u : FractionRing V, u ^ (N ^ 2) = 1 ∧ ValAt th x e' (u * c) := by
  intro V _ _ A ρA _ N _ x e e' H H' th c hv
  obtain ⟨-, he, α, hα, nα, cα⟩ := H
  obtain ⟨-, he', α', hα', nα', cα'⟩ := H'
  obtain ⟨l, hl0, hl⟩ := frame_ratio he he'

  have hp : Function.Surjective A.A.hom.appTop.hom := (GlobalTheory.globalFns_holds _ _ A.isAb).2
  have hαα : ∀ (Z : Scheme.{0}) (r : Z ⟶ A.A.left) (z : Z) J, Good A.L z J →
      Geo.Tor.val α r z J = Geo.Tor.val α' r z J :=
    gen_unique A.isLB A.A.hom (eSec A.A) (Over.w η[A.A]) hp hα hα' (fun w I hI => by
      have a := val_corr hI nα (𝟙 _)
      have b := val_corr hI nα' (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a b
      exact a.trans b.symm)
  let z : (TFK (R := V) (FractionRing V)).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  choose J hJ using fun χ : (TFK (R := V) (FractionRing V)).left ⟶ A.A.left => Geo.Tor.exists_chart A.isLB (χ z)
  replace hJ : Good A.L z J := hJ
  have q : Geo.Tor.val e (𝟙 _) z J ^ ((N : ℤ) ^ 2) = Geo.Tor.val e' (𝟙 _) z J ^ ((N : ℤ) ^ 2) := by
    have a := val_corr hJ cα (𝟙 _)
    have b := val_corr hJ cα' (𝟙 _)
    have p₁ : Geo.Tor.val (powFrame A.A A.L x e ((N : ℤ) ^ 2)) (𝟙 _) z J =
      Geo.Tor.val e (𝟙 _) z J ^ ((N : ℤ) ^ 2) := map_zpow _ _ _
    have p₂ : Geo.Tor.val (powFrame A.A A.L x e' ((N : ℤ) ^ 2)) (𝟙 _) z J =
      Geo.Tor.val e' (𝟙 _) z J ^ ((N : ℤ) ^ 2) := map_zpow _ _ _
    rw [val_mul hJ, val_pull hJ] at a b
    rw [← p₁, ← p₂, a, b, hαα _ _ z J hJ]
  have hlN : l ^ (N ^ 2) = 1 := by
    have q' := congrArg Units.val q
    rw [show ((N : ℤ) ^ 2) = ((N ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, hl z J hJ, mul_pow, ← map_pow] at q'
    have hu : IsUnit ((Geo.Tor.val e (𝟙 _) z J).val ^ (N ^ 2)) := (Units.isUnit _).pow _
    have h1 : cstK z (l ^ (N ^ 2)) = cstK z 1 := by
      rw [map_one]
      exact hu.mul_left_inj.1 (by rw [_root_.one_mul]; exact q'.symm)
    exact (cstK z).injective h1
  refine ⟨l⁻¹, by rw [inv_pow, hlN, inv_one], fun z' J' hJ' => ?_⟩
  rw [hv z' J' hJ']
  have r₁ : Geo.Tor.val (powFrame A.A A.L x e ((1 : ℕ) : ℤ)) (𝟙 _) z' J' = Geo.Tor.val e (𝟙 _) z' J' ^ ((1 : ℕ) : ℤ) :=
    map_zpow _ _ _
  have r₂ : Geo.Tor.val (powFrame A.A A.L x e' ((1 : ℕ) : ℤ)) (𝟙 _) z' J' =
      Geo.Tor.val e' (𝟙 _) z' J' ^ ((1 : ℕ) : ℤ) := map_zpow _ _ _
  rw [r₁, r₂, Nat.cast_one, zpow_one, zpow_one, hl z' J' hJ']
  simp only [id, cst_eq_cstK]
  rw [← _root_.mul_assoc, ← map_mul, mul_comm l⁻¹ c, inv_mul_cancel_right₀ hl0]

end GlobalTheory.Poinc.TorsRatio
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsEighthPowerProjections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.Labels

theorem eq_comp_of_genMap {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D D' : DegData R (maximalIdeal R)}
    {A A' : PolAV (Sp (FractionRing R))} {G G' : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G') (p : G' ⟶ G)
    (π : A'.A ⟶ A.A) (h : (Over.pullback (jK R)).map p ≫ U.gen.hom = U'.gen.hom ≫ π) {T : Over (Sp (FractionRing R))}
    (a : T ⟶ A.A) (a' : T ⟶ A'.A) (e : a.left ≫ genMap U = a'.left ≫ genMap U' ≫ p.left) : a = a' ≫ π := by
  have hU := GlobalTheory.TauFormHom.isGrpPullback_genMap U
  have h' : U'.gen.inv ≫ (Over.pullback (jK R)).map p = π ≫ U.gen.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h'' : π.left ≫ U.gen.inv.left = U'.gen.inv.left ≫ ((Over.pullback (jK R)).map p).left := by
    rw [← Over.comp_left, ← Over.comp_left, h']
  have hf : ((Over.pullback (jK R)).map p).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R) ≫ p.left := by
    simp only [Over.pullback_map_left, pullback.lift_fst]
  apply Over.OverMorphism.ext
  refine hU.1.hom_ext ?_ ?_
  · rw [e, Over.comp_left, genMap, genMap]
    simp only [Category.assoc]
    rw [reassoc_of% h'', hf]
  · rw [Over.w a, Over.w (a' ≫ π)]

theorem commutatorPairing_eighthPower_bundle : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P P' : PolAV S) (pr : Fin 8 → (P'.A ⟶ P.A)), (∀ a, IsMonHom (pr a)) → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), LBIso P'.L (LB.LinComb (abelian₂ P.A P.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (n : ℕ) (T : Over S) (x y : T ⟶ P'.A), x ^ n = 1 → y ^ n = 1 → ∀ (c : Fin 8 → Fin 8 → Γ(T.left, ⊤)ˣ), (∀ a b, WeilIs P.A P.L n (x ≫ pr a) (y ≫ pr b) (c a b)) → WeilIs P'.A P'.L n x y (∏ ab : Fin 8 × Fin 8, (c ab.1 ab.2 * c ab.2 ab.1) ^ W ab.1 ab.2) := by
  intro S _ P P' pr hpr W hL n T x y hx hy c hc
  have hG := GlobalTheory.globalFns_holds
  have hΛ : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  have hM := LB.isLB_linComb hΛ (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
    (fun ab => W ab.1 ab.2)
  have hφ : ∀ ab : Fin 8 × Fin 8, IsMonHom (lift (pr ab.1) (pr ab.2)) := fun ab => by
    haveI := hpr ab.1
    haveI := hpr ab.2
    infer_instance
  have ht : ∀ {z : T ⟶ P'.A}, z ^ n = 1 → ∀ a, (z ≫ pr a) ^ n = 1 := fun {z} hz a => by
    haveI := hpr a
    rw [← MonObj.pow_comp, hz, MonObj.one_comp]
  have key := GlobalTheory.PairingComb.weilIs_linComb hG P'.isAb hΛ (fun ab : Fin 8 × Fin 8 => lift (pr ab.1) (pr ab.2)) hφ
    (fun ab => W ab.1 ab.2) (n := n) (x := x) (y := y) (fun ab => c ab.1 ab.2 * c ab.2 ab.1) (fun ab => by
      rw [comp_lift, comp_lift]
      exact GlobalTheory.T.weilPairing_mumfordLambda_square S P n T _ _ _ _ (ht hx _) (ht hx _) (ht hy _) (ht hy _) _ _ (hc ab.1 ab.2) (hc ab.2 ab.1))
  refine GlobalTheory.PELFamily.weilIs_of_lbIso hG P'.isAb P'.isLB hM ?_ key
  refine LBIso.trans P'.isLB hM (LB.isLB_pull hM _) hL ?_
  have := GlobalTheory.DescendedPrincipal.lbIso_pull_id hM
  simpa using this.symm

theorem sum_symmetrised_bilinear_matrix_eq {J X Y : Type} [Fintype J] [AddCommGroup X] [AddCommGroup Y] (W : Matrix J J ℤ) (c : J → (X →+ Y))
    (l : J → X) :
    ∑ ab : J × J, W ab.1 ab.2 • (c ab.1 (l ab.2) + c ab.2 (l ab.1)) =
      ∑ u, c u (∑ w, (W + W.transpose) u w • l w) := by
  rw [Fintype.sum_prod_type]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [smul_add, Finset.sum_add_distrib, map_add (f := _), map_sum, map_zsmul, Matrix.add_apply, Matrix.transpose_apply,
    add_smul]
  congr 1
  exact Finset.sum_comm

theorem label_proj_eq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ v : Fin 8, (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), IsUnit (k : R) → ∀ (q : QkPt D.toPre F k) (q' : QkPt D'.toPre F k) (a : TFK (R := R) F ⟶ A.A) (a' : TFK (R := R) F ⟶ A'.A), QkToAkU U.toUnifPre F k q a → QkToAkU U'.toUnifPre F k q' a' → a.left ≫ genMap U = a'.left ≫ genMap U' ≫ (pG v).left → ∃ z, q.y = e q'.y v + k • z) := by
  intro R _ _ _ hRb hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr huniv hL pG hpG hgen c hc e he v F _ _ _ k hk
    q q' a a' hqa hqa' hla
  haveI := hdvr
  obtain ⟨hR, hR0⟩ := id hRb
  obtain ⟨-, -, -, hRc⟩ := id hR
  haveI := hRc
  haveI := hR0
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
  have hkF : (k : F) ≠ 0 := by
    have h := hk.map ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))
    rw [map_natCast] at h
    exact h.ne_zero
  obtain ⟨f, ⟨i₁, s₁, q₁, -, w₁⟩, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR D A G hG U F k hk1
  obtain ⟨f', ⟨i₂, -, -, -, w₂⟩, p₂⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR D' A' G' hG' U' F k hk1
  obtain rfl : a = f q := (i₁ q a).1 hqa
  obtain rfl : a' = f' q' := (i₂ q' a').1 hqa'
  have hav : f q = f' q' ≫ pr v := eq_comp_of_genMap U U' (pG v) (pr v) (hgen v) _ _ hla
  have hpw : ∀ w, (f' q' ≫ pr w) ^ k = 1 := fun w => by
    haveI := hpr w
    rw [← MonObj.pow_comp, p₂, MonObj.one_comp]
  choose qw hqw using fun w => s₁ _ (hpw w)
  have key : ∀ τ : Multiplicative D.toPre.X →* Fˣ, τ ^ k = 1 →
      τ (Multiplicative.ofAdd (q.y - e q'.y v)) = 1 := by
    intro τ hτ
    have hτk : ∀ x, τ x ^ k = 1 := fun x => by
      rw [← MonoidHom.pow_apply, hτ, MonoidHom.one_apply]
    let ev : D'.toPre.X →+ D.toPre.X := (Pi.evalAddMonoidHom (fun _ : Fin 8 => D.toPre.X) v).comp e.toAddMonoidHom
    let τ' : Multiplicative D'.toPre.X →* Fˣ := τ.comp (AddMonoidHom.toMultiplicative ev)
    have hτ' : τ' ^ k = 1 := MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.one_apply]
      exact hτk _
    let τu : Fin 8 → (Multiplicative D.toPre.X →* Fˣ) := fun u => τ'.comp (AddMonoidHom.toMultiplicative (c u))
    have hτu : ∀ u, τu u ^ k = 1 := fun u => MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.one_apply]
      exact hτk _
    obtain ⟨tT', htT'y, htT'⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor (F := F) hB' τ' hτ'
    choose tT htTy htT using fun u => GlobalTheory.ZH.TorusPerp.exists_qkPt_tor (F := F) hB (τu u) (hτu u)
    have hproj : ∀ u, f (tT u) = f' tT' ≫ pr u := fun u =>
      eq_comp_of_genMap U U' (pG u) (pr u) (hgen u) _ _
        (hc u F (fun _ => rfl) k hk (τu u) τ' (tT u) tT' (f (tT u)) (f' tT') hτ' (fun _ => rfl) (htTy u) (htT u)
          htT'y htT' ((i₁ _ _).2 rfl) ((i₂ _ _).2 rfl))
    have hA : ∀ u w, WeilIs A.A A.L k (f' tT' ≫ pr u) (f' q' ≫ pr w)
        (unitOn (τ' (Multiplicative.ofAdd (c u (qw w).y)))) := fun u w => by
      rw [← hproj u, ← hqw w]
      exact (w₁ _ _ _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns (tT u) (qw w) (htTy u) (htT u))
    have hA' : WeilIs A'.A A'.L k (f' tT') (f' q') (unitOn (τ' (Multiplicative.ofAdd q'.y))) :=
      (w₂ _ _ _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns tT' q' htT'y htT')
    have hA₂ := commutatorPairing_eighthPower_bundle _ A A' pr hpr W hL k _ (f' tT') (f' q') (p₂ _) (p₂ _) _ hA
    have hval : (∏ ab : Fin 8 × Fin 8, (unitOn (τ' (Multiplicative.ofAdd (c ab.1 (qw ab.2).y))) *
        unitOn (τ' (Multiplicative.ofAdd (c ab.2 (qw ab.1).y)))) ^ W ab.1 ab.2) =
        unitOn (τ' (Multiplicative.ofAdd (∑ u, c u (∑ w, (W + W.transpose) u w • (qw w).y)))) := by
      let ψ : Multiplicative D'.toPre.X →* Γ(Sp F, ⊤)ˣ :=
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom).comp τ'
      have hψ : ∀ x, unitOn (τ' x) = ψ x := fun x => rfl
      simp only [hψ]
      rw [← sum_symmetrised_bilinear_matrix_eq W c (fun w => (qw w).y), ofAdd_sum, map_prod]
      refine Finset.prod_congr rfl fun ab _ => ?_
      rw [ofAdd_zsmul, map_zpow, ofAdd_add, map_mul]
    rw [hval] at hA₂
    have hu := GlobalTheory.weilIs_unique_fieldPoint _ A'.A A'.L A'.isLB F _ k _ _ _ _ hA' hA₂
    have hinv : e (∑ u, c u (∑ w, (W + W.transpose) u w • (qw w).y)) = fun w => (qw w).y := by
      have := he (e.symm fun w => (qw w).y)
      rw [e.apply_symm_apply] at this
      rw [this, e.apply_symm_apply]
    have h₁ : τ (Multiplicative.ofAdd (e q'.y v)) = τ (Multiplicative.ofAdd (qw v).y) := by
      have := hu
      simp only [τ', ev, MonoidHom.comp_apply, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd,
        AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply, AddEquiv.coe_toAddMonoidHom, hinv] at this
      exact this
    obtain ⟨z, hz, -⟩ := (q₁ (qw v) q).1 (by rw [hqw, hav])
    rw [ofAdd_sub, map_div, h₁, hz, ofAdd_add, map_mul, ofAdd_nsmul, map_pow, hτk, _root_.mul_one, div_self']
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_eq_nsmul_of_forall_char_pow_eq_one _ F k hkF _ key
  exact ⟨z, by rw [← hz]; abel⟩

end GlobalTheory.Poinc.Eq8.Labels
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsPullbackUniformisationCommonField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.ArcPull

namespace GlobalTheory.Poinc.Sep.BaseChangeLabels

theorem qkToAkU_pullback_common_field : ∀ {V V' : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'], IsCN V → IsCN V' → ∀ (j : V →+* V') (hj : Function.Injective j), IsLocalHom j → ∀ {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (D' : DegData V' (maximalIdeal V')) (hD : IsPullDeg j D.toPre D'.toPre) (A' : PolAV (Spec (CommRingCat.of (FractionRing V')))) (gA : A'.A.left ⟶ A.A.left) (U' : Unif (maximalIdeal V') D' A' ((Over.pullback (specOf j)).obj G)), IsPullUnif j hD (Iso.refl _) U U' → IsGrpPullback A'.A A.A (spMap (fracMap hj)) gA → gA ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) = U'.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf j)).obj G).hom (jK V') ≫ pullback.fst G.hom (specOf j) → ∀ (F' : Type) [Field F'] [Algebra (FractionRing V) F'] [Algebra (FractionRing V') F'], (∀ r : V, algebraMap (FractionRing V) F' (algebraMap V (FractionRing V) r) = algebraMap (FractionRing V') F' (algebraMap V' (FractionRing V') (j r))) → ∀ (k : ℕ), 1 ≤ k → ∀ (p₁ : QkPt D.toPre F' k) (x₁ : TFK (R := V) F' ⟶ A.A), QkToAkU U.toUnifPre F' k p₁ x₁ → ∃ (p' : QkPt D'.toPre F' k) (x' : TFK (R := V') F' ⟶ A'.A), p'.y = hD.xe.symm p₁.y ∧ QkToAkU U'.toUnifPre F' k p' x' ∧ x'.left ≫ gA = x₁.left := by
  intro V V' _ _ _ _ _ _ hV hV' j hj _ D A G _ _ _ U D' hD A' gA U' hPU hgU hgA F' _ _ _ hF k hk p₁ x₁ hQ

  have hcomp : algebraMap (FractionRing V) F' = (algebraMap (FractionRing V') F').comp (fracMap hj) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors V)
    ext r
    simp only [RingHom.comp_apply, fracMap_algebraMap]
    exact hF r

  have P := GlobalTheory.UT.EndBaseChange.points GlobalTheory.firstFiveLaws.1.globalFns hD D.tau_bimult D'.tau_bimult F' hF
  obtain ⟨g', hg', -⟩ := P.1 p₁.g
  obtain ⟨h, hn, hi⟩ := p₁.eq
  obtain ⟨h', hh', -⟩ := P.1 h
  have hn' := (P.2.2.2 k p₁.g g' h h' hg' hh').1 hn
  have hi' : GtPtF.IsIota (hD.xe.symm p₁.y) h' := (P.2.2.1 h h' (hD.xe.symm p₁.y) hh').1 (by simpa using hi)
  let p' : QkPt D'.toPre F' k := ⟨hD.xe.symm p₁.y, g', ⟨h', hn', hi'⟩⟩

  have sq : x₁.left ≫ A.A.hom = (TFK (R := V') F').hom ≫ spMap (fracMap hj) := by
    rw [Over.w x₁]
    show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) F')) =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V') F')) ≫ Spec.map (CommRingCat.ofHom (fracMap hj))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  let l := hgU.1.lift x₁.left (TFK (R := V') F').hom sq
  have hl₁ : l ≫ gA = x₁.left := hgU.1.lift_fst _ _ sq
  have hl₂ : l ≫ A'.A.hom = (TFK (R := V') F').hom := hgU.1.lift_snd _ _ sq
  let x' : TFK (R := V') F' ⟶ A'.A := Over.homMk l hl₂
  have hx' : x'.left ≫ gA = x₁.left := hl₁

  have hA : AdmBase V (maximalIdeal V) := ⟨hV.1, inferInstance, hV.2.1, hV.2.2.1⟩
  have hA' : AdmBase V' (maximalIdeal V') := ⟨hV'.1, inferInstance, hV'.2.1, hV'.2.2.1⟩
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf j)).obj G)).hom := by
    show IsMonHom (𝟙 _); infer_instance
  refine ⟨p', x', rfl, ?_, hx'⟩
  refine GlobalTheory.firstFiveLaws.2.2.2.2.qkBaseChange V V' (maximalIdeal V) (maximalIdeal V') hA hA' j D A G U
    ((Over.pullback (specOf j)).obj G) (Iso.refl _) mR A' D' hD U' hPU F' hF k hk p₁ x₁ p' x' rfl hg' ?_ hQ
  rw [Iso.refl_hom, Over.id_left, Category.id_comp, ← hx', Category.assoc, hgA]

end GlobalTheory.Poinc.Sep.BaseChangeLabels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBundleRigidLinearisationsSameLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationBundle_rigidLinearisations_same_localUnits : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (D' : DegData R' (maximalIdeal R')) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (s : Sp R' ⟶ Sp R') (f₁ f₂ : G'.left ⟶ G'.left), f₁ = f₂ → ∀ (he₁ : eSec G' ≫ f₁ = s ≫ eSec G') (he₂ : eSec G' ≫ f₂ = s ≫ eSec G') (w₁ : LB.Iso U'.LG.L (U'.LG.L.pull f₁)) (w₂ : LB.Iso U'.LG.L (U'.LG.L.pull f₂)), w₁.IsGen → w₂.IsGen → LB.Gen.Maps (LB.linCombIso w₁ (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig (rigPullOf f₁ s he₁ U'.LG.L U'.LG.rig) → LB.Gen.Maps (LB.linCombIso w₂ (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig (rigPullOf f₂ s he₂ U'.LG.L U'.LG.rig) → ∀ (z : G'.left) (j k : U'.LG.L.ι), z ∈ U'.LG.L.U k → f₁ z ∈ U'.LG.L.U j → gw w₁ (𝟙 G'.left) z j k = gw w₂ (𝟙 G'.left) z j k := by
  first | exact @GlobalTheory.Mum.RigLinUnique.gw_eq_of_rigidified | exact GlobalTheory.Mum.RigLinUnique.gw_eq_of_rigidified | (intros; apply GlobalTheory.Mum.RigLinUnique.gw_eq_of_rigidified <;> assumption)
end

