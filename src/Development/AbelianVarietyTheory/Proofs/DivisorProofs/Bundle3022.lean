module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIsoCarriesSharpPointsToConjugates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2980
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2166
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2407
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2978
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCoverByPolarizationPowerSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRelationZeroDerivationOfShifted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2999
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2923

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSquareProductIsFunctionOnSpec
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

namespace GlobalTheory.IntPointFnSq

theorem c_comp_inv (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (χ : D.X) :
    (D.c χ).left ≫ (ι[D.P.A]).left = (D.c (-χ)).left := by
  rw [← Over.comp_left]
  congr 1
  have h : D.c χ * D.c (-χ) = 1 := by
    rw [← GlobalTheory.Poinc.ThetaOne.c_zero D, ← add_neg_cancel χ, D.c_add]; rfl
  exact (eq_inv_of_mul_eq_one_right h).symm

theorem c_eq_eta (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (χ : D.X) :
    (D.c (χ + -χ)).left = (η[D.P.A]).left := by
  rw [add_neg_cancel, GlobalTheory.Poinc.ThetaOne.c_zero, ← SymFrame.eta_eq]


open GlobalTheory.IntPointFn in
theorem fn_of_theta_sq : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V)
    (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) (χ : D.X)
    (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen →
    ∀ (χt : LB.Gen (LB.LinComb D.P.L ![(D.c χ * b).left, (D.c χ).left, b.left, (η[D.P.A]).left] DegPre.gtε)),
    χt.IsGen →
    ∀ (τ : LB.Gen (LB.LinComb D.P.L (K := Fin 4) ![(D.c (χ + -χ)).left, (D.c χ).left, (D.c (-χ)).left, (D.c 0).left]
      ![-1, 1, 1, -1])), τ.IsGen →
    ∃ G : V, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) J, Good D.P.L z J →
      gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom G) =
        sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b * D.c χ).left) z J ^ 2 *
          (val t r z J ^ 2 * val χt r z J ^ 2 * val D.sym (r ≫ (D.c χ).left) z J *
            (val τ r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹).val := by
  intro V _ _ D θ b χ t ht χt hχt τ hτ
  have hL := D.P.isLB
  have e0 : (D.c 0).left = (η[D.P.A]).left := by rw [GlobalTheory.Poinc.ThetaOne.c_zero, ← SymFrame.eta_eq]
  have e1 := c_comp_inv V D χ
  have e2 := c_eq_eta V D χ
  have e4 : (b * D.c χ).left = (D.c χ * b).left := by rw [_root_.mul_comm]
  let u := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ t t) (LB.mulGen D.P.L _ _ _ _ χt χt))
    (LB.pullGen D.P.L _ _ D.sym (D.c χ).left)) (LB.invGen D.P.L _ _ τ))
    (LB.invGen D.P.L _ _ (LB.mulGen D.P.L (Y := Sp V) (fun _ : PUnit => eSec D.P.A) (fun _ => 1) (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.rig))
  have hu : u.IsGen := by
    refine mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
      (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ ht ht) (mulGen_isGen _ _ _ _ _ _ _ hχt hχt))
      (pullGen_isGen _ _ _ _ D.sym_gen _)) (invGen_isGen _ _ _ _ hτ))
      (invGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ D.rig_gen D.rig_gen))
  obtain ⟨s', hs'⟩ := GlobalTheory.Poinc.Sep.ConjPt.exists_powSec hL (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (b * D.c χ).left 2 u hu (K' := PEmpty) PEmpty.elim PEmpty.elim (fun U _ f => by
      simp only [u, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, Fin.prod_univ_two,
        Fintype.prod_empty, Fintype.prod_unique, DegPre.famφB, DegPre.famε, DegPre.lineε, DegPre.gtε,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons, Category.comp_id, Nat.cast_one, sub_self,
        comp_padd_c_zero, comp_toUnit_c_zero, comp_toUnit_eta, eSec, e0, e1, e2, e4]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      abel)
  obtain ⟨a, ha⟩ := GlobalTheory.Poinc.Sep.ConjPt.exists_fn s'
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom a, fun Z r z J hJ => ?_⟩
  have e2' : (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom a) = a := by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  rw [e2', ← ha, hs' Z r z J hJ]
  congr 1
  simp only [u, val_mul hJ, val_inv, val_pull hJ, rigV]
  simp only [pow_two]

end GlobalTheory.IntPointFnSq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsDefinedOverSubfieldAbelianModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.USep

theorem points_defOver : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ D.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (D.P.L.pull π₁) (M₀.pull π₀)), IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback B' D.P.A (spMap ev) π₁ → IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ → w.IsGen → ∀ (a : D.X) (x : Sp K ⟶ B'.left), x ≫ B'.hom = 𝟙 _ → x ≫ π₁ = spMap ev ≫ (D.c a).left → GlobalTheory.Poinc.Sep.DefOver k₀ (x ≫ π₀) := by
  intro g n hn hodd
  obtain ⟨j₁, hC⟩ := _root_.GlobalTheory.USep.coords_scalar_mul_rational g n hn hodd
  refine ⟨max j₁ 1, ?_⟩
  intro j hj V₁ _ _ _ hCN hunit D hg X C _ e u mo hmo hT K _ _ ev k₀ hk₀ hrat B₀ _ _ M₀ B' _ π₁ π₀ w hB₀ hM₀ h₁ h₀ hw a x hx hxa
  have hj₁ : j₁ ≤ j := le_trans (le_max_left _ _) hj
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hmodd : Odd (n ^ j) := hodd.pow
  have hn3 : 3 ≤ n := by
    have h2 := hn.two_le
    rcases Nat.lt_or_ge n 3 with h | h
    · have : n = 2 := by omega
      subst this; exact absurd hodd (by decide)
    · exact h
  have hm3 : 3 ≤ n ^ j := le_trans hn3 (by
    calc n = n ^ 1 := (pow_one n).symm
      _ ≤ n ^ j := Nat.pow_le_pow_right hn.pos hj1)
  have hmK : ((n ^ j : ℕ) : K) ≠ 0 := by
    have h := (hunit (n ^ j) (by positivity)).map ev
    rw [map_natCast] at h
    exact h.ne_zero
  haveI : IsNoetherianRing V₁ := hCN.1
  haveI : IsCommMonObj D.P.A := D.P.isAb.comm
  haveI : IsCommMonObj B' := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback h₁
  let P' : PolAV (Sp K) :=
    { A := B'
      isAb :=
        { comm := inferInstance
          smooth := MorphismProperty.of_isPullback (P := @Smooth) h₁.1 D.P.isAb.smooth
          proper := MorphismProperty.of_isPullback (P := @IsProper) h₁.1 D.P.isAb.proper
          geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h₁.1 D.P.isAb.geomConnected }
      g := D.P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h₁.1 D.P.smoothDim
      L := D.P.L.pull π₁
      isLB := pull_isLB D.P.isLB _
      rigid := GlobalTheory.PolBaseChange.rigidified_pull h₁ D.P.rigid
      sym := GlobalTheory.PolBaseChange.sym_pull h₁ D.P.sym
      ample := by
        haveI := D.P.isAb.proper
        exact GlobalTheory.AmpleBaseChange.relAmple_of_isPullback D.P.isLB D.P.ample h₁.1
      ktriv := kTriv_pull h₁ D.P.isLB (pull_isLB D.P.isLB _)
        ((isGen_iff _).1 (GlobalTheory.TorsionTauCompare.isGen_refl (pull_isLB D.P.isLB π₁))) D.P.ktriv }
  have hw' : LBIso P'.L (M₀.pull π₀) := ⟨w, hw⟩
  have hSym : Out.Sym B₀ M₀ := (GlobalTheory.PolDescent.rigidified_sym_kTriv_descend k₀ K k₀.subtype B₀ B' π₀ M₀ P'.L hB₀ h₀
    hM₀ P'.isLB hw').2.1 P'.sym
  have h₀' : IsGrpPullback P'.A B₀ (spMap (algebraMap k₀ K)) π₀ := h₀
  set_option synthInstance.maxHeartbeats 400000 in
  have : Flat (spMap k₀.subtype) := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  let P₀ : PolAV (Sp k₀) :=
    { A := B₀, isAb := hB₀, g := P'.g,
      smoothDim := GlobalTheory.CM.smoothOfRelativeDimension_of_fibre k₀ K k₀.subtype B₀ P'.A.left π₀ P'.A.hom P'.g hB₀ h₀.1
        P'.smoothDim,
      L := M₀, isLB := hM₀, rigid := ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local M₀ hM₀ _ _, sym := hSym,
      ample := GlobalTheory.AmpleDescent.relAmple_of_faithfullyFlat k₀ K B₀ P'.A π₀ M₀ P'.L hB₀ h₀' hM₀ P'.isLB hw' P'.ample,
      ktriv := GlobalTheory.AmpleDescent.kTriv_of_pull h₀ hM₀ P'.isLB hw' P'.ktriv }
  obtain ⟨Φ₀, hΦ₀⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback (G := B₀) (G' := B') h₀
    (𝟙 (Sp K)) (spMap k₀.subtype) (Category.id_comp _)
  obtain ⟨Φ₁, hΦ₁⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback (G := D.P.A) (G' := B') h₁
    (𝟙 (Sp K)) (spMap ev) (Category.id_comp _)
  let t₀ : Sp K ⟶ Sp k₀ := spMap k₀.subtype
  let t₁ : Sp K ⟶ Sp V₁ := spMap ev
  let Ix := {y : Over.mk t₀ ⟶ B₀ // y ^ (n ^ j) ^ 2 = 1}
  let X' : Ix → (baseOver (Sp K) ⟶ B') := fun i => Φ₀.symm i.1
  have hX' : ∀ i, X' i ^ (n ^ j) ^ 2 = 1 := fun i => Φ₀.injective (by
    rw [map_pow, MulEquiv.apply_symm_apply, i.2, map_one])
  let z' : baseOver (Sp K) ⟶ B' := Over.homMk x hx
  let yD : Ix → (Over.mk t₁ ⟶ D.P.A) := fun i => Φ₁ (X' i)
  have hyD : ∀ i, yD i ^ (n ^ j) ^ 2 = 1 := fun i => by
    simp only [yD]; rw [← map_pow, hX' i, map_one]
  have hzD : (Φ₁ z').left = t₁ ≫ (D.c a).left := by
    rw [hΦ₁]; simp [t₁, z', hxa]
  obtain ⟨vD, l, r, hvD, hr, hvr⟩ := hC j hj₁ V₁ hCN hunit D hg X C e u mo hmo hT K ev k₀ hk₀ hrat
    Ix yD hyD a (Φ₁ z') hzD
  have HD := GlobalTheory.FullExtend.isCoordPt_move (f := spMap ev) (T := baseOver (Sp K)) (T₀ := Over.mk t₁) (𝟙 _)
    (P₀ := D.P) (P := P') (φ := π₁) h₁ (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB D.P.isLB π₁)) (B := Over.mk t₁)
    (𝟙 _) (𝟙 _) (by simp) (by simp [t₁])
    (fun th₀ h => GlobalTheory.ThetaCoord.isGenSec_pullS D.P.isLB (𝟙 _) (𝟙 _) (by simp) h) (x := X') (x₀ := yD)
    (fun i => (Category.id_comp _).trans (hΦ₁ _)) hX' (z := z') (z₀ := Φ₁ z') ((Category.id_comp _).trans (hΦ₁ z')) hvD
  obtain ⟨v₀, hv₀⟩ := (GlobalTheory.CoordSep.coord_exists_unique_separate GlobalTheory.abelianSchemeLaws_all.1 K (Sp k₀) P₀ t₀ (n ^ j)
    hmodd hmK Ix (fun i => i.1) (fun i => i.2)).1 (Φ₀ z')
  have H0 := GlobalTheory.FullExtend.isCoordPt_move (f := spMap k₀.subtype) (T := baseOver (Sp K)) (T₀ := Over.mk t₀) (𝟙 _)
    (P₀ := P₀) (P := P') (φ := π₀) h₀ hw' (B := Over.mk t₀) (𝟙 _) (𝟙 _) (by simp) (by simp [t₀])
    (fun th₀ h => GlobalTheory.ThetaCoord.isGenSec_pullS hM₀ (𝟙 _) (𝟙 _) (by simp) h) (x := X') (x₀ := fun i => i.1)
    (fun i => (Category.id_comp _).trans ((congrArg Over.Hom.left (Φ₀.apply_symm_apply i.1)).symm.trans (hΦ₀ _)))
    hX' (z := z') (z₀ := Φ₀ z') ((Category.id_comp _).trans (hΦ₀ z')) hv₀
  have HD' : GlobalTheory.Ex.IsCoordPt P' (n ^ j) X' z' (fun i => GlobalTheory.Ex.fnOf (vD i)) := by
    convert HD using 2 with i
    simp
  have H0' : GlobalTheory.Ex.IsCoordPt P' (n ^ j) X' z' (fun i => GlobalTheory.Ex.fnOf (v₀ i)) := by
    convert H0 using 2 with i
    simp
  obtain ⟨-, U₂, -, -⟩ := GlobalTheory.CoordSep.coord_exists_unique_separate GlobalTheory.abelianSchemeLaws_all.1 K (Sp K) P' (𝟙 _)
    (n ^ j) hmodd hmK Ix X' hX'
  obtain ⟨c, hc⟩ := (U₂ z' v₀ vD H0').1 HD'
  have hv₀r : ∀ i, v₀ i = ((c⁻¹ : Kˣ) * l) * r i := fun i => by
    have := congrFun hc i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [_root_.mul_assoc, ← hvr i, this, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  have hD := _root_.GlobalTheory.Poinc.Sep.defOver_of_coord_proportional K k₀ hk₀ P₀ (n ^ j) hmodd hm3 hmK (Φ₀ z') v₀ _ r hv₀ hr hv₀r
  rwa [hΦ₀] at hD

end GlobalTheory.USep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsProjectionsDefinedOverSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

namespace GlobalTheory.USep.EvG

theorem points_defOver : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (N : ℕ), 1 ≤ N → ∀ (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A), b ^ N = 1 → ∀ a : D.X,
      DefOver k₀ (spMap ev ≫ b.left ≫ β) ∧ DefOver k₀ (spMap ev ≫ (D.c a).left ≫ β) ∧
        DefOver k₀ (spMap ev ≫ (b * D.c a).left ≫ β) ∧ DefOver k₀ (spMap ev ≫ (D.c a * b).left ≫ β) := by
  intro V₁ _ _ _ hV hunit D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hF K _ _ ev k₀ hk₀ hk N hN b hb a
  classical
  obtain ⟨-, -, hβ, -, hc, -, -⟩ := hF
  haveI : IsNoetherianRing V₁ := hV.1
  have hg : spMap ev ≫ spMap ib = spMap (ev.comp ib) := by
    simp only [spMap, ← Spec.map_comp]; rfl
  obtain ⟨Φ, hΦ⟩ :=
    GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hβ (spMap ev) (spMap (ev.comp ib)) hg

  have htor : ∀ x : Over.mk (spMap ev) ⟶ D.P.A, x ^ N = 1 → DefOver k₀ (x.left ≫ β) := by
    intro x hx
    have hNK : (N : K) ≠ 0 := by
      have := ((hunit N (by omega)).map ev).ne_zero
      simpa using this
    have hcard := (GlobalTheory.abelianSchemeLaws_all.1.mulN (Sp V₁) D.P N hN).2.2.2.2 K (spMap ev) hNK
    have hfin : Finite {y : Over.mk (spMap ev) ⟶ D.P.A // y ^ N = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))
    refine defOver_of_finite_orbit K k₀ hk₀ _ _ ((Set.finite_range
      fun y : {y : Over.mk (spMap ev) ⟶ D.P.A // y ^ N = 1} => (Φ y.1).left).subset ?_)
    rintro _ ⟨σ, hσ, rfl⟩
    have hσf : spMap σ.toRingHom ≫ spMap (ev.comp ib) = spMap (ev.comp ib) := by
      have e1 : (σ.toRingHom).comp (ev.comp ib) = ev.comp ib := RingHom.ext fun u => hσ _ (hk u)
      have e0 : spMap σ.toRingHom ≫ spMap (ev.comp ib) = spMap ((σ.toRingHom).comp (ev.comp ib)) := by
        simp only [spMap, ← Spec.map_comp]; rfl
      rw [e0, e1]
    let hh : Over.mk (spMap (ev.comp ib)) ⟶ Over.mk (spMap (ev.comp ib)) := Over.homMk (spMap σ.toRingHom) hσf
    refine ⟨⟨Φ.symm (hh ≫ Φ x), ?_⟩, ?_⟩
    · rw [← map_pow, ← MonObj.comp_pow, ← map_pow, hx, map_one, MonObj.comp_one, map_one]
    · show (Φ (Φ.symm (hh ≫ Φ x))).left = _
      rw [MulEquiv.apply_symm_apply, Over.comp_left, hΦ]
      rfl

  have hsub : spMap k₀.subtype ≫ spMap ((ev.comp ib).codRestrict k₀ hk) = spMap (ev.comp ib) := by
    simp only [spMap, ← Spec.map_comp]; rfl
  let j : Over.mk (spMap (ev.comp ib)) ⟶ Over.mk (spMap ((ev.comp ib).codRestrict k₀ hk)) :=
    Over.homMk (spMap k₀.subtype) hsub
  have hdesc : ∀ p : Over.mk (spMap (ev.comp ib)) ⟶ B₀, DefOver k₀ p.left →
      ∃ p₀ : Over.mk (spMap ((ev.comp ib).codRestrict k₀ hk)) ⟶ B₀, j ≫ p₀ = p := by
    intro p ⟨P₀, hP₀⟩
    have e : P₀ ≫ B₀.hom = spMap ((ev.comp ib).codRestrict k₀ hk) := spMap_subtype_cancel k₀ (by
      rw [← Category.assoc, hP₀, Over.w p, hsub]; rfl)
    exact ⟨Over.homMk P₀ e, Over.OverMorphism.ext hP₀⟩
  have hmul : ∀ p q : Over.mk (spMap (ev.comp ib)) ⟶ B₀, DefOver k₀ p.left → DefOver k₀ q.left →
      DefOver k₀ (p * q).left := by
    intro p q hp hq
    obtain ⟨p₀, rfl⟩ := hdesc p hp
    obtain ⟨q₀, rfl⟩ := hdesc q hq
    rw [← MonObj.comp_mul]
    exact ⟨(p₀ * q₀).left, rfl⟩
  have hprod : ∀ y z : Over.mk (spMap ev) ⟶ D.P.A, DefOver k₀ (y.left ≫ β) → DefOver k₀ (z.left ≫ β) →
      DefOver k₀ ((y * z).left ≫ β) := by
    intro y z hy hz
    rw [← hΦ, map_mul]
    exact hmul _ _ (by rw [hΦ]; exact hy) (by rw [hΦ]; exact hz)

  let h : Over.mk (spMap ev) ⟶ 𝟙_ (Over (Sp V₁)) := Over.homMk (spMap ev) (Category.comp_id _)
  have hl : ∀ y : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A, spMap ev ≫ y.left ≫ β = (h ≫ y).left ≫ β := by
    intro y
    rw [Over.comp_left, Category.assoc]
    rfl
  have h1 : DefOver k₀ (spMap ev ≫ b.left ≫ β) := by
    rw [hl]
    exact htor _ (by rw [← MonObj.comp_pow, hb, MonObj.comp_one])
  have h2 : DefOver k₀ (spMap ev ≫ (D.c a).left ≫ β) := by
    have e : spMap ev ≫ (D.c a).left ≫ β = spMap (ev.comp ib) ≫ c₀ a := by
      rw [show (D.c a).left ≫ β = spMap ib ≫ c₀ a from hc a, ← Category.assoc, hg]
    rw [e]
    exact defOver_comp k₀ (defOver_spMap k₀ _ hk) _
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [hl, MonObj.comp_mul]
    exact hprod _ _ (by rw [← hl]; exact h1) (by rw [← hl]; exact h2)
  · rw [hl, MonObj.comp_mul]
    exact hprod _ _ (by rw [← hl]; exact h2) (by rw [← hl]; exact h1)

end GlobalTheory.USep.EvG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSectionsExhaustOfGenericGeometric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntTerm

theorem tf_apply_eq_genericPoint {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F]
    [Algebra (FractionRing R) F] (a : Sp F) : (TF (R := R) F).hom a = genericPoint (Sp R) := by
  rw [genericPoint_eq_bot_of_affine]
  have ha : (a : PrimeSpectrum F).asIdeal = ⊥ :=
    @Ideal.eq_bot_of_prime _ _ _ (a : PrimeSpectrum F).isPrime
  have hinj : Function.Injective ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) :=
    (algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R (FractionRing R))
  apply PrimeSpectrum.ext
  show Ideal.comap _ (Ideal.comap _ (a : PrimeSpectrum F).asIdeal) = ⊥
  rw [ha, Ideal.comap_comap]
  exact Ideal.comap_bot_of_injective _ hinj

theorem exists_eq_section_of_finite_flat {R : Type} [CommRing R] [IsDomain R] (T : Over (Sp R))
    [IsFinite T.hom] [Flat T.hom] {C : Type} (σ : C → (𝟙_ (Over (Sp R)) ⟶ T))
    (H : ∀ t : TF (R := R) (AlgebraicClosure (FractionRing R)) ⟶ T, ∃ c, t = toUnit _ ≫ σ c)
    (K : Type) [Field K] (x : Sp K ⟶ Sp R) (p : Over.mk x ⟶ T) : ∃ c, p = toUnit _ ≫ σ c := by
  set Kb := AlgebraicClosure (FractionRing R)
  set q := p.left (IsLocalRing.closedPoint K) with hqdef
  obtain ⟨q', hq'q, hq'⟩ := Flat.generalizingMap T.hom (genericPoint_specializes (T.hom q))
  let j : Sp Kb ⟶ Sp R := (TF (R := R) Kb).hom
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := T.hom) (g := j) q'
    (IsLocalRing.closedPoint Kb) (by rw [hq']; exact (tf_apply_eq_genericPoint (R := R) Kb _).symm)
  have : LocallyOfFiniteType (pullback.snd T.hom j) := inferInstance
  have : IsIntegralHom (pullback.snd T.hom j) := inferInstance
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd T.hom j)
  obtain ⟨c, hcz, hcc⟩ := nonempty_inter_closedPoints (X := (pullback T.hom j : Scheme))
    (Z := closure {z}) ⟨z, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  have hzc : z = c := GlobalTheory.eq_of_specializes_of_isIntegralHom (pullback.snd T.hom j)
    (specializes_iff_mem_closure.2 hcz) (Subsingleton.elim _ _)
  subst hzc
  let s : Sp Kb ⟶ pullback T.hom j := pointOfClosedPoint (pullback.snd T.hom j) z hcc
  have hs : s ≫ pullback.snd T.hom j = 𝟙 _ := pointOfClosedPoint_comp (pullback.snd T.hom j) z hcc
  have hsz : ∀ a, s a = z := fun a => pointOfClosedPoint_apply (pullback.snd T.hom j) z hcc a
  let t : TF (R := R) Kb ⟶ T := Over.homMk (s ≫ pullback.fst T.hom j) (by
    show (s ≫ pullback.fst T.hom j) ≫ T.hom = j
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp])
  obtain ⟨c0, hc0⟩ := H t
  have hσ : IsClosedImmersion (σ c0).left := by
    have h1 : (σ c0).left ≫ T.hom = 𝟙 _ := Over.w (σ c0)
    have : IsClosedImmersion ((σ c0).left ≫ T.hom) := by rw [h1]; infer_instance
    exact IsClosedImmersion.of_comp (σ c0).left T.hom
  have hq'mem : q' ∈ Set.range (σ c0).left := by
    let pt : Sp Kb := IsLocalRing.closedPoint Kb
    refine ⟨(toUnit (TF (R := R) Kb)).left pt, ?_⟩
    have e1 : t.left pt = q' := by
      show pullback.fst T.hom j (s pt) = q'
      rw [hsz, hz1]
    rw [← e1, hc0]
    rfl
  have hqmem : q ∈ Set.range (σ c0).left :=
    hq'q.mem_closed (σ c0).left.isClosedEmbedding.isClosed_range hq'mem
  have : IsReduced (Sp K) := inferInstance
  obtain ⟨l, hl⟩ := GlobalTheory.AbelianSubgroupFinite.exists_lift_of_range_subset (T := Sp K) p.left (σ c0).left (by
    rintro _ ⟨(a : Sp K), rfl⟩
    rw [Subsingleton.elim a (IsLocalRing.closedPoint K)]
    exact hqmem)
  have hlx : l = x := by
    have h1 : (σ c0).left ≫ T.hom = 𝟙 _ := Over.w (σ c0)
    have h2 : p.left ≫ T.hom = x := Over.w p
    rw [← h2, ← hl, Category.assoc, h1, Category.comp_id]
  refine ⟨c0, Over.OverMorphism.ext ?_⟩
  rw [Over.comp_left, ← hl, hlx]
  congr 1

end GlobalTheory.Poinc.IntTerm

namespace GlobalTheory.Poinc.IntTerm

theorem exhausts_of_generic : ∀ (V : Type) [CommRing V] [IsDomain V] [IsNoetherianRing V]
    (P : PolAV (Sp V)) (N : ℕ), 1 ≤ N → ∀ (C : Type) (b : C → (𝟙_ (Over (Sp V)) ⟶ P.A)),
    (∀ c, b c ^ N = 1) →
    (∀ p : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ P.A, p ^ N = 1 → ∃ c, p = toUnit _ ≫ b c) →
    IntTerm.Exhausts P N b := by
  intro V _ _ _ P N hN C b hb H K _ _ x p hp
  obtain ⟨h1, h2, -⟩ := GlobalTheory.abelianSchemeLaws_all.1.mulN (Sp V) P N hN
  rw [Out.mulA, ← GrpTangent.mulN_eq_pow] at h1 h2
  haveI : IsFinite (torsion P.A N).hom :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GrpTangent.isPullback_torsion P.A N) h1
  haveI : Flat (torsion P.A N).hom :=
    MorphismProperty.of_isPullback (P := @Flat) (GrpTangent.isPullback_torsion P.A N) h2
  haveI : Mono (torsion.ι P.A N) := inferInstanceAs (Mono (pullback.fst _ _))
  obtain ⟨hι, hu⟩ := GlobalTheory.LamF.torsion_universal P.A N
  choose σ hσ using fun c => hu _ (b c) (hb c)
  obtain ⟨t, ht⟩ := hu _ p hp
  obtain ⟨c, hc⟩ := exists_eq_section_of_finite_flat (torsion P.A N) σ (fun t' => by
      obtain ⟨c, hc⟩ := H (t' ≫ torsion.ι P.A N) (by rw [← comp_pow, hι, comp_one])
      exact ⟨c, by rw [← cancel_mono (torsion.ι P.A N), hc, Category.assoc, hσ]⟩) K x t
  exact ⟨c, by rw [← ht, hc, Category.assoc, hσ]⟩

end GlobalTheory.Poinc.IntTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalSecondOrderSymbolVanishesOfPolarisation
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Heat.gc_symbol_vanishes : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (j₀ : P₀.L.ι), ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U j₀ → ∀ (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F), Λᵀ = Λ → (∀ r, δ₀ (ψ r) = 0) → (∀ (k : ℕ), 1 ≤ k → ∀ σ τ : SecM (𝟙 P₀.A.left) P₀.L k, ∃ ρ : SecM (𝟙 P₀.A.left) P₀.L (3 * k), ∀ b c : F, b = valR ξ _ (σ.f fun _ => j₀) → c = valR ξ _ (τ.f fun _ => j₀) → (k : F) * b * (b * δ₀ c - c * δ₀ b) - ∑ a, ∑ e, Λ a e * δ a b * (b * δ e c - c * δ e b) = valR ξ _ (ρ.f fun _ => j₀)) → Λ = 0 := by
  intro K _ _ P₀ n v dd hv F _ ψ ξ hξ hval δ hδ j₀ hj₀ δ₀ Λ hΛ hδ₀ hbr
  obtain ⟨k, I, s, hk, hcov, hai⟩ := _root_.GlobalTheory.AmpleCover.exists_affine_cover_secM K P₀
  have haff : ∀ i, IsAffineOpen (Out.nonzeroLocus (s i)) := fun i => (hai i).1
  have hne := fun i => (hai i).2
  have hloc : ∀ i, ⊤ ≤ ξ ⁻¹ᵁ Out.nonzeroLocus (s i) := fun i =>
    _root_.GlobalTheory.GenPtOpen.top_le_preimage_of_valR_injective K P₀ F ψ ξ hξ hval _ (hne i)
  have hL := fun i => _root_.GlobalTheory.HeatLoc.symb_regular K P₀ n v dd hv F ψ ξ hξ hval δ hδ j₀ hj₀ δ₀ Λ hbr k hk (s i) (hloc i)
  have hreg : ∀ i a e, ∃ h : Γ(P₀.A.left, Out.nonzeroLocus (s i)), valR ξ _ h = Λ a e := fun i =>
    _root_.GlobalTheory.Heat.SymReg.entry_regular K P₀ n v dd hv F ψ ξ hξ hval δ hδ Λ _ (haff i) (hloc i) (hL i).1
  have hc : ∀ a e, ∃ r : K, ψ r = Λ a e := fun a e =>
    _root_.GlobalTheory.HeatConst.const_of_regular_on_cover K P₀ F ψ ξ hξ hval I (fun i => Out.nonzeroLocus (s i)) hcov hloc (Λ a e) (fun i => hreg i a e)
  choose lam hlam using hc
  have hsym : lamᵀ = lam := by
    ext a e
    apply ψ.injective
    show ψ (lam e a) = ψ (lam a e)
    rw [hlam, hlam]
    exact congrFun (congrFun hΛ a) e
  have hks := _root_.GlobalTheory.Heat.ZeroKS.ksRel_zero K P₀ n v dd hv F ψ ξ hξ hval δ hδ j₀ hj₀ δ₀ lam hsym hδ₀ k hk I s hcov haff hloc
    (fun i f => by
      obtain ⟨f', hf'⟩ := (hL i).2 f
      exact ⟨f', by rw [hf']; simp only [hlam]⟩)
  have h0 := _root_.GlobalTheory.KSZeroDer.main K P₀ n v dd hv lam hks
  ext a e
  rw [← hlam a e, h0]
  simp
end

