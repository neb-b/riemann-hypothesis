module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionCommutesPullbackCmEndoFourLe
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullExpansion

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem sval_eq_mul_of_id {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (a b : LB.Sec (LB.LinComb L φ ε)) (c : Γ(Y, ⊤))
    (h : ∀ y J, Good L y J → sval a (𝟙 Y) y J = gs (𝟙 Y) y ⊤ c * sval b (𝟙 Y) y J)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (J) (hJ : Good L z J) :
    sval a r z J = gs r z ⊤ c * sval b r z J := by
  have key : ∀ j : K → L.ι, a.f j =
      (Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c * (show Γ(Y, LB.wchart L φ j) from b.f j) := fun j =>
    fn_ext (V := LB.wchart L φ j) fun y hy => by
      choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
      have hI' : Good L y I := hI
      refine Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 Y) y le_top hy c)
        (sec_trans b (𝟙 Y) y hy (hI'.mem φ (𝟙 Y))))).symm
      refine (sec_trans a (𝟙 Y) y hy (hI'.mem φ (𝟙 Y))).trans ?_
      exact (congrArg _ (h y I hI')).trans (mul_left_comm _ _ _)
  have hm := hJ.mem φ r
  exact (congrArg (gs r z _) (key _)).trans ((gs_mul r z _ hm _ _).trans
    (congrArg (· * sval b r z J) (gs_res r z le_top hm c)))

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

theorem unitK_snd : unitK (G := G) ≫ pullback.snd G.hom (jK V) = 𝟙 _ := pullback.lift_snd _ _ _

theorem unitK_endK (f : G ⟶ G) [IsMonHom f] : unitK (G := G) ≫ endK f = unitK := by
  have he : eSec G ≫ f.left = eSec G := by
    simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
  apply pullback.hom_ext
  · simp only [unitK, endK, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    exact congrArg (jK V ≫ ·) he
  · simp only [unitK, endK, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]

end

theorem expands_pull_of_four_le : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ k : ℕ, 4 ≤ k → ∀ (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k), P.U.Expands k s F → ∀ s' : P.U.SecK (k * N), IsPullByEnd P.U (t.act.act a) k N s s' → ∃ F' : Fam P.D.toPre (FractionRing V) (k * N), P.U.Expands (k * N) s' F' ∧ PullAl P.D (FractionRing V) P.oD a k N F F' := by
  intro hLaws V _ _ _ E _ _ _ H t P a N hN hN0
  letI := H.starRing
  intro k hk s F hs s' hs'
  obtain ⟨uΨ, huΨ, -, -⟩ := P.w0
  have hM : P.D.toPre.P.L.IsLB := P.D.toPre.P.isLB
  have hL : P.U.LG.L.IsLB := P.U.LG.isLB
  have hk1 : 1 ≤ k := by omega
  have hkN : 1 ≤ k * N := Nat.mul_pos hk1 hN0
  choose Fx hFx hFu using (P.U.expand k hk1).1
  choose Fp hFp using fun F : Fam P.D.toPre (FractionRing V) k =>
    exists_pullAl P.D (FractionRing V) hM P.oD H.w0 uΨ huΨ a N hN hN0 k F
      (pullSecs_fe' P.D (FractionRing V) hLaws.globalFns hM P.oD H.w0 P.w0 uΨ huΨ a N hN hN0 k F)
  choose sp hsp _ using (P.U.expand (k * N) hkN).2
  obtain rfl : F = Fx s := hFu s F hs
  refine ⟨Fp (Fx s), ?_, hFp _⟩
  obtain ⟨u, hu, hn, hrel⟩ := hs'
  haveI : IsMonHom (t.act.act a) := t.act.hom a
  have hF : FormEq (fun _ : Fin 1 => gK (G := t.G)) (fun _ => ((k * N : ℕ) : ℤ))
      (Sum.elim (fun _ : Fin 1 => endK (t.act.act a) ≫ gK) ![gK, endK (t.act.act a) ≫ gK])
      (Sum.elim (fun _ : Fin 1 => (k : ℤ)) ![((k * N : ℕ) : ℤ), -(k : ℤ)]) := fun U _ g => by
    simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  obtain ⟨c, hc⟩ := GlobalTheory.SectionRatio.ratio_glue _ _ P.U.LG.L hL _ _ _ _ _ (fun _ : Fin 1 => gK) _ _ _
    (endK (t.act.act a)) hF u hu (P.U.SecK k) (fun s₀ => sp (Fp (Fx s₀))) (fun s₀ => s₀)
    (fun y J hJ => GlobalTheory.GenericGenerated.exists_secK_isUnit hLaws.ample V _ P.D P.A t.G P.U.toUnifPre k hk _ _ y J hJ)
    (fun i i' y J hJ => by
      have e := GlobalTheory.T.mixed_cross_identity_genericFibre hLaws V E H t P a N hN hN0 k i _ _ _ (hFx i) (hsp _) (hFp _) k i' _ _ _ (hFx i') (hsp _)
        (hFp _) 1 1 rfl y J hJ
      simpa only [pow_one] using e)
  obtain ⟨c₀, rfl⟩ := (GlobalTheory.unifPre_genericFibre_surjective_appTop_and_isIntegral hLaws.globalFns V _ P.D P.A t.G
    P.U.toUnifPre).1 c
  have hF' := fun (U : Type) (i : CommGroup U) g => (@hF U i g).symm
  have hc₀ : c₀ = 1 := fn_ext (V := ⊤) fun y _ => by
    choose J hJ using fun χ : Spec (CommRingCat.of (FractionRing V)) ⟶ t.G.left => exists_chart hL (χ y)
    have hJ' : Good P.U.LG.L y J := hJ
    obtain ⟨s₀, hs₀⟩ := GlobalTheory.GenericGenerated.exists_secK_isUnit hLaws.ample V _ P.D P.A t.G P.U.toUnifPre k hk _
      unitK y J hJ'
    obtain ⟨b, hb⟩ := exists_sec hL hF' (pullMulSec s₀ (endK (t.act.act a)) u hu)
    have e₁ := sval_eq_mul_of_id hL (sp (Fp (Fx s₀))) b _ (fun y J hJ => by
      rw [hb _ _ y J hJ, sval_pullMulSec _ _ u hu _ y hJ, Category.id_comp]
      exact hc s₀ y J hJ) unitK y J hJ'
    rw [hb _ _ y J hJ', sval_pullMulSec _ _ u hu _ y hJ', unitK_endK] at e₁
    have e₂ := GlobalTheory.T.value_at_unitSection_genericFibre hLaws V E H t P a N hN hN0 k s₀ _ _ _ (hFx s₀) (hsp _) (hFp _) y J hJ'
    have e₃ : val u unitK y J = val (L := P.U.LG.L) P.U.LG.rig (jK V) y J ^ (k * (N - 1)) := by
      have e := val_corr hJ' hn (𝟙 _)
      rw [val_pull hJ', val_pull hJ', Category.id_comp, Category.id_comp, val_pow] at e
      exact e
    have e₄ : gs unitK y ⊤ ((pullback.snd t.G.hom (jK V)).appTop.hom c₀) = gs (𝟙 _) y ⊤ c₀ :=
      (gs_pull unitK (pullback.snd t.G.hom (jK V)) y ⊤ trivial c₀).trans (by rw [unitK_snd])
    rw [e₂, e₃, e₄] at e₁
    rw [gs_eq (𝟙 _) y ⊤ trivial 1, map_one, map_one]
    refine (hs₀.mul (Units.isUnit (val (L := P.U.LG.L) P.U.LG.rig (jK V) y J ^ (k * (N - 1))))).mul_right_cancel ?_
    rw [← e₁, _root_.one_mul, mul_comm]
  have hss : s' = sp (Fp (Fx s)) := SecOps.sec_ext (sec_ext_val hL fun y J hJ => by
    rw [(secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 hrel _ (𝟙 _) y J hJ, Category.id_comp, hc s y J hJ, hc₀, map_one,
      gs_eq (𝟙 _) y ⊤ trivial 1, map_one, map_one, _root_.one_mul])
  rw [hss]
  exact hsp _

end GlobalTheory.PullExpansion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FinrankOfExpBij
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnifPower

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_clear {R Rm : Type} [CommRing R] [CommRing Rm] [Algebra R Rm] (M : Submonoid R) [IsLocalization M Rm]
    {X Y Y' : Scheme.{0}} {π : Y ⟶ Spec (CommRingCat.of R)} {π' : Y' ⟶ Spec (CommRingCat.of Rm)} {h : Y' ⟶ Y}
    (H : IsPullback h π' π (Spec.map (CommRingCat.ofHom (algebraMap R Rm))))
    [CompactSpace Y] [QuasiSeparatedSpace Y] {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K → (Y' ⟶ X)) (hφ : ∀ a, φ' a = h ≫ φ a)
    (s' : LB.Sec (LB.LinComb L φ' ε)) :
    ∃ t ∈ M, ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (y : Y') (J : (Y' ⟶ X) → L.ι), Good L y J →
      sval s (𝟙 _ ≫ h) y J = cst (𝟙 _ ≫ π') y (algebraMap R Rm t) * sval s' (𝟙 _) y J := by
  obtain rfl : φ' = fun a => h ≫ φ a := funext hφ
  obtain ⟨t, ht, s, hs⟩ := TwistLoc.exists_clear_denominator M H hL φ ε s'
  refine ⟨t, ht, s, fun y J hJ => ?_⟩
  rw [sval_of s (𝟙 _ ≫ h) y J (fun a => J (𝟙 _ ≫ h ≫ φ a)) (fun a => by rw [Category.assoc])]
  refine (hs _ (𝟙 _) y _ (hJ.mem (fun a => h ≫ φ a) (𝟙 _))).trans (congrArg₂ (· * ·) ?_ rfl)
  rw [H.w, ← Category.assoc]
  exact cst_comp _ (algebraMap R Rm) y t

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V))

theorem exists_vge (v : AddValuation (FractionRing V) (WithTop ℚ)) {k : ℕ} {α : D.toPre.X}
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))) :
    ∃ r : ℚ, VGe D (FractionRing V) v k α s r := by
  have hL := D.toPre.P.isLB
  have := D.toPre.P.isAb.proper
  have : CompactSpace D.toPre.P.A.left := QuasiCompact.compactSpace_of_compactSpace D.toPre.P.A.hom
  have : QuasiSeparatedSpace D.toPre.P.A.left :=
    (quasiSeparated_iff_quasiSeparatedSpace D.toPre.P.A.hom).mp inferInstance
  have hid : jFK (R := V) (FractionRing V) ≫ jK V = jK V :=
    (congrArg (· ≫ jK V) (Spec.map_id _ : jFK (R := V) (FractionRing V) = 𝟙 _)).trans (Category.id_comp _)
  have H₀ : IsPullback (DegPre.prB D.toPre (FractionRing V)).left
      (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left D.toPre.P.A.hom (jFK (R := V) (FractionRing V) ≫ jK V) :=
    (IsPullback.of_hasPullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom).flip
  rw [hid] at H₀
  obtain ⟨t, ht, σ, hσ⟩ := exists_clear (nonZeroDivisors V) H₀ hL (D.toPre.famφB α) (DegPre.famε k) _
    (GC.famφ_eq D.toPre (FractionRing V) α) s
  obtain ⟨σF, hσF⟩ := FamInt.exists_pull (D := D) (F := FractionRing V) σ
  have ht0 : algebraMap V (FractionRing V) t ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1
    (fun h => inv_ne_zero ht0 ((AddValuation.top_iff v).1 h) : v (algebraMap V (FractionRing V) t)⁻¹ ≠ ⊤)
  refine ⟨r, 1, fun _ => (algebraMap V (FractionRing V) t)⁻¹, fun _ => σ, fun _ => σF, fun _ => hσF,
    fun _ => hr.le, fun j => ?_⟩
  refine (sec_ext_val hL (s' := FamInt.secLin (fun _ : Fin 1 => gF D.toPre (FractionRing V)
    (algebraMap V (FractionRing V) t)⁻¹) (fun _ => σF)) (fun y J hJ => ?_) j).trans rfl
  rw [SectionScalarValuation.sval_lin (s := FamInt.secLin _ _) (fun _ : Fin 1 => gF D.toPre (FractionRing V)
    (algebraMap V (FractionRing V) t)⁻¹) (fun _ : Fin 1 => σF) (fun _ => rfl) _ y hJ, Fin.sum_univ_one,
    ← SectionScalarValuation.secScal_sval hσF _ y hJ, hσ y J hJ, ← _root_.mul_assoc]
  have e2 : gs (𝟙 _) y ⊤ (gF D.toPre (FractionRing V) (algebraMap V (FractionRing V) t)⁻¹) =
      cst (𝟙 _ ≫ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left) y (algebraMap V (FractionRing V) t)⁻¹ :=
    gs_pull _ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y ⊤ trivial _
  rw [e2]
  refine (_root_.one_mul _).symm.trans (congrArg₂ (· * ·) ?_ rfl)
  refine Eq.trans ?_ (TwistLoc.gc_mul _ y _ _)
  rw [inv_mul_cancel₀ ht0, TwistLoc.gc, map_one, gs_eq _ _ ⊤ trivial, map_one, map_one]

theorem exists_basis (hU : UUStatement) (k : ℕ) (hk : 1 ≤ k) :
    Nonempty (Module.Basis (Fin (k ^ (D.toPre.rank + D.toPre.P.g))) (FractionRing V)
      (Fam D.toPre (FractionRing V) k)) := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  choose Q hQ using QForm.exists_QVal hϖ D
  have hv := FamInt.valOver_ordVal hϖ
  obtain ⟨b, hb, -, hsp⟩ := hU V ϖ hϖ D Q hQ (FractionRing V) (FamInt.ordVal hϖ) hv
    (Or.inr ⟨1, le_rfl, fun x hx => by
      obtain ⟨n, hn⟩ := hasVal_of_ne_zero hϖ hx
      exact ⟨n, by rw [Nat.cast_one, div_one]; exact hv x n hn⟩⟩) k hk
  refine ⟨Module.Basis.mk hb fun s _ => ?_⟩
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul D.toPre.X k hk
  choose r hr using fun i => exists_vge D (FamInt.ordVal hϖ) (s.s (e i))
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ i, (Q (e i) : ℚ) / k - r i ≤ n := by
    obtain ⟨m, hm⟩ := (Set.finite_range fun i => (Q (e i) : ℚ) / k - r i).bddAbove
    obtain ⟨n, hn⟩ := exists_nat_ge m
    exact ⟨n, fun i => (hm ⟨i, rfl⟩).trans hn⟩
  have h1 : NuGe D Q (FractionRing V) (FamInt.ordVal hϖ) k s (-n) := by
    rw [n1a V ϖ hϖ D Q hQ _ _ hv k hk (Finset.univ.image e) (fun χ => by
      obtain ⟨i, hi, -⟩ := he χ
      exact ⟨e i, Finset.mem_image_of_mem _ (Finset.mem_univ i), hi⟩) s]
    intro α hα
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hα
    exact VGe.mono (hr i) (by linarith [hn i])
  have hπ : algebraMap V (FractionRing V) ϖ ^ n ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr hϖ.ne_zero)
  have h2 := NuGe.smul Q (q := n) (ζ := algebraMap V (FractionRing V) ϖ ^ n)
    (le_of_eq (hv (algebraMap V (FractionRing V) ϖ ^ n) n ⟨1, by simp⟩).symm) ((isSmul_iff _ s _).2 rfl) h1
  rw [neg_add_cancel] at h2
  obtain ⟨c, -, hc⟩ := (hsp _).1 h2
  rw [← inv_smul_smul₀ hπ s, hc]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem finrank_of_expBij (hL : Laws) {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G)
    (k : ℕ) (hk : 1 ≤ k) (hbij : U.ExpBij k) :
    Module.finrank (FractionRing V) (Fam D.toPre (FractionRing V) k) = k ^ A.g := by
  obtain ⟨b, hex, huniq⟩ := GenericSectionBasis.exists_secK_basis hL.secBaseChange V _ D A G U k hk
  choose F hF using fun i => (hbij.1 (b i)).exists
  have hlin := fun c s hs => ExpandsFracLinear.main V _ D A G U k (k ^ A.g) c b F s hF hs
  let φ : (Fin (k ^ A.g) → FractionRing V) →ₗ[FractionRing V] Fam D.toPre (FractionRing V) k :=
    Fintype.linearCombination (FractionRing V) F
  have hinj : Function.Injective φ := by
    intro c c' h
    obtain ⟨s, hs⟩ := hex c
    obtain ⟨s', hs'⟩ := hex c'
    have h1 : U.Expands k s (φ c) := hlin c s hs
    have h2 : U.Expands k s' (φ c') := hlin c' s' hs'
    rw [← h] at h2
    obtain rfl : s = s' := (hbij.2 (φ c)).unique h1 h2
    exact (huniq s).unique hs hs'
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨s, hs⟩ := (hbij.2 x).exists
    obtain ⟨c, hc⟩ := (huniq s).exists
    exact ⟨c, (hbij.1 s).unique (hlin c s hc) hs⟩
  rw [← (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq]
  simp

theorem expBij_of_indep (hL : Laws) {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G)
    (k : ℕ) (hk : 1 ≤ k) [Module.Finite (FractionRing V) (Fam D.toPre (FractionRing V) k)]
    (hdim : Module.finrank (FractionRing V) (Fam D.toPre (FractionRing V) k) = k ^ A.g)
    (htot : ∀ s, ∃ E, U.Expands k s E) {Ix : Type} [Fintype Ix] (hIx : Fintype.card Ix = k ^ A.g)
    (B : Ix → Fam D.toPre (FractionRing V) k) (hB : LinearIndependent (FractionRing V) B)
    (hon : ∀ a, ∃ s, U.Expands k s (B a)) : U.ExpBij k := by
  have hfun := ExpFun.main hL.lemmaB V D A G U k
  obtain ⟨b, hex, huniq⟩ := GenericSectionBasis.exists_secK_basis hL.secBaseChange V _ D A G U k hk
  choose F hF using fun i => htot (b i)
  let φ : (Fin (k ^ A.g) → FractionRing V) →ₗ[FractionRing V] Fam D.toPre (FractionRing V) k :=
    Fintype.linearCombination (FractionRing V) F
  have hlin : ∀ c s, _ → U.Expands k s (φ c) :=
    fun c s hs => ExpandsFracLinear.main V _ D A G U k (k ^ A.g) c b F s hF hs
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hB.span_eq_top_of_card_eq_finrank' (hIx.trans hdim.symm),
      Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨s, hs⟩ := hon a
    obtain ⟨c, hc⟩ := (huniq s).exists
    exact ⟨c, hfun s _ _ (hlin c s hc) hs⟩
  have hinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hdim]; simp)).2 hsurj
  refine ⟨fun s => ?_, fun E => ?_⟩
  · obtain ⟨E, hE⟩ := htot s
    exact ⟨E, hE, fun E' hE' => hfun s _ _ hE' hE⟩
  · obtain ⟨c, rfl⟩ := hsurj E
    obtain ⟨s, hs⟩ := hex c
    refine ⟨s, hlin c s hs, fun s' hs' => SecOps.sec_ext fun j => ?_⟩
    obtain ⟨c', hc'⟩ := (huniq s').exists
    obtain rfl : c' = c := hinj (hfun s' _ _ (hlin c' s' hc') hs')
    exact (hc' j).trans (hs j).symm

theorem main : Laws → UUStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V],
    UnifPowSt3 (I := maximalIdeal V) := by
  intro hL hU V _ _ _ D A G _ _ U j D' A' G' _ _ pD pA pG
  obtain ⟨U', wL, hyp⟩ := GlobalTheory.T.uniformisation_power_without_expansion hL.globalFns V _ j D D' A A' G G' pD pA pG U.toUnifPre
  have key : ∀ k : ℕ, 1 ≤ k → U'.ExpBij k := by
    intro k hk
    obtain ⟨hbox, hspan⟩ := GenericBoxSpan.main hL V _ j D D' A A' G G' pD pA pG U' U.toUnifPre wL hyp k hk
    have hexp := ExpandsBoxPre.main V _ j D D' A A' G G' pD pA pG U' U.toUnifPre wL hyp k
    have hfam := BoxFamily.exists_isBoxFam hL.globalFns V j D.toPre D'.toPre pD (FractionRing V) k
    obtain ⟨b⟩ := exists_basis D hU k hk
    obtain ⟨b'⟩ := exists_basis D' hU k hk
    have := Module.Finite.of_basis b'
    have e₁ : k ^ (D.toPre.rank + D.toPre.P.g) = k ^ A.g := by
      rw [← finrank_of_expBij D hL U.toUnifPre k hk (U.expand k hk), Module.finrank_eq_card_basis b,
        Fintype.card_fin]
    have e₂ : A'.g = j * A.g :=
      H1.dim_unique _ A'.smoothDim ((PowGrp.powers _ A'.A A.A j pA.toIsPowGrp).2.2.1 A.g A.smoothDim)
        (eSec A'.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V)))
    have e₃ : (k ^ (D.toPre.rank + D.toPre.P.g)) ^ j = k ^ A'.g := by rw [e₁, e₂, ← pow_mul, mul_comm]
    obtain ⟨r₁, r₂⟩ := rank_and_g_of_isPowDeg V j D.toPre D'.toPre pD
    choose B hB using fun a : Fin j → Fin (k ^ (D.toPre.rank + D.toPre.P.g)) => hfam fun i => b (a i)
    refine expBij_of_indep D' hL U' k hk ?_ (fun s₀ => ?_) (by rw [← e₃]; simp) B
      (boxFam_linearIndependent V j _ _ pD _ k _ b b.linearIndependent B hB) (fun a => ?_)
    · rw [Module.finrank_eq_card_basis b', Fintype.card_fin, r₁, r₂, ← mul_add, ← e₃, ← pow_mul, mul_comm]
    · obtain ⟨n, c, s, s', hs, hs₀⟩ := hspan s₀
      choose E hE using fun l i => ((U.expand k hk).1 (s l i)).exists
      choose E' hE' using fun l => hfam (E l)
      exact ⟨_, ExpandsFracLinear.main V _ D' A' G' U' k n c s' E' s₀
        (fun l => hexp (s l) (E l) (hE l) (s' l) (E' l) (hs l) (hE' l)) hs₀⟩
    · choose s hs using fun i => ((U.expand k hk).2 (b (a i))).exists
      obtain ⟨s', hs'⟩ := hbox s
      exact ⟨s', hexp s _ hs s' (B a) hs' (hB a)⟩
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hyp
  exact ⟨⟨U', key⟩, ⟨⟨⟨⟨h₁, wL, h₂, h₃, h₄⟩, h₅⟩, h₆⟩⟩⟩

end GlobalTheory.UnifPower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsSymmetricOfSymmetryGenerator
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory


open Geo.Tor in
theorem isSymmetric_of_symmetry_generator {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (sy : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hsy : sy.IsGen)
    (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sy (eSec G)) (LB.oneGen L.L)) : L.IsSymmetric := by
  have oi : eSec G ≫ (ι[G]).left = eSec G := by
    have : η[G] ≫ ι[G] = η[G] := by simp
    exact congrArg (fun q => q.left) this
  have mem : ∀ (x : G.left) (a b : L.L.ι), (ι[G]).left x ∈ L.L.U a → x ∈ L.L.U b →
      x ∈ LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![a, b] := fun x a b ha hb =>
    Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [ha, hb]
  have le : ∀ p : (PUnit → L.L.ι) × L.L.ι, (L.L.pull (ι[G]).left).U p.1 ⊓ L.L.U p.2 ≤
      LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![p.1 PUnit.unit, p.2] := fun p x hx =>
    mem x _ _ (mem_pull.1 hx.1) hx.2
  let w : LB.Iso L.L (L.L.pull (ι[G]).left) := ⟨fun p => res (le p) (sy.s ![p.1 PUnit.unit, p.2])⟩
  have hw : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (a b : L.L.ι), (ι[G]).left (f y) ∈ L.L.U a → f y ∈ L.L.U b →
      gw w f y a b = gm f y (LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![a, b]) (sy.s ![a, b]) :=
    fun Y f y a b ha hb => gm_res f y (le (fun _ => a, b)) ⟨mem_pull.2 ha, hb⟩ _
  have pg : PGen w := by
    intro Y f y j j' k k' hj hj' hk hk'
    rw [hw Y f y j k hj hk, hw Y f y j' k' hj' hk', gen_trans hsy f y (mem _ _ _ hj hk) (mem _ _ _ hj' hk')]
    congr 1
    rw [trF, Fin.prod_univ_two]
    show gm (f ≫ (ι[G]).left) y _ (L.L.g j j') ^ (1 : ℤ) * gm (f ≫ 𝟙 _) y _ (L.L.g k k') ^ (-1 : ℤ) = _
    rw [Category.comp_id, zpow_one, zpow_neg_one]
  refine ⟨oi.trans (Category.id_comp _).symm, w, (isGen_iff w).2 pg, ?_⟩
  refine (maps_iff w (K := PUnit) (fun _ => eSec G) (fun _ => eSec G) (fun _ => 1) L.rig L.rig (𝟙 _) _
    (fun j => rigPull_le _ (𝟙 _) (oi.trans (Category.id_comp _).symm) L.L j) (fun _ => rfl)).2 ?_
  intro Z r z p q hp hq
  have hp₀ : (ι[G]).left ((r ≫ eSec G) z) ∈ L.L.U (p PUnit.unit) := hp PUnit.unit
  have hq₀ : (r ≫ eSec G) z ∈ L.L.U (q PUnit.unit) := hq PUnit.unit
  have ri : (r ≫ eSec G) ≫ (ι[G]).left = r ≫ eSec G := by rw [Category.assoc, oi]
  have hp₁ : (r ≫ eSec G) z ∈ L.L.U (p PUnit.unit) := by rw [← ri]; exact hp₀
  have hq₁ : (ι[G]).left ((r ≫ eSec G) z) ∈ L.L.U (q PUnit.unit) := by
    have := hq₀
    rw [← ri] at this; exact this
  have one : gw w (r ≫ eSec G) z (q PUnit.unit) (q PUnit.unit) = 1 := by
    obtain ⟨J, hJ, e⟩ := exists_good L.L L.isLB z (K := PUnit) (fun _ => r ≫ eSec G) q (fun _ _ _ => rfl)
      (fun _ => hq₀)
    have a := val_corr hJ hr r
    rw [val_pull hJ, val_one, val_of sy (r ≫ eSec G) z J ![q PUnit.unit, q PUnit.unit] (fun k => by
      fin_cases k
      · exact (congrArg J ri).trans (e PUnit.unit)
      · exact (congrArg J (Category.comp_id _)).trans (e PUnit.unit))] at a
    exact (hw _ _ _ _ _ hq₁ hq₀).trans a
  rw [Category.comp_id, Fintype.prod_unique, zpow_one,
    gen_trans L.rigGen r z (j := p) (j' := q) (Set.mem_iInter.2 fun _ => hp₁) (Set.mem_iInter.2 fun _ => hq₀)]
  congr 1
  have b := pg _ (r ≫ eSec G) z (p PUnit.unit) (q PUnit.unit) (q PUnit.unit) (q PUnit.unit) hp₀ hq₁ hq₀ hq₀
  rw [one, gm_self L.isLB _ z hq₀, ri, inv_one, _root_.mul_one, _root_.mul_one] at b
  rw [trF, Fintype.prod_unique, zpow_one]
  exact b.symm

theorem exists_pelUnif_pow : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of R))) (P : Geo.Tor.PELUnif I t) (j : ℕ), UnifPowSt3 (I := I) → (∃ D' : DegData R I, Nonempty (IsPowDeg D'.toPre P.D.toPre j)) → (∃ A' : PolAV (Spec (CommRingCat.of (FractionRing R))), Nonempty (IsPowPolAV A' P.A j)) → ∃ (t' : Geo.Tor.SAB H (Spec (CommRingCat.of R))) (P' : Geo.Tor.PELUnif I t') (pG : IsPowGrp t'.G t.G j) (pD : IsPowDeg P'.D.toPre P.D.toPre j) (pA : IsPowPolAV P'.A P.A j), Nonempty (UnifPowOf3 pD pA pG P'.U P.U) ∧ (∀ a i, t'.act.act a ≫ pG.pr i = pG.pr i ≫ t.act.act a) ∧ ∀ (a : NumberField.RingOfIntegers E) (x : P'.D.toPre.X), pD.xe (a • x) = a • pD.xe x := by
  intro hG R _ _ I E _ _ _ H t P j hU ⟨D', ⟨pD⟩⟩ ⟨A', ⟨pA⟩⟩
  letI := H.starRing
  let pG : IsPowGrp (powObj t.G j) t.G j := powIsPowGrp t.G j
  obtain ⟨U', ⟨Q⟩⟩ := hU P.D P.A t.G P.U j D' A' (powObj t.G j) pD pA pG
  obtain ⟨act', hact⟩ := (GlobalTheory.exists_powAct _ _ _ j pG).2 _ t.act
  have iso : Geo.Tor.LBIso U'.LG.L (boxLB t.PP.L pG.pr) := by
    rw [← P.bundle]; exact ⟨Q.wL, Q.wL_gen⟩
  let t' : Geo.Tor.SAB H (Spec (CommRingCat.of R)) :=
    { G := powObj t.G j
      semi := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ j pG t.semi
      act := act'
      PP := U'.LG
      cub := U'.cubG
      sym := isSymmetric_of_symmetry_generator U'.LG U'.symG U'.symG_gen U'.symG_rig
      adj := fun a => GlobalTheory.PowAdj.lbIso_cube_pow _ _ _ j pG _ _ t.PP.isLB U'.LG.isLB iso _ _ _ _ (hact a) (hact (H.bar a)) (t.adj a)
      prim := GlobalTheory.PowPrimitive.lbIso_cube_pow _ _ _ j pG _ _ t.PP.isLB U'.LG.isLB iso _ _ (hact H.w0) t.prim }
  letI md : Module (NumberField.RingOfIntegers E) D'.toPre.X := pD.xe.module _
  have hx : ∀ (a : NumberField.RingOfIntegers E) (x : D'.toPre.X), pD.xe (a • x) = a • pD.xe x := fun a x =>
    pD.xe.apply_symm_apply _
  obtain ⟨oD', hoD⟩ := GlobalTheory.powDeg_diagonal_action hG R j _ _ pD _ hx P.oD
  obtain ⟨rA, hrA⟩ := (GlobalTheory.exists_powAct _ _ _ j pA.toIsPowGrp).1 _ P.oA.toRingAct
  let oA' : A'.OAct (NumberField.RingOfIntegers E) :=
    { toRingAct := rA
      rosati := fun a => GlobalTheory.rosatiAdj_pow _ _ _ j pA.toIsPowGrp _ _ P.A.isLB A'.isLB ⟨pA.w, pA.w_gen⟩ _ _ _ _ (hrA a)
        (hrA (star a)) (P.oA.rosati a) }
  let P' : Geo.Tor.PELUnif I t' :=
    { D := D'
      oD := oD'
      A := A'
      oA := oA'
      U := U'
      bundle := rfl
      lin := GlobalTheory.oLinear_of_unifPow R I j _ _ _ _ _ _ pD pA pG U' P.U Q _ hx P.oD oD' P.oA oA' t.act.toRingAct act'.toRingAct
        hoD hrA hact P.lin
      w0 := GlobalTheory.PsiWZeroProd.main R j _ _ pD _ hx P.oD oD' hoD H.w0 P.w0 }
  exact ⟨t', P', pG, pD, pA, ⟨Q⟩, hact, hx⟩

end GlobalTheory
end

