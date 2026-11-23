module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0091
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CommGroupCommonFactorQuotientCancel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecExpandsAtOfIntegralFamily
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_sec_expandsAt_of_integral_family : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) [QuasiCompact G.hom], (∀ F : Fam D.toPre (FractionRing R) k, ∃ s : U.SecK k, U.Expands k s F) → ∀ (F : Fam D.toPre (FractionRing R) k) (f : ∀ α, D.toPre.SecB k α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α) (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left 1) → ∃ σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))), ∀ e, U.ExpandsAt e k σ f := by
  intro R _ _ I hR D A G _ _ _ U k _ hall F f hf
  obtain ⟨s, r, hr, σ₀, f₀, -, hf₀, hE⟩ := hall F
  have hw : (D.toPre.prB (FractionRing R)).left ≫ D.toPre.P.A.hom = (D.toPre.BF (FractionRing R)).hom := Over.w _
  have hm : ∀ α, DVR.SecIsMul D.toPre.P.A.hom r (f₀ α) (f α) := fun α =>
    GlobalTheory.IntegralExpansion.secIsMul_of_secScal D.toPre.P.isLB D.toPre.P.A.hom
      (fun W => GlobalTheory.IntegralExpansion.prB_app_injective D.toPre W) (hf α) (by rw [hw]; exact hf₀ α)
  have hm' : ∀ α, ∀ j, (f₀ α).f j = resTop _ (scal D.toPre.P.A.hom r) * (f α).f j := fun α j => hm α j
  obtain ⟨σ, hσ⟩ := GlobalTheory.sec_div_of_expandsAt R I hR D A G U k r hr σ₀ f₀ f hm' hE
  exact ⟨σ, GlobalTheory.T.expandsAt_cancel_nonzero_scalar R I hR D A G U k r hr σ₀ σ f₀ f hm' hσ hE⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistGen

open LBGerm TopologicalSpace

variable {X : Scheme.{0}} {M H : LB X}

theorem gm_tw_g (M H : LB X) (t : ℕ) (y : X) (p q : M.ι × H.ι) (hp : y ∈ M.U p.1 ⊓ H.U p.2)
    (hq : y ∈ M.U q.1 ⊓ H.U q.2) :
    (gm (𝟙 X) y ((tw M H t).U p ⊓ (tw M H t).U q) ((tw M H t).g p q)).val =
      (gm (𝟙 X) y (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1)).val *
        (gm (𝟙 X) y (H.U p.2 ⊓ H.U q.2) (H.g p.2 q.2)).val ^ t := by
  have hy : (𝟙 X : X ⟶ X) y ∈ M.U p.1 ⊓ H.U p.2 ⊓ (M.U q.1 ⊓ H.U q.2) := ⟨hp, hq⟩
  rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, tw_g]
  refine congrArg Units.val ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res (𝟙 X) y _ hy _) ?_))
  rw [zpow_natCast]
  exact (map_pow _ _ _).trans (congrArg (· ^ t) (gm_res (𝟙 X) y _ hy _))

theorem exists_mul_pow (a e : ℕ) (u : LB.Sec (tw M H a)) (s : LB.Sec H) :
    ∃ u' : LB.Sec (tw M H ((a + e : ℕ) : ℤ)), nonzeroLocus u ⊓ nonzeroLocus s ≤ nonzeroLocus u' := by
  let F : ∀ p : M.ι × H.ι, Γ(X, M.U p.1 ⊓ H.U p.2) := fun p =>
    (show Γ(X, M.U p.1 ⊓ H.U p.2) from u.f p) * resG X inf_le_right (s.f p.2) ^ e
  have hF : ∀ (y : X) (p : M.ι × H.ι), y ∈ M.U p.1 ⊓ H.U p.2 → gs (𝟙 X) y _ (F p) =
      gs (𝟙 X) y _ (u.f p) * gs (𝟙 X) y _ (s.f p.2) ^ e := fun y p hy => by
    rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy]
    rfl
  refine ⟨secOfGerm (M := tw M H ((a + e : ℕ) : ℤ)) F fun y p q hp hq => ?_, fun y hy => ?_⟩
  · refine (hF y p hp).trans (Eq.trans ?_ (congrArg₂ (· * ·) (gm_tw_g M H (a + e) y p q hp hq) (hF y q hq)).symm)
    rw [gs_compat u (𝟙 X) y (j := p) (j' := q) hp hq, gm_tw_g M H a y p q hp hq,
      gs_compat s (𝟙 X) y (j := p.2) (j' := q.2) hp.2 hq.2]
    ring
  · obtain ⟨p, hp⟩ := exists_chart_of_mem_nonzeroLocus hy.1
    refine (mem_nonzeroLocus_iff_isUnit (M := tw M H ((a + e : ℕ) : ℤ)) _ (k := p) hp).2 ?_
    refine (congrArg IsUnit (hF y p hp)).mpr ?_
    exact (((mem_nonzeroLocus_iff_isUnit u hp).1 hy.1).mul
      (((mem_nonzeroLocus_iff_isUnit s hp.2).1 hy.2).pow e))

theorem exists_sec_of_le_chart [CompactSpace X] [QuasiSeparatedSpace X] (hM : M.IsLB) (hH : H.IsLB) (n : ℕ)
    (σ : ∀ j, Γ(X, H.U j))
    (hσ : ∀ (y : X) j j', y ∈ H.U j → y ∈ H.U j' → gs (𝟙 X) y _ (σ j) =
      (gm (𝟙 X) y (H.U j ⊓ H.U j') (H.g j j')).val ^ n * gs (𝟙 X) y _ (σ j'))
    (V : X.Opens) (hV : ∀ (y : X) j, y ∈ H.U j → (y ∈ V ↔ IsUnit (gs (𝟙 X) y _ (σ j))))
    (k : M.ι) (hk : V ≤ M.U k) :
    ∃ (N : ℕ) (u : LB.Sec (tw M H ((n * N : ℕ) : ℤ))), V ≤ nonzeroLocus u := by
  obtain ⟨α, _, W, J, hWa, hW, hc⟩ : ∃ (α : Type) (_ : Fintype α) (W : α → X.Opens) (J : α → M.ι × H.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ M.U (J a).1 ⊓ H.U (J a).2) ∧ ∀ y : X, ∃ a, y ∈ W a :=
    exists_finite_affine_refinement (isLB_tw hM hH 0)
  have hW₂ : ∀ a, W a ≤ H.U (J a).2 := fun a => (hW a).trans inf_le_right
  have hb : ∀ (U : X.Opens) (j : H.ι) (hU : U ≤ H.U j) (y : X),
      y ∈ X.basicOpen (resG X hU (σ j)) → y ∈ V := fun U j hU y hy => by
    have hy₁ : y ∈ U := X.basicOpen_le _ hy
    have hs := (isUnit_gs_iff (𝟙 X) y _ hy₁ _).2 hy
    rwa [gs_res _ y _ hy₁, ← hV y j (hU hy₁)] at hs
  have step₁ : ∀ a, ∃ (e : ℕ) (v : Γ(X, W a)), ∀ y ∈ W a, y ∈ V →
      gs (𝟙 X) y _ v = gs (𝟙 X) y _ (σ (J a).2) ^ e *
        (gm (𝟙 X) y (M.U (J a).1 ⊓ M.U k) (M.g (J a).1 k)).val := fun a => by
    have le : X.basicOpen (resG X (hW₂ a) (σ (J a).2)) ≤ M.U (J a).1 ⊓ M.U k :=
      fun y hy => ⟨(hW a (X.basicOpen_le _ hy)).1, hk (hb _ _ _ y hy)⟩
    obtain ⟨e, v, hv⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X (W a) (hWa a).isCompact
      (hWa a).isQuasiSeparated (resG X (hW₂ a) (σ (J a).2)) (resG X le (M.g (J a).1 k).val)
    have hv' : resG X (X.basicOpen_le _) v =
        resG X (X.basicOpen_le _) (resG X (hW₂ a) (σ (J a).2)) ^ e * resG X le (M.g (J a).1 k).val := hv
    refine ⟨e, v, fun y hy hs => ?_⟩
    have hy' : y ∈ X.basicOpen (resG X (hW₂ a) (σ (J a).2)) := (isUnit_gs_iff (𝟙 X) y _ hy _).1 (by
      rw [gs_res _ y _ hy]; exact (hV y _ (hW₂ a hy)).1 hs)
    have e₁ := congrArg (gs (𝟙 X) y _) hv'
    rwa [gs_res _ y _ hy', gs_mul _ y _ hy', gs_pow _ y _ hy', gs_res _ y _ hy', gs_res _ y _ hy,
      gs_res _ y _ hy', gs_unit (𝟙 X) y _ (le hy')] at e₁
  choose e v hv using step₁
  obtain ⟨N₁, v', hv'⟩ : ∃ (N₁ : ℕ) (v' : ∀ a, Γ(X, W a)), ∀ a, ∀ y ∈ W a, y ∈ V →
      gs (𝟙 X) y _ (v' a) = gs (𝟙 X) y _ (σ (J a).2) ^ N₁ *
        (gm (𝟙 X) y (M.U (J a).1 ⊓ M.U k) (M.g (J a).1 k)).val :=
    ⟨Finset.univ.sup e, fun a => resG X (hW₂ a) (σ (J a).2) ^ (Finset.univ.sup e - e a) * v a, fun a y hy hs => by
      rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy, hv a y hy hs, ← _root_.mul_assoc, ← pow_add,
        Nat.sub_add_cancel (Finset.le_sup (f := e) (Finset.mem_univ a))]⟩
  have step₂ : ∀ p : α × α, ∃ d : ℕ, ∀ y ∈ W p.1 ⊓ W p.2, gs (𝟙 X) y _ (σ (J p.1).2) ^ d *
      (gs (𝟙 X) y _ (v' p.1) - (gm (𝟙 X) y (M.U (J p.1).1 ⊓ M.U (J p.2).1) (M.g (J p.1).1 (J p.2).1)).val *
        (gm (𝟙 X) y (H.U (J p.1).2 ⊓ H.U (J p.2).2)
        (H.g (J p.1).2 (J p.2).2)).val ^ (n * N₁) * gs (𝟙 X) y _ (v' p.2)) = 0 := by
    rintro ⟨a, b⟩
    have hcpt : IsCompact ((W a ⊓ W b : X.Opens) : Set X) :=
      QuasiSeparatedSpace.inter_isCompact _ _ (W a).isOpen (hWa a).isCompact (W b).isOpen (hWa b).isCompact
    have le₁ : W a ⊓ W b ≤ M.U (J a).1 ⊓ M.U (J b).1 := fun y hy => ⟨(hW a hy.1).1, (hW b hy.2).1⟩
    have le : W a ⊓ W b ≤ H.U (J a).2 ⊓ H.U (J b).2 := fun y hy => ⟨(hW a hy.1).2, (hW b hy.2).2⟩
    have hx : ∀ y ∈ W a ⊓ W b, gs (𝟙 X) y (W a ⊓ W b) (resG X inf_le_left (v' a) -
        resG X le₁ (M.g (J a).1 (J b).1).val * resG X le (H.g (J a).2 (J b).2).val ^ (n * N₁) *
          resG X inf_le_right (v' b)) =
        gs (𝟙 X) y _ (v' a) - (gm (𝟙 X) y (M.U (J a).1 ⊓ M.U (J b).1) (M.g (J a).1 (J b).1)).val *
          (gm (𝟙 X) y (H.U (J a).2 ⊓ H.U (J b).2) (H.g (J a).2 (J b).2)).val ^ (n * N₁) *
            gs (𝟙 X) y _ (v' b) := fun y hy => by
      rw [gs_sub _ y _ hy, gs_mul _ y _ hy, gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy,
        gs_res _ y _ hy, gs_res _ y _ hy, gs_unit (𝟙 X) y _ (le hy), gs_unit (𝟙 X) y _ (le₁ hy)]
    obtain ⟨d, hd⟩ := exists_pow_mul_gs_eq_zero hcpt (resG X (inf_le_left.trans (hW₂ a)) (σ (J a).2)) _
      fun y hy => by
        have hy₁ : y ∈ W a ⊓ W b := X.basicOpen_le _ hy
        have hs := hb _ _ _ y hy
        refine (hx y hy₁).trans ?_
        rw [hv' a y hy₁.1 hs, hv' b y hy₁.2 hs, hσ y (J a).2 (J b).2 (hW₂ a hy₁.1) (hW₂ b hy₁.2),
          ← gm_cocycle hM (𝟙 X) y (hW a hy₁.1).1 (hW b hy₁.2).1 (hk hs), Units.val_mul]
        ring
    refine ⟨d, fun y hy => ?_⟩
    have := hd y hy
    rwa [hx y hy, gs_res _ y _ hy] at this
  choose d hd using step₂
  obtain ⟨c, hc'⟩ : ∃ c, ∀ p, d p ≤ c := ⟨Finset.univ.sup d, fun p => Finset.le_sup (Finset.mem_univ p)⟩
  have hz : ∀ a, ∀ y ∈ W a, gs (𝟙 X) y _ (resG X (hW₂ a) (σ (J a).2) ^ c * v' a) =
      gs (𝟙 X) y _ (σ (J a).2) ^ c * gs (𝟙 X) y _ (v' a) := fun a y hy => by
    rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy]
  obtain ⟨u, hu⟩ := exists_sec_of_refinement (isLB_tw hM hH ((n * (N₁ + c) : ℕ) : ℤ)) W J hW hc
    (fun a => resG X (hW₂ a) (σ (J a).2) ^ c * v' a) fun y a b ha hb => by
      obtain ⟨c', hc''⟩ := Nat.exists_eq_add_of_le (hc' (a, b))
      have e₁ := hd (a, b) y ⟨ha, hb⟩
      have e₂ := hσ y (J a).2 (J b).2 (hW₂ a ha) (hW₂ b hb)
      rw [hz a y ha, hz b y hb, gm_tw_g M H _ y (J a) (J b) (hW a ha) (hW b hb)]
      dsimp only at e₁
      rw [e₂] at e₁ ⊢
      rw [hc'']
      generalize gs (𝟙 X) y _ (σ (J b).2) = τ at e₁ ⊢
      generalize Units.val (gm (𝟙 X) y _ (H.g (J a).2 (J b).2)) = w at e₁ ⊢
      linear_combination (w ^ n * τ) ^ c' * e₁
  refine ⟨N₁ + c, u, fun y hy => ?_⟩
  obtain ⟨a, ha⟩ := hc y
  have hs := (hV y _ (hW₂ a ha)).1 hy
  rw [mem_nonzeroLocus_iff_isUnit u (k := J a) (hW a ha), hu y (J a) a (hW a ha) ha, hz a y ha, hv' a y ha hy]
  exact (Units.isUnit _).mul ((hs.pow c).mul ((hs.pow N₁).mul (Units.isUnit _)))

theorem compact_quasiSeparated (hH : H.IsLB) {I : Type} [Finite I] (s : I → LB.Sec H)
    (hc : ⨆ i, nonzeroLocus (s i) = ⊤) (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i))) :
    CompactSpace X ∧ QuasiSeparatedSpace X := by
  have mem : ∀ y : X, ∃ i, y ∈ nonzeroLocus (s i) := fun y =>
    Opens.mem_iSup.1 (show y ∈ ⨆ i, nonzeroLocus (s i) by rw [hc]; trivial)
  refine ⟨⟨?_⟩, quasiSeparatedSpace_iff_forall_affineOpens.2 fun U V => ?_⟩
  · have : (Set.univ : Set X) = ⋃ i, (nonzeroLocus (s i) : Set X) :=
      (Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 (mem y)).symm
    rw [this]
    exact isCompact_iUnion fun i => (ha i).isCompact
  · have : (U.1 ∩ V.1 : Set X) = ⋃ i, ((nonzeroLocus (s i) ⊓ U.1 : X.Opens) : Set X) ∩
        ((nonzeroLocus (s i) ⊓ V.1 : X.Opens) : Set X) := by
      ext y
      refine ⟨fun hy => ?_, fun hy => ?_⟩
      · obtain ⟨i, hi⟩ := mem y
        exact Set.mem_iUnion.2 ⟨i, ⟨hi, hy.1⟩, ⟨hi, hy.2⟩⟩
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
        exact ⟨hi.1.2, hi.2.2⟩
    rw [this]
    exact isCompact_iUnion fun i => (ha i).isQuasiSeparated _ _ Set.inter_subset_left (Opens.isOpen _)
      (isAffineOpen_nonzeroLocus_inf hH (s i) U.2).isCompact Set.inter_subset_left (Opens.isOpen _)
      (isAffineOpen_nonzeroLocus_inf hH (s i) V.2).isCompact

theorem exists_nhds [CompactSpace X] [QuasiSeparatedSpace X] (hM : M.IsLB) (hH : H.IsLB) (s : LB.Sec H)
    (ha : IsAffineOpen (nonzeroLocus s)) (y : X) (hy : y ∈ nonzeroLocus s) :
    ∃ (V : X.Opens) (N : ℕ), y ∈ V ∧ ∀ e : ℕ, ∃ u : LB.Sec (tw M H ((N + e : ℕ) : ℤ)), V ≤ nonzeroLocus u := by
  obtain ⟨k, hk⟩ := exists_chart hM y
  have hl := nonzeroLocus_secToPow s (le_refl 1)
  rw [← hl] at ha hy
  obtain ⟨a, hle, hya⟩ := ha.exists_basicOpen_le (V := M.U k) ⟨y, hk⟩ hy
  obtain ⟨m, -, σ, hσ⟩ := exists_nonzeroLocus_eq_basicOpen hH (secToPow s 1) a
  obtain ⟨N, u, hu⟩ := exists_sec_of_le_chart hM hH (1 * m) (powSecFn σ) (fun z j j' hj hj' => by
      have hz : z ∈ H.U j ⊓ H.U j' := ⟨hj, hj'⟩
      have e := congrArg (gs (𝟙 X) z _) (powSecFn_compat σ j j')
      rwa [gs_res _ z _ hz, gs_mul _ z _ hz, gs_res _ z _ hz, gs_pow _ z _ hz, gs_unit _ z _ hz] at e)
    (X.basicOpen a) (fun z j hj => by
      rw [isUnit_gs_iff (𝟙 X) z _ hj, ← nonzeroLocus_inf_powSecFn, hσ]
      exact ⟨fun h => ⟨h, hj⟩, fun h => h.1⟩) k hle
  refine ⟨X.basicOpen a, 1 * m * N, hya, fun e => ?_⟩
  obtain ⟨u', hu'⟩ := exists_mul_pow _ e u s
  exact ⟨u', (le_inf hu ((X.basicOpen_le a).trans hl.le)).trans hu'⟩

theorem twist_generated : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ M : LB X, M.IsLB → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∃ (n' : ℕ) (u : Fin (n' + 1) → LB.Sec (tw M H t)), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  intro R _ X f H n s hH hs M hM
  obtain ⟨_, _⟩ := compact_quasiSeparated hH s hs.1 fun i => (hs.2 i).1
  have loc : ∀ y : X, ∃ (V : X.Opens) (N : ℕ), y ∈ V ∧
      ∀ e : ℕ, ∃ u : LB.Sec (tw M H ((N + e : ℕ) : ℤ)), V ≤ nonzeroLocus u := fun y => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs.1]; trivial)
    exact exists_nhds hM hH (s i) (hs.2 i).1 y hi
  choose V N hy hV using loc
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y => (V y : Set X)) (fun y => (V y).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩)
  refine ⟨(T.sup N : ℕ), fun t ht => ?_⟩
  have h : ∀ y : T, ∃ u : LB.Sec (tw M H t), V y ≤ nonzeroLocus u := fun y => by
    have h₁ : N y ≤ T.sup N := Finset.le_sup y.2
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, t = ((N y + e : ℕ) : ℤ) := ⟨(t - N y).toNat, by omega⟩
    exact hV y e
  choose u hu using h
  let c : Option T → LB.Sec (tw M H t) := fun o => o.elim DVR.SecOps.secZero u
  let e : Option T ≃ Fin (Fintype.card T + 1) := Fintype.equivFinOfCardEq Fintype.card_option
  refine ⟨_, fun i => c (e.symm i), top_unique fun x _ => ?_⟩
  obtain ⟨y, hyT, hx⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ x))
  refine Opens.mem_iSup.2 ⟨e (some ⟨y, hyT⟩), ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact hu ⟨y, hyT⟩ hx

end GlobalTheory.TwistGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionPrimitiveTwistTorusExtension
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.WtSec

theorem stalkMap_injective {X Z : Scheme.{0}} (r : Z ⟶ X) [Flat r] (z : Z) :
    Function.Injective (r.stalkMap z).hom :=
  (injective_iff_map_eq_zero _).2 fun b hb =>
    zero_dvd_iff.1 (dvd_descend r z (a := 0) (b := b) (by rw [hb, map_zero]))

theorem exists_gs_ne_zero {X : Scheme.{0}} {V : X.Opens} {a : Γ(X, V)} (ha : a ≠ 0) :
    ∃ x ∈ V, gs (𝟙 X) x V a ≠ 0 := by
  by_contra h
  refine ha (fn_ext fun x hx => ?_)
  rw [LBGerm.gs_zero _ x V hx]
  exact by_contra fun k => h ⟨x, hx, k⟩

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X]

theorem isWt_sub {i : splitTorus S X ⟶ G} {V : G.left.Opens} {u v : Γ(G.left, V)} {χ : X} (hu : IsWt i V u χ)
    (hv : IsWt i V v χ) : IsWt i V (u - v) χ :=
  fun Z t g h₁ h₂ => by rw [map_sub, map_sub, hu Z t g h₁ h₂, hv Z t g h₁ h₂, mul_sub]

variable (Q : TQ G X)

theorem isWt_app (V : Q.B.left.Opens) (c : Γ(Q.B.left, V)) : IsWt Q.i _ ((Q.q.left.app V).hom c) 0 := by
  intro Z t g k₁ k₂
  have e : ∀ (r : Z.left ⟶ G.left) (k : ⊤ ≤ r ⁻¹ᵁ (Q.q.left ⁻¹ᵁ V)),
      (r.appLE _ ⊤ k).hom ((Q.q.left.app V).hom c) = ((r ≫ Q.q.left).appLE V ⊤ k).hom c := fun r k =>
    (congrArg (fun q => q.hom c) (Scheme.Hom.comp_appLE r Q.q.left V ⊤ k)).symm
  have e' : ∀ (r r' : Z.left ⟶ Q.B.left) (_ : r = r') (k : ⊤ ≤ r ⁻¹ᵁ V) (k' : ⊤ ≤ r' ⁻¹ᵁ V),
      (r.appLE V ⊤ k).hom c = (r'.appLE V ⊤ k').hom c := by
    rintro r _ rfl k k'; rfl
  rw [e, e, ← chV_val, chV_zero, Units.val_one, _root_.one_mul]
  have k : ((t ≫ Q.i) * g).left ≫ Q.q.left = g.left ≫ Q.q.left := by
    rw [← Over.comp_left, ← Over.comp_left, WtBundle.act_comp]
  exact e' _ _ k _ _

theorem exists_app_of_isWt (V : Q.B.left.Opens) (a : Γ(G.left, Q.q.left ⁻¹ᵁ V)) (h : IsWt Q.i _ a 0) :
    ∃ c, (Q.q.left.app V).hom c = a := by
  have := Q.q_affine
  refine (invariant_functions_descend S G Q.B _ Q.q Q.i Q.q_hom Q.i_hom Q.q_flat Q.q_surj
    inferInstance Q.isKernel V).2.2 a fun Z t g k₁ k₂ => ?_
  rw [h Z t g k₁ k₂, ← chV_val, chV_zero, Units.val_one, _root_.one_mul]

theorem graded (V : Q.B.left.Opens) (hV : IsAffineOpen V) :
    (∀ u : Γ(G.left, Q.q.left ⁻¹ᵁ V), ∃ a : X →₀ Γ(G.left, Q.q.left ⁻¹ᵁ V),
      (∀ χ, IsWt Q.i _ (a χ) χ) ∧ u = a.sum fun _ x => x) ∧
    ∀ a : X →₀ Γ(G.left, Q.q.left ⁻¹ᵁ V), (∀ χ, IsWt Q.i _ (a χ) χ) → (a.sum fun _ x => x) = 0 → a = 0 := by
  have := Q.q_affine
  refine GlobalTheory.functions_graded_by_weights S G X Q.i Q.i_hom _ (hV.preimage _) ?_
  have e := congrArg (fun q => q.left) (WtBundle.act_comp Q (fst (splitTorus _ X) G) (snd _ G))
  simp only [Over.comp_left] at e
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, e]

theorem comp_compat {V V' U : Q.B.left.Opens} (g : Γ(Q.B.left, U)) (hU : V ⊓ V' ≤ U)
    (a : X →₀ Γ(G.left, Q.q.left ⁻¹ᵁ V)) (a' : X →₀ Γ(G.left, Q.q.left ⁻¹ᵁ V'))
    (ha : ∀ χ, IsWt Q.i _ (a χ) χ) (ha' : ∀ χ, IsWt Q.i _ (a' χ) χ)
    (h : ∀ x, Q.q.left x ∈ V → Q.q.left x ∈ V' → gs (𝟙 _) x (Q.q.left ⁻¹ᵁ V) (a.sum fun _ x => x) =
      gs Q.q.left x U g * gs (𝟙 _) x (Q.q.left ⁻¹ᵁ V') (a'.sum fun _ x => x))
    (χ : X) (x : G.left) (hx : Q.q.left x ∈ V) (hx' : Q.q.left x ∈ V') :
    gs (𝟙 _) x (Q.q.left ⁻¹ᵁ V) (a χ) = gs Q.q.left x U g * gs (𝟙 _) x (Q.q.left ⁻¹ᵁ V') (a' χ) := by
  obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (show Q.q.left x ∈ V ⊓ V' from ⟨hx, hx'⟩)
  have hle : W ≤ V ⊓ V' := hle
  have l₁ : Q.q.left ⁻¹ᵁ W ≤ Q.q.left ⁻¹ᵁ V := fun _ k => (hle k).1
  have l₂ : Q.q.left ⁻¹ᵁ W ≤ Q.q.left ⁻¹ᵁ V' := fun _ k => (hle k).2
  have l₃ : Q.q.left ⁻¹ᵁ W ≤ Q.q.left ⁻¹ᵁ U := fun _ k => hU (hle k)
  let g' : Γ(G.left, Q.q.left ⁻¹ᵁ W) := (G.left.presheaf.map (homOfLE l₃).op).hom ((Q.q.left.app U).hom g)
  let r₁ : Γ(G.left, Q.q.left ⁻¹ᵁ V) →+ Γ(G.left, Q.q.left ⁻¹ᵁ W) :=
    (G.left.presheaf.map (homOfLE l₁).op).hom.toAddMonoidHom
  let r₂ : Γ(G.left, Q.q.left ⁻¹ᵁ V') →+ Γ(G.left, Q.q.left ⁻¹ᵁ W) :=
    (AddMonoidHom.mulLeft g').comp (G.left.presheaf.map (homOfLE l₂).op).hom.toAddMonoidHom
  have v : ∀ y, Q.q.left y ∈ W → ∀ b b', gs (𝟙 _) y (Q.q.left ⁻¹ᵁ W) (r₁ b - r₂ b') =
      gs (𝟙 _) y (Q.q.left ⁻¹ᵁ V) b - gs Q.q.left y U g * gs (𝟙 _) y (Q.q.left ⁻¹ᵁ V') b' := fun y hy b b' => by
    refine (LBGerm.gs_sub (𝟙 _) y (Q.q.left ⁻¹ᵁ W) hy _ _).trans (congrArg₂ (· - ·) (gs_res (𝟙 _) y l₁ hy _)
      ((gs_mul (𝟙 _) y (Q.q.left ⁻¹ᵁ W) hy g' _).trans (congrArg₂ (· * ·) ((gs_res (𝟙 _) y l₃ hy _).trans ?_)
        (gs_res (𝟙 _) y l₂ hy _))))
    rw [gs_pull (𝟙 _) Q.q.left y U (l₃ hy), Category.id_comp]
  have s : ∀ {A B : Type} [AddCommGroup A] [AddCommGroup B] (r : A →+ B) (b : X →₀ A),
      ((b.mapRange r (map_zero r)).sum fun _ x => x) = r (b.sum fun _ x => x) := fun r b => by
    rw [Finsupp.sum_mapRange_index (fun _ => rfl), map_finsuppSum]
  have z := (graded Q W hW).2 (a.mapRange r₁ (map_zero r₁) - a'.mapRange r₂ (map_zero r₂))
    (fun ψ => isWt_sub ((ha ψ).res l₁) (by
      have := ((isWt_app Q U g).res l₃).mul ((ha' ψ).res l₂)
      rwa [zero_add] at this)) (by
      rw [Finsupp.sum_sub_index (fun _ _ _ => rfl), s, s]
      refine fn_ext fun y hy => ?_
      rw [v y hy, h y (l₁ hy) (l₂ hy), sub_self, LBGerm.gs_zero (𝟙 _) y (Q.q.left ⁻¹ᵁ W) hy])
  have z' : r₁ (a χ) - r₂ (a' χ) = 0 := DFunLike.congr_fun z χ
  rw [← sub_eq_zero, ← v x hxW, z', LBGerm.gs_zero (𝟙 _) x (Q.q.left ⁻¹ᵁ W) hxW]

theorem exists_component (M : LB Q.B.left) (hM : M.IsLB) (s : LB.Sec (M.pull Q.q.left)) (hs : ∃ j, s.f j ≠ 0) :
    ∃ (χ : X) (α : Type) (V : α → Q.B.left.Opens) (i : α → M.ι) (f : ∀ p, Γ(G.left, Q.q.left ⁻¹ᵁ V p)),
      (∀ p, V p ≤ M.U (i p)) ∧ (∀ y, ∃ p, y ∈ V p) ∧ (∀ p, IsWt Q.i _ (f p) χ) ∧ (∃ p, f p ≠ 0) ∧
      ∀ p p' x, Q.q.left x ∈ V p → Q.q.left x ∈ V p' → gs (𝟙 _) x (Q.q.left ⁻¹ᵁ V p) (f p) =
        (gm Q.q.left x (M.U (i p) ⊓ M.U (i p')) (M.g (i p) (i p'))).val * gs (𝟙 _) x (Q.q.left ⁻¹ᵁ V p') (f p') := by
  let α := {p : Q.B.left.Opens × M.ι // IsAffineOpen p.1 ∧ p.1 ≤ M.U p.2}
  have le : ∀ p : α, Q.q.left ⁻¹ᵁ p.1.1 ≤ (M.pull Q.q.left).U fun _ => p.1.2 := fun p _ k => mem_pull.2 (p.2.2 k)
  choose a ha hsum using fun p : α => (graded Q p.1.1 p.2.1).1
    ((G.left.presheaf.map (homOfLE (le p)).op).hom (s.f fun _ => p.1.2))
  have cov : ∀ y j, y ∈ M.U j → ∃ p : α, y ∈ p.1.1 ∧ p.1.2 = j := fun y j hj => by
    obtain ⟨W, hW, hy, hle⟩ := exists_isAffineOpen_mem_and_subset hj
    exact ⟨⟨(W, j), hW, hle⟩, hy, rfl⟩
  obtain ⟨J, hJ⟩ := hs
  obtain ⟨x, hx, hx0⟩ := exists_gs_ne_zero hJ
  obtain ⟨p₀, hp, e⟩ := cov _ _ (mem_pull.1 hx)
  obtain rfl : (fun _ => p₀.1.2) = J := funext fun _ => e
  have n : a p₀ ≠ 0 := fun k => hx0 (by
    rw [← gs_res (𝟙 _) x (le p₀) hp, hsum, k, Finsupp.sum_zero_index,
      LBGerm.gs_zero (𝟙 _) x (Q.q.left ⁻¹ᵁ p₀.1.1) hp])
  obtain ⟨χ, hχ⟩ := Finsupp.ne_iff.1 n
  refine ⟨χ, α, fun p => p.1.1, fun p => p.1.2, fun p => a p χ, fun p => p.2.2, fun y => ?_, fun p => ha p χ,
    ⟨p₀, hχ⟩, fun p p' x hx hx' => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart hM y
    exact (cov y j hj).imp fun _ k => k.1
  · rw [← gs_unit Q.q.left x (M.U p.1.2 ⊓ M.U p'.1.2) ⟨p.2.2 hx, p'.2.2 hx'⟩]
    refine comp_compat Q _ (inf_le_inf p.2.2 p'.2.2) _ _ (ha p) (ha p') (fun y hy hy' => ?_) χ x hx hx'
    rw [← hsum, ← hsum, gs_res (𝟙 _) y (le p) hy, gs_res (𝟙 _) y (le p') hy',
      gs_unit Q.q.left y (M.U p.1.2 ⊓ M.U p'.1.2) ⟨p.2.2 hy, p'.2.2 hy'⟩]
    refine (gs_compat s (𝟙 _) y (le p hy) (le p' hy')).trans ?_
    rw [gm_pull_g M Q.q.left (𝟙 _) y _ _ (le p hy) (le p' hy'), Category.id_comp]

theorem exists_sec_div [IsCommMonObj G] (M : LB Q.B.left) (hM : M.IsLB) (s : LB.Sec (M.pull Q.q.left))
    (hs : ∃ j, s.f j ≠ 0) : ∃ O : LB Q.B.left, O.IsLB ∧ (∃ u : LB.Gen (abelian₂ Q.B O), u.IsGen) ∧
      ∃ s : LB.Sec (LB.div M O), ∃ j, s.f j ≠ 0 := by
  have := Q.q_flat
  have := Q.q_surj
  obtain ⟨χ, α, V, i, f, hV, hc, hf, ⟨p₀, hp₀⟩, hff⟩ := exists_component Q M hM s hs
  obtain ⟨N, u, hN, hw, hu⟩ := WtBundle.exists_bundle Q χ
  refine ⟨N, hN, WtBundle.exists_gen_lam Q χ N hN u hw hu, ?_⟩
  have loc : ∀ p : α × N.ι, ∃ c : Γ(Q.B.left, V p.1 ⊓ N.U p.2), ∀ x, Q.q.left x ∈ V p.1 ⊓ N.U p.2 →
      gs Q.q.left x _ c = gs (𝟙 _) x (Q.q.left ⁻¹ᵁ V p.1) (f p.1) *
        (gm (𝟙 _) x (Q.q.left ⁻¹ᵁ N.U p.2) (u p.2))⁻¹.val := fun p => by
    have l₁ : Q.q.left ⁻¹ᵁ (V p.1 ⊓ N.U p.2) ≤ Q.q.left ⁻¹ᵁ V p.1 := fun _ k => k.1
    have l₂ : Q.q.left ⁻¹ᵁ (V p.1 ⊓ N.U p.2) ≤ Q.q.left ⁻¹ᵁ N.U p.2 := fun _ k => k.2
    have w := ((hf p.1).res l₁).mul ((hw p.2).inv.res l₂)
    rw [add_neg_cancel] at w
    obtain ⟨c, hc⟩ := exists_app_of_isWt Q _ _ w
    refine ⟨c, fun x hx => ?_⟩
    have e := gs_pull (𝟙 _) Q.q.left x _ hx c
    rw [Category.id_comp] at e
    rw [← e, hc, gs_mul (𝟙 _) x (Q.q.left ⁻¹ᵁ (V p.1 ⊓ N.U p.2)) hx, gs_res (𝟙 _) x l₁ hx, gs_res (𝟙 _) x l₂ hx,
      gs_unit (𝟙 _) x _ (l₂ hx), map_inv]
  choose c hc' using loc
  obtain ⟨σ, hσ⟩ := exists_sec_of_refinement (LB.isLB_div hM hN) (fun p : α × N.ι => V p.1 ⊓ N.U p.2)
    (fun p => (i p.1, p.2)) (fun p => inf_le_inf_right _ (hV p.1))
    (fun y => (hc y).elim fun p hp => (exists_chart hN y).elim fun k hk => ⟨(p, k), hp, hk⟩) c
    (fun y p p' hp hp' => by
      obtain ⟨x, rfl⟩ := Q.q.left.surjective y
      apply stalkMap_injective Q.q.left x
      have hm : Q.q.left x ∈ M.U (i p.1) ⊓ N.U p.2 ⊓ (M.U (i p'.1) ⊓ N.U p'.2) :=
        ⟨⟨hV _ hp.1, hp.2⟩, hV _ hp'.1, hp'.2⟩
      have e₁ := congrArg Units.val ((WtBundle.gm_stalkMap Q.q.left x (𝟙 _) _ hm
        ((LB.div M N).g (i p.1, p.2) (i p'.1, p'.2))).trans
        (gm_div N M (Q.q.left ≫ 𝟙 _) x (i p.1, p.2) (i p'.1, p'.2) hm))
      have e₂ := hu _ (𝟙 _) x p.2 p'.2 hp.2 hp'.2
      rw [Category.comp_id] at e₁
      rw [Category.id_comp] at e₂
      rw [map_mul, ← gs_stalkMap _ x _ hp, ← gs_stalkMap _ x _ hp', hc' p x hp, hc' p' x hp',
        hff _ _ x hp.1 hp'.1, e₂]
      refine Eq.trans ?_ (congrArg (· * _) e₁).symm
      simp only [mul_inv, Units.val_mul]
      ring)
  obtain ⟨x, hx, hx0⟩ := exists_gs_ne_zero hp₀
  obtain ⟨k, hk⟩ := exists_chart hN (Q.q.left x)
  have hm : Q.q.left x ∈ (LB.div M N).U (i p₀, k) := ⟨hV _ hx, hk⟩
  refine ⟨σ, (i p₀, k), fun h => hx0 ?_⟩
  have e := hσ _ (i p₀, k) (p₀, k) hm ⟨hx, hk⟩
  rw [h, LBGerm.gs_zero (𝟙 _) (Q.q.left x) _ hm, eq_comm, Units.mul_right_eq_zero] at e
  have e' := hc' (p₀, k) x ⟨hx, hk⟩
  rw [gs_stalkMap _ x _ (show _ ∈ V p₀ ⊓ N.U k from ⟨hx, hk⟩), e, map_zero, eq_comm, Units.mul_left_eq_zero] at e'
  exact e'

end GlobalTheory.WtSec

namespace GlobalTheory

theorem exists_sec_primitive_twist : GlobalFnsSt → ∀ (A : Type) [CommRing A] [IsLocalRing A] (X : Type) [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] (Q : TQ G X) (M : LB Q.B.left), M.IsLB → (∃ s : LB.Sec (M.pull Q.q.left), (∃ j, s.f j ≠ 0)) → ∃ O : LB Q.B.left, O.IsLB ∧ (∃ u : LB.Gen (abelian₂ Q.B O), u.IsGen) ∧ ∃ s : LB.Sec (LB.div M O), (∃ j, s.f j ≠ 0) :=
  fun _ _ _ _ _ _ _ _ _ Q M hM ⟨s, hs⟩ => WtSec.exists_sec_div Q M hM s hs

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemKernelOfLineBundleBaseChangeRepresentable
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem memKL_baseChange_rep : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (B : Over S) [GrpObj B] (L : LB B.left), L.IsLB → ∀ (H : Over S) (j : H ⟶ B), (∀ (T : Over S) (x : T ⟶ B), GlobalTheory.MemKL B L x ↔ ∃ z : T ⟶ H, z ≫ j = x) → ∀ (T' : Over S') (x : T' ⟶ (Over.pullback f).obj B), GlobalTheory.MemKL ((Over.pullback f).obj B) (L.pull (pullback.fst B.hom f)) x ↔ ∃ z : T' ⟶ (Over.pullback f).obj H, z ≫ (Over.pullback f).map j = x := by
  intro S S' f B _ L hL H j hrep T' x
  have h := isGrpPullback_pullback B f
  have hL' : (L.pull (pullback.fst B.hom f)).IsLB := LB.isLB_pull hL _
  rw [GlobalTheory.memKL_iff_memKL_push S S' f B _ _ L _ h hL hL' (GlobalTheory.lbIso_self hL') T' x, hrep]
  constructor
  · rintro ⟨z, hz⟩
    have hz' : z.left ≫ j.left = x.left ≫ pullback.fst B.hom f := congrArg (·.left) hz
    refine ⟨Over.homMk (pullback.lift z.left T'.hom (Over.w z)) (pullback.lift_snd _ _ _), ?_⟩
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w x).symm))
    rw [← hz']
    simp [pullback.lift_fst, pullback.lift_fst_assoc]
  · rintro ⟨z, rfl⟩
    refine ⟨Over.homMk (z.left ≫ pullback.fst H.hom f) ?_, ?_⟩
    · have := Over.w z
      simp only [Over.pullback_obj_hom] at this
      simp [pullback.condition, ← this]
    · refine Over.OverMorphism.ext ?_
      change (z.left ≫ pullback.fst H.hom f) ≫ j.left = (z.left ≫ ((Over.pullback f).map j).left) ≫ pullback.fst B.hom f
      simp [pullback.lift_fst]

end GlobalTheory
end

