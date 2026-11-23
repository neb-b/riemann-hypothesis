module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTangentGenericFibreOfThetaSections
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.GenericTan

section Charts

variable {R : Type} [CommRing R] [IsLocalRing R] {Z Z' : Scheme.{0}} {L : LB Z}

theorem valR_cocycle (hL : L.IsLB) (x : Sp R ⟶ Z) {i j k : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j)
    (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    valR x (L.U i ⊓ L.U j) (L.g i j).val * valR x (L.U j ⊓ L.U k) (L.g j k).val =
      valR x (L.U i ⊓ L.U k) (L.g i k).val := by
  apply toStkA_injective
  rw [map_mul, FormalValue.toStkA_valR_eq_gs x (L.U i ⊓ L.U j) _ (fun _ hz => ⟨hi hz, hj hz⟩) _, gs_unit x (cpt R) (L.U i ⊓ L.U j) ⟨hi trivial, hj trivial⟩ (L.g i j),
    FormalValue.toStkA_valR_eq_gs x (L.U j ⊓ L.U k) _ (fun _ hz => ⟨hj hz, hk hz⟩) _, gs_unit x (cpt R) (L.U j ⊓ L.U k) ⟨hj trivial, hk trivial⟩ (L.g j k),
    FormalValue.toStkA_valR_eq_gs x (L.U i ⊓ L.U k) _ (fun _ hz => ⟨hi hz, hk hz⟩) _, gs_unit x (cpt R) (L.U i ⊓ L.U k) ⟨hi trivial, hk trivial⟩ (L.g i k), ← Units.val_mul,
    gm_cocycle hL x _ (hi trivial) (hj trivial) (hk trivial)]

theorem valR_self (hL : L.IsLB) (x : Sp R ⟶ Z) {j : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valR x (L.U j ⊓ L.U j) (L.g j j).val = 1 := by
  apply toStkA_injective
  rw [FormalValue.toStkA_valR_eq_gs x (L.U j ⊓ L.U j) _ (fun _ hz => ⟨h hz, h hz⟩) _, gs_unit x (cpt R) (L.U j ⊓ L.U j) ⟨h trivial, h trivial⟩ (L.g j j), map_one]
  exact congrArg Units.val (gm_self hL x _ (h trivial))

theorem isFrm_spread (hL : L.IsLB) (x : Sp R ⟶ Z) {k : L.ι} (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) {a : R} (ha : IsUnit a) :
    IsFrm L x (fun j => valR x (L.U j ⊓ L.U k) (L.g j k).val * a) := by
  refine ⟨fun j hj => (FormalValue.isUnit_valR x (L.U j ⊓ L.U k) (fun _ hz => ⟨hj hz, hk hz⟩) _).mul ha,
    fun j j' h => ?_⟩
  rw [← _root_.mul_assoc, valR_cocycle hL x (fun _ hz => (h hz).1) (fun _ hz => (h hz).2) hk]

theorem sval_chart {p : Z' ⟶ Z} {m : ℕ} (s : SecP L p m) (q : Sp R ⟶ Z') {j k : L.ι}
    (hj : ⊤ ≤ (q ≫ p) ⁻¹ᵁ L.U j) (hk : ⊤ ≤ (q ≫ p) ⁻¹ᵁ L.U k) :
    ArcPts.sval s q j = valR (q ≫ p) (L.U j ⊓ L.U k) (L.g j k).val ^ m * ArcPts.sval s q k := by
  have wj : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j) :=
    fun z hz => Set.mem_iInter.2 fun _ => hj hz
  have wk : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => p) (fun _ => k) :=
    fun z hz => Set.mem_iInter.2 fun _ => hk hz
  apply toStkA_injective
  rw [map_mul, map_pow, FormalValue.toStkA_valR_eq_gs (q ≫ p) (L.U j ⊓ L.U k) _ (fun _ hz => ⟨hj hz, hk hz⟩) _, gs_unit (q ≫ p) (cpt R) (L.U j ⊓ L.U k) ⟨hj trivial, hk trivial⟩ (L.g j k)]
  refine (FormalValue.toStkA_valR_eq_gs q _ _ wj _).trans ((sec_trans s q _ (wj trivial) (wk trivial)).trans
    (congrArg₂ (· * ·) ?_ (FormalValue.toStkA_valR_eq_gs q _ _ wk _).symm))
  rw [trF, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]

theorem hasVal_of_chart {p : Z' ⟶ Z} {m : ℕ} (s : SecP L p m) (q : Sp R ⟶ Z') {τ : L.ι → R}
    (hτ : IsFrm L (q ≫ p) τ) {k : L.ι} (hk : ⊤ ≤ (q ≫ p) ⁻¹ᵁ L.U k) {r : R}
    (h : ArcPts.sval s q k = r * τ k ^ m) : HasVal s q τ r := fun j hj => by
  rw [sval_chart s q hj hk, h, hτ.2 j k (fun _ hz => ⟨hj hz, hk hz⟩), mul_pow, mul_left_comm]

def pullPow (p : Z' ⟶ Z) {m : ℕ} (σ : Out.H0 L m) : SecP L p m :=
  have l : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => p) j ≤ p ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 Z) j :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  { f := fun j => (p.appLE _ _ (l j)).hom (σ.f j)
    compat := fun (j j' : Fin 1 → L.ι) => fn_ext fun y hy => by
      have v : ∀ j : Fin 1 → L.ι, y ∈ LB.wchart L (fun _ : Fin 1 => p) j →
          gs (𝟙 Z') y _ ((p.appLE _ _ (l j)).hom (σ.f j)) =
          gs (𝟙 Z' ≫ p) y (LB.wchart L (fun _ : Fin 1 => 𝟙 Z) j) (σ.f j) := fun j hj =>
        (gs_res (𝟙 Z') y (l j) hj _).trans (gs_pull _ p y _ (l j hj) _)
      refine ((gs_res (𝟙 Z') y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Z') y _ hy _ _).trans
        (congrArg₂ (· * ·) ((gs_unit (𝟙 Z') y _ hy _).trans
          (congrArg Units.val (gm_linComb L _ _ (𝟙 Z') y j j' hy.1 hy.2)))
          ((gs_res (𝟙 Z') y _ hy _).trans (v j' hy.2)))).symm)
      rw [sec_trans σ (𝟙 Z' ≫ p) y (l j hy.1) (l j' hy.2)]
      simp only [trF, Category.comp_id] }

omit [IsLocalRing R] in
theorem sval_pullPow (p : Z' ⟶ Z) {m : ℕ} (σ : Out.H0 L m) (q : Sp R ⟶ Z') {k : L.ι}
    (hk : ⊤ ≤ (q ≫ p) ⁻¹ᵁ L.U k) : ArcPts.sval (pullPow p σ) q k =
      valR (q ≫ p) (LB.wchart L (fun _ : Fin 1 => 𝟙 Z) (fun _ => k)) (σ.f (fun _ => k)) :=
  HolHom.valR_appLE q p _ _ _ _ (fun z hz => Set.mem_iInter.2 fun _ => hk hz)

omit [IsLocalRing R] in
theorem le_powChart {x : Sp R ⟶ Z} {k : L.ι} (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 Z) (fun _ => k) :=
  fun _ hz => Set.mem_iInter.2 fun _ => hk hz

end Charts

theorem isTan_of_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (A : AnArc (𝓞 E)) (t : SAB H (Sp ℂ⟦X⟧)) (Φ : GenPts A t gen) (L : RigLB t.G) (x : A.V → (Sp ℂ⟦X⟧ ⟶ t.G.left)) (τ : A.V → L.L.ι → ℂ⟦X⟧) (z : A.V) (v : Sp (DualNumber ℂ⟦X⟧) ⟶ t.G.left) (k₀ : L.L.ι) (τ₁ : DualNumber ℂ⟦X⟧) (ρ : DualNumber ℂ⟦X⟧ →+* DualNumber ℂ⸨X⸩) (νK : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback t.G.hom gen), L = t.PP → (∀ u, (Φ.x u).left = gen ≫ x u ∧ ∀ (k : L.L.ι) (k' : t.PP.L.ι), HEq k k' → ⊤ ≤ x u ⁻¹ᵁ L.L.U k → Φ.τ u k' = algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (τ u k)) → spMap (TrivSqZeroExt.fstHom ℂ⟦X⟧ ℂ⟦X⟧ ℂ⟦X⟧).toRingHom ≫ v = x 0 → ⊤ ≤ v ⁻¹ᵁ L.L.U k₀ → IsUnit τ₁ → (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (algebraMap ℂ⟦X⟧ ℂ⸨X⸩ r)) → ρ DualNumber.eps = DualNumber.eps → νK ≫ pullback.fst _ _ = spMap ρ ≫ v → νK ≫ pullback.snd _ _ = spMap (algebraMap ℂ⸨X⸩ (DualNumber ℂ⸨X⸩)) → (∀ (j : ℕ) [NeZero j] (α : A.X), ∀ th ∈ A.Theta j α, ∀ F, IsDFSum A j α th z F → ∃ (m : ℕ) (σ : Out.H0 L.L j), (∀ u k, ⊤ ≤ x u ⁻¹ᵁ L.L.U k → algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (valR (x u) (LB.wchart L.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k)) (σ.f (fun _ => k))) = HahnSeries.single (m : ℤ) (1 : ℂ) * A.FSum j α th u * algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (τ u k) ^ j) ∧ ρ (valR v (LB.wchart L.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k₀)) (σ.f (fun _ => k₀))) = TrivSqZeroExt.inl (HahnSeries.single (m : ℤ) (1 : ℂ)) * (TrivSqZeroExt.inl (A.FSum j α th 0) + TrivSqZeroExt.inr F) * ρ τ₁ ^ j) → Φ.IsTan z νK := by
  intro E _ _ _ H _ A t Φ L x τ z v k₀ τ₁ ρ νK hL hx hv hk₀ hτ₁ hρ hε hfst hsnd hsec
  subst hL
  have hρ' := eq_dualMapR _ ρ hρ hε
  have hK : ⊤ ≤ (νK ≫ pullback.fst _ _) ⁻¹ᵁ t.PP.L.U k₀ := by
    rw [hfst]; exact FormalValue.top_le_comp hk₀ _
  haveI := isLocalRing_dual ℂ⸨X⸩
  have hfrm := isFrm_spread t.PP.isLB (νK ≫ pullback.fst _ _) hK (hτ₁.map ρ)
  refine ⟨hsnd, ?_, _, hfrm, fun j _ α th hth F hF => ?_⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hfst, fib, pullback.lift_fst, (hx 0).1, ← hv, ← Category.assoc, ← Category.assoc,
        ← Spec.map_comp, ← Spec.map_comp]
      congr 2
      ext1
      refine RingHom.ext fun a => ?_
      rw [hρ']
      exact fst_dualMapR _ a
    · rw [Category.assoc, hsnd, fib, pullback.lift_snd, ← Spec.map_comp, ← Spec.map_id]
      congr 1
  · obtain ⟨m, σ, h₁, h₂⟩ := hsec j α th hth F hF
    have key := sval_eq_sum_of_hasVal E H _ A t gen Φ j (pullPow (pullback.fst t.G.hom gen) σ) 1
      (fun _ => HahnSeries.single (m : ℤ) (1 : ℂ)) (fun _ => α) (fun _ => th) (fun _ => hth) (fun u => by
        have e : fib (Φ.x u) ≫ pullback.fst t.G.hom gen = gen ≫ x u := by
          rw [fib, pullback.lift_fst, (hx u).1]
        obtain ⟨k, hk⟩ := exists_chart t.PP.isLB (x u (cpt ℂ⟦X⟧))
        have hk' := (top_le_iff_cpt _ _).2 hk
        have hk'' : ⊤ ≤ (fib (Φ.x u) ≫ pullback.fst t.G.hom gen) ⁻¹ᵁ t.PP.L.U k := by
          rw [e]; exact FormalValue.top_le_comp hk' _
        refine hasVal_of_chart _ _ ?_ hk'' ?_
        · rw [e, ← (hx u).1]; exact Φ.frm u
        · rw [sval_pullPow _ _ _ hk'', e, Fin.sum_univ_one, (hx u).2 k k HEq.rfl hk', ← h₁ u k hk']
          exact FormalValue.valR_spMap _ _ _ (le_powChart hk') _)
      _ _ νK hsnd k₀ hK
    refine hasVal_of_chart _ _ hfrm hK ?_
    rw [sval_pullPow _ _ _ hK, hfst, Fin.sum_univ_one, TrivSqZeroExt.algebraMap_eq_inl] at key
    replace key := (h₂.symm.trans (FormalValue.valR_spMap ρ v _ (le_powChart hk₀) _).symm).trans key
    rw [_root_.mul_assoc] at key
    have hu : IsUnit (TrivSqZeroExt.inl (HahnSeries.single (m : ℤ) (1 : ℂ)) : DualNumber ℂ⸨X⸩) :=
      TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit (by simp))
    rw [valR_self t.PP.isLB _ hK, _root_.one_mul]
    exact (hu.mul_left_cancel key).symm

end GlobalTheory.GenericTan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecValMulGenVal
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstFamValues

open ConstThetaSections ConstFam

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] {b : O →+* ℂ} {a : ArcIn D l β ℂ b}


omit [IsScalarTower ℂ (FractionRing ℂ) ℂ] in
theorem ex_add_nsmul (Λ : GtAn a) (j : ℕ) (α mu : Λ.A.X) :
    Λ.u.ex (Λ.A.ct α + j • Λ.A.ct mu) = a.D₀.c (Λ.ε α + j • Λ.ε mu) := by
  rw [← map_nsmul, ← map_add (f := _), ← map_nsmul, ← map_add (f := _), Λ.ct]


omit [IsScalarTower ℂ (FractionRing ℂ) ℂ] in
theorem expo_eq (Λ : GtAn a) (j : ℕ) (α mu : Λ.A.X) : expo a j (Λ.ε α) (Λ.ε mu) = Λ.A.exponent j α mu := by
  rw [expo, AnArc.exponent, AnArc.q, Λ.be_eq, Λ.be_eq]

theorem secVal_mul_genVal (Λ : GtAn a) (j : ℕ) (α mu : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (v : Λ.A.V) :
    FrameValue.secVal Λ.u a.D₀.P.isLB (feTranslate a.D₀ j (Λ.ε mu) (Λ.ε α) s₀) (Λ.u.ex v.2).left
        ![v.2, v.2 + (Λ.A.ct α + j • Λ.A.ct mu), Λ.A.ct α + j • Λ.A.ct mu, 0] *
      FrameValue.genVal Λ.u a.D₀.P.isLB ((Λ.ex0 v).s (Λ.ε α + j • Λ.ε mu)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ))
        ![(Λ.A.ct α + j • Λ.A.ct mu) + v.2, Λ.A.ct α + j • Λ.A.ct mu, v.2, 0] =
      Λ.A.term j α (Λ.fn j α s₀) mu v := by
  have h₁ : ∀ y x z, x = Λ.ε y → z = Λ.A.ct y → FrameValue.genVal Λ.u a.D₀.P.isLB ((Λ.ex0 v).s x)
      (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![z + v.2, z, v.2, 0] = eTwoPi (v.1 y) := by
    rintro y _ _ rfl rfl
    exact Λ.arcDict_expZero_section v y
  have h₂ : ∀ y x z, x = Λ.ε y → z = Λ.A.ct y → FrameValue.genVal Λ.u a.D₀.P.isLB (a.D₀.psi x)
      (Out.jFK (R := ℂ) ℂ) (fun _ => z) = Λ.A.psi y := by
    rintro y _ _ rfl rfl
    exact Λ.psi y
  refine (congrArg₂ (· * ·) (secVal_feTranslate Λ.ah Λ.rig j (Λ.ct α) (Λ.ct mu) (Λ.psi α) (Λ.psi mu)
    (h₂ (mu + α) _ _ (map_add _ _ _).symm (map_add _ _ _).symm) s₀ v.2)
    (h₁ (α + j • mu) _ _ (by rw [map_add (f := _), map_nsmul]) (by rw [map_add (f := _), map_nsmul]))).trans ?_
  change Λ.fn j α s₀ (v.2 + Λ.A.ct mu) * _ * _ = _
  have n₁ := (Λ.A.psi mu).ne_zero
  have n₂ := (Λ.A.psi α).ne_zero
  simp only [AnArc.term, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Λ.A.psi_add]
  field_simp

end

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (hW : WitData a W.P.D W.P.oD W.φ W.he W.w W.e) (j : ℕ) [NeZero j] (α : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (m : ℕ) (f : ∀ x, ConstFam.SecBMod W.P.D.toPre j x) (σ : Out.H0 W.P.U.LG.L j), ConstFam.IsIntegralForm hW j (Λ.ε α) s₀ m f → (∀ n, W.P.U.toUnifPre.ExpandsAt n j σ f) → Ξ.Vals σ (fun v => HahnSeries.single (m : ℤ) (1 : ℂ) * Λ.A.FSum j α (Λ.fn j α s₀) v) := by
  intro _ _ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ hW j _ α s₀ m f σ hf hE v jL hL
  have hj : 1 ≤ j := Nat.one_le_iff_ne_zero.2 (NeZero.ne j)
  have hm : ∀ mu, 0 ≤ (m : ℤ) + Λ.A.exponent j α mu := fun mu => expo_eq Λ j α mu ▸ (hf.1 (Λ.ε mu)).1
  have hJ : (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = Ideal.span {PowerSeries.X} :=
    Ideal.map_id _
  have : IsAdicComplete ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) ℂ⟦X⟧ :=
    hJ.symm ▸ (admissibleBase_powerSeries ℂ).2.2.2
  have hb : (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.u.ex v.2).left :=
    ((Ξ.g_rel v 0).1 2).trans (congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) (Λ.ex0_b v))
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) (cpt ℂ⟦X⟧))
  replace hM := (top_le_iff_cpt (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) _).2 hM
  obtain ⟨j₀, h₀⟩ : ∃ j₀, ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ a.D₀.P.L.U j₀ := ⟨_, FrameValue.le_chartAt a.D₀.P.isLB _⟩
  have hd := ConstTerm.le_div (M := W.P.D.toPre.P.L) (φ := W.φ) (k := j₀) (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left)
    (hb ▸ FormalValue.top_le_comp h₀ _) hM
  have hτ := Ξ.τ_eq v jL jM j₀ hL hd
  have hu := FormalValue.isUnit_valR _ _ hd (W.w.s (fun _ => j₀, jM))
  choose jf jt hc using FormalValue.exists_cohCharts (Ξ.g v) jM hM
  have hs := exists_sum_sub_mem (i := fun mu => W.e (Λ.ε α + j • Λ.ε mu))
    (fun _ _ h => Λ.ε.injective (FamFree.add_nsmul_inj hj _ _ _ (W.e.injective h)))
    (n := fun mu => ((m : ℤ) + Λ.A.exponent j α mu).toNat)
    (c := fun mu => Λ.A.term j α (Λ.fn j α s₀) mu v * Λ.u.fr j₀ v.2 ^ j)
    (h := fun x => valR (A := ℂ⟦X⟧) (Ξ.g v).b.left _ (W.w.s (fun _ => j₀, jM)).val ^ j *
      (FormalValue.famVal (Ξ.g v) (f x) (jf x) * FormalValue.coordVal (Ξ.g v) x (jt x)))
    (fun mu => by
      rw [(hf.1 (Λ.ε mu)).2, ← secVal_mul_genVal, ← expo_eq]
      exact ConstTerm.core Λ.u (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) (PowerSeries.C (R := ℂ)) W.w (Ξ.g v) (Λ.ex0 v)
        (ex_add_nsmul Λ j α mu) (Λ.ex0_b v) (Ξ.g_rel v _) _ _ _
        (fun p => valR_smul_pullB hW j _ _ _ _ p _) jM j₀ _ _ (hc _) hd)
    (fun x hx => by
      have e : f x = 0 := hf.2 x fun mu h => hx (Λ.ε.symm (W.e.symm mu)) (by
        rw [Λ.ε.apply_symm_apply, map_add_nsmul, W.e.apply_symm_apply, h])
      have e' : FormalValue.famVal (Ξ.g v) (f x) (jf x) = 0 := by
        rw [e]
        exact (HolHom.valR_eq _ _ (hc x).1 _).trans (map_zero _)
      rw [e', zero_mul, mul_zero])
    (L := fun k => Λ.A.level j α ((k : ℤ) - m)) (fun k mu => by
      have := hm mu
      rw [AnArc.mem_level]
      omega)
  beta_reduce
  rw [← algebraMap_mk_eq Λ.A j α _ v hm, ← map_pow, ← map_mul]
  refine congrArg _ ((hu.pow j).mul_left_cancel (FormalValue.eq_of_forall_mk_eq
    ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) fun e => Ideal.Quotient.eq.2 ?_))
  obtain ⟨F, -, hF⟩ := ((FormalValue.value_eq_sum_expansion (admissibleBase_powerSeries ℂ) W.P.U (Ξ.g v) (Ξ.x v).left
    (Ξ.x_fm v)).2 j σ f hE).1 e
  obtain ⟨F', hFF, h₂⟩ := hs (e + 1) F
  have h₁ := hF F' jL jM jf jt hFF hL hM fun x _ => hc x
  have e₁ : (PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m),
      Λ.A.term j α (Λ.fn j α s₀) mu v * Λ.u.fr j₀ v.2 ^ j) =
      (PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m), Λ.A.term j α (Λ.fn j α s₀) mu v) *
        PowerSeries.C (Λ.u.fr j₀ v.2) ^ j := by
    ext k
    rw [← map_pow, PowerSeries.coeff_mul_C, PowerSeries.coeff_mk, PowerSeries.coeff_mk, Finset.sum_mul]
  rw [e₁, ← Finset.mul_sum, ← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow] at h₂
  replace h₂ := Ideal.pow_right_mono hJ.ge (e + 1) h₂
  have h₃ := congrArg (· ^ j) hτ
  simp only [mul_pow] at h₃
  convert add_mem (Ideal.mul_mem_left _ (valR (A := ℂ⟦X⟧) (Ξ.g v).b.left _ (W.w.s (fun _ => j₀, jM)).val ^ j) h₁)
    (Ideal.mul_mem_left _ ((FormalValue.tau W.P.U.toUnifPre ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map
      (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) (Ξ.x v).left jL jM).val ^ j) h₂) using 1
  linear_combination (-(PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m),
    Λ.A.term j α (Λ.fn j α s₀) mu v)) * h₃

end GlobalTheory.ConstFamValues
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SpecPtsNonempty
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts.Special

theorem exists_lift {Z Z' : Scheme.{0}} (x : Z' ⟶ Z) (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) :
    ∃ x' : Z' ⟶ W.toScheme, x' ≫ W.ι = x := by
  refine ⟨IsOpenImmersion.lift W.ι x ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨p, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact h (x := p) trivial

theorem le_comp {Z Z' Z'' : Scheme.{0}} (g : Z'' ⟶ Z') (x : Z' ⟶ Z) (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) :
    ⊤ ≤ (g ≫ x) ⁻¹ᵁ W := fun p _ => h (x := g p) trivial

theorem le_powOver {S Z' : Scheme.{0}} (G : Over S) (L : LB G.left) (U : S.Opens) (N : ℕ)
    (x : Z' ⟶ (G.hom ⁻¹ᵁ U).toScheme) (j : L.ι) (h : ⊤ ≤ (x ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j) :
    ⊤ ≤ x ⁻¹ᵁ (Out.powOver G L U N).U (fun _ => j) :=
  fun p _ => Set.mem_iInter.2 fun _ => h (x := p) trivial

theorem exists_chart {Z : Scheme.{0}} {K : Type} [Field K] (L : LB Z) (hL : L.IsLB) (x : Sp K ⟶ Z) :
    ∃ j, ⊤ ≤ x ⁻¹ᵁ L.U j := by
  have h : x (default : PrimeSpectrum K) ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  refine ⟨j, fun p _ => ?_⟩
  obtain rfl : p = (default : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
  exact hj

theorem exists_ext {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsSeparated G.hom] (L : LB G.left) (hL : L.IsLB)
    {R K : Type} [CommRing R] [IsLocalRing R] [Field K] (f : R →+* K) (hf : Function.Injective f)
    (y : Sp R ⟶ S) (x : Sp K ⟶ G.left) (hx : x ≫ G.hom = spMap f ≫ y) (τ : L.ι → K) (hτ : IsFrm L x τ)
    (U : S.Opens) (hU : IsAffineOpen U) (hyU : ⊤ ≤ y ⁻¹ᵁ U) {n : ℕ} (b : Fin n → LB.Sec (Out.powOver G L U 4))
    (hb : AmpleSpan.EmbedsBy (G.hom ∣_ U) b) (cf : Fin n → R) (hcf : ∃ i, IsUnit (cf i))
    (hv : ∀ i (x' : Sp K ⟶ (G.hom ⁻¹ᵁ U).toScheme) (j : L.ι), x' ≫ (G.hom ⁻¹ᵁ U).ι = x → ⊤ ≤ x ⁻¹ᵁ L.U j →
      valR x' ((Out.powOver G L U 4).U (fun _ => j)) ((b i).f (fun _ => j)) = f (cf i) * τ j ^ 4)
    (U' : S.Opens) (hyU' : ⊤ ≤ y ⁻¹ᵁ U') (b' : LB.Sec (Out.powOver G L U' 5)) (cf' : R) (hcf' : IsUnit cf')
    (hv' : ∀ (x' : Sp K ⟶ (G.hom ⁻¹ᵁ U').toScheme) (j : L.ι), x' ≫ (G.hom ⁻¹ᵁ U').ι = x → ⊤ ≤ x ⁻¹ᵁ L.U j →
      valR x' ((Out.powOver G L U' 5).U (fun _ => j)) (b'.f (fun _ => j)) = f cf' * τ j ^ 5) :
    ∃ (z : Sp R ⟶ G.left) (σ : L.ι → R), z ≫ G.hom = y ∧ spMap f ≫ z = x ∧ IsFrm L z σ ∧
      ∀ j, ⊤ ≤ z ⁻¹ᵁ L.U j → f (σ j) = τ j := by
  classical
  have hxU : ⊤ ≤ x ⁻¹ᵁ (G.hom ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, hx]
    exact le_comp _ _ _ hyU
  obtain ⟨x₁, hx₁⟩ := exists_lift x _ hxU
  obtain ⟨j₀, hj₀⟩ := exists_chart L hL x
  obtain ⟨u₀, hu₀⟩ := (hτ.1 j₀ hj₀).pow 4
  obtain ⟨z₁, ⟨hz₁, hz₂, hz₃⟩, -⟩ := _root_.GlobalTheory.LiftPoint.existsUnique_lift S G L U 4 n b R K f y x₁ cf j₀ u₀ hL hU hb hf hyU
    (by rw [← Category.assoc, hx₁, hx]) (by rw [hx₁]; exact hj₀)
    (fun i => by rw [hu₀]; exact hv i x₁ j₀ hx₁ hj₀) hcf
  have hz : spMap f ≫ z₁ ≫ (G.hom ⁻¹ᵁ U).ι = x := by rw [← Category.assoc, hz₂, hx₁]
  have hzy : (z₁ ≫ (G.hom ⁻¹ᵁ U).ι) ≫ G.hom = y := by rw [Category.assoc, hz₁]
  have hzU' : ⊤ ≤ (z₁ ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ (G.hom ⁻¹ᵁ U') := by
    rw [← Scheme.Hom.comp_preimage, hzy]
    exact hyU'
  obtain ⟨z₂, hz₄⟩ := exists_lift _ _ hzU'
  have key : ∀ j, ⊤ ≤ (z₁ ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → ∃ r : R, IsUnit r ∧ f r = τ j := by
    intro j hj
    have hxj : ⊤ ≤ x ⁻¹ᵁ L.U j := by rw [← hz]; exact le_comp _ _ _ hj
    obtain ⟨u, hu⟩ := hz₃ j hj
    obtain ⟨i, hi⟩ := hcf
    have h4 : f u = τ j ^ 4 := by
      have e := hv i x₁ j hx₁ hxj
      rw [← hz₂, HolHom.valR_spMap _ _ _ (le_powOver G L U 4 z₁ j hj), hu, map_mul] at e
      exact mul_left_cancel₀ (hi.map f).ne_zero e
    have e := hv' (spMap f ≫ z₂) j (by rw [Category.assoc, hz₄, hz]) hxj
    rw [HolHom.valR_spMap _ _ _ (le_powOver G L U' 5 z₂ j (by rw [hz₄]; exact hj))] at e
    obtain ⟨c, rfl⟩ := hcf'
    set a := valR z₂ ((Out.powOver G L U' 5).U (fun _ => j)) (b'.f (fun _ => j))
    have hc : f (↑c⁻¹ : R) * f c = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    have hu' : f (↑u⁻¹ : R) * f u = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    have hr : f (↑c⁻¹ * ↑u⁻¹ * a) = τ j := by
      rw [map_mul, map_mul, e]
      rw [h4] at hu'
      linear_combination (f (↑u⁻¹ : R) * τ j ^ 5) * hc + τ j * hu'
    refine ⟨_, ?_, hr⟩
    have : (↑c⁻¹ * ↑u⁻¹ * a) ^ 4 = (u : R) := hf (by rw [map_pow, hr, h4])
    exact (isUnit_pow_iff (by norm_num : 4 ≠ 0)).1 (this ▸ u.isUnit)
  choose! σ hσ using key
  refine ⟨z₁ ≫ (G.hom ⁻¹ᵁ U).ι, σ, hzy, hz, ⟨fun j hj => (hσ j hj).1, fun j j' hj => hf ?_⟩,
    fun j hj => (hσ j hj).2⟩
  have h1 := hj.trans (Scheme.Hom.preimage_mono _ (inf_le_left : L.U j ⊓ L.U j' ≤ _))
  have h2 := hj.trans (Scheme.Hom.preimage_mono _ (inf_le_right : L.U j ⊓ L.U j' ≤ _))
  rw [map_mul, (hσ j h1).2, (hσ j' h2).2, ← HolHom.valR_spMap _ _ _ hj, hz]
  exact hτ.2 j j' (by rw [← hz]; exact le_comp _ _ _ hj)

theorem germs_local (Γ : Germs) (w : ℂ) : IsLocalRing (Γ.R w) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    by_cases h : Γ.ev w a = 0
    · exact Or.inr (Γ.unit w _ (by rw [map_sub, h, map_one, sub_zero]; exact one_ne_zero))
    · exact Or.inl (Γ.unit w _ h)

theorem specPts_nonempty : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (k : Type) [CommRing k] (s₀ : S ⟶ Sp k) [LocallyOfFiniteType s₀] (b₀ : k →+* ℂ), y ≫ s₀ = spMap ((algebraMap ℂ ℂ⸨X⸩).comp b₀) → AnFin A → Φ.Rational → Nonempty (SpecPts Φ Γ) := by
  intro h1 h2 E _ _ _ H _ D l B _ bb S _ s o A y Φ Γ k _ s₀ _ b₀ hy hA hΦ
  classical
  obtain ⟨C⟩ := _root_.GlobalTheory.SpanFrame.nonempty_coords h1 h2 E H D l B bb S s o A y Φ hA hΦ 4 le_rfl
  obtain ⟨C'⟩ := _root_.GlobalTheory.SpanFrame.nonempty_coords h1 h2 E H D l B bb S s o A y Φ hA hΦ 5 (by norm_num)
  haveI := o.proper
  obtain ⟨x₀, hx₀⟩ := hΦ.1 0
  have hy₀ : spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) ≫ x₀ ≫ o.t.G.hom = y := by
    rw [← Category.assoc, hx₀]
    exact Over.w (Φ.x 0)
  set y₀ := x₀ ≫ o.t.G.hom
  have hin : ∀ U : S.Opens, ⊤ ≤ y ⁻¹ᵁ U → ⊤ ≤ y₀ ⁻¹ᵁ U := by
    intro U hU p _
    rw [← hy₀] at hU
    obtain rfl : p = spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) (default : PrimeSpectrum ℂ⸨X⸩) :=
      Subsingleton.elim (α := PrimeSpectrum Conv.convLaurent) _ _
    exact hU (x := (default : PrimeSpectrum ℂ⸨X⸩)) trivial
  have hs₀ : y₀ ≫ s₀ = spMap ((algebraMap ℂ Conv.convLaurent).comp b₀) := by
    refine HolHom.point_ext (isAffineOpen_top _) le_top le_top fun g => Subtype.ext ?_
    have e1 := HolHom.valR_spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) (y₀ ≫ s₀) ⊤ le_top g
    have e2 := HolHom.valR_spMap (algebraMap Conv.convLaurent ℂ⸨X⸩)
      (spMap ((algebraMap ℂ Conv.convLaurent).comp b₀)) ⊤ le_top g
    rw [← Category.assoc, hy₀, hy] at e1
    rw [← spMap_comp] at e2
    exact e1.symm.trans e2
  obtain ⟨T₁, hT₁, y₁, hy₁U, hy₁, -⟩ :=
    Conv.exists_halfRing_point s₀ b₀ y₀ hs₀ C.aff (hin _ C.mem) (max C.T C'.T)
  obtain ⟨T, hT, hU'⟩ := Conv.exists_le_preimage_inclusion y₁ (U := C'.U) (by rw [hy₁]; exact hin _ C'.mem)
  set yT := spMap (Subalgebra.inclusion (Conv.halfRing_mono hT) : Conv.halfRing T₁ →+* Conv.halfRing T) ≫ y₁ with hyT
  have hU : ⊤ ≤ yT ⁻¹ᵁ C.U := le_comp _ _ _ hy₁U
  have hgen : spMap (Conv.halfRing T).val.toRingHom ≫ yT = y := by
    rw [← hy₀, ← hy₁, hyT, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    rfl
  have hC : C.T ≤ T := ((le_max_left _ _).trans hT₁).trans hT
  have hC' : C'.T ≤ T := ((le_max_right _ _).trans hT₁).trans hT
  have key : ∀ (w : ℂ) (hw : T < w.im) (v : A.V), ∃ (z : Sp (Γ.R w) ⟶ o.t.G.left) (σ : o.t.PP.L.ι → Γ.R w),
      z ≫ o.t.G.hom = spMap (Subalgebra.inclusion (Γ.le T w hw)).toRingHom ≫ yT ∧
      spMap (Γ.R w).val.toRingHom ≫ z = (Φ.x v).left ∧ IsFrm o.t.PP.L z σ ∧
      ∀ j, ⊤ ≤ z ⁻¹ᵁ o.t.PP.L.U j → (Γ.R w).val.toRingHom (σ j) = Φ.τ v j := by
    intro w hw v
    haveI := germs_local Γ w
    have hw₁ := hC.trans_lt hw
    have hw₂ := hC'.trans_lt hw
    obtain ⟨i, hi⟩ := C.bpf w hw₁ v
    obtain ⟨i', hi'⟩ := C'.bpf w hw₂ v
    refine exists_ext o.t.G o.t.PP.L o.t.PP.isLB (Γ.R w).val.toRingHom Subtype.val_injective _ (Φ.x v).left ?_
      (Φ.τ v) (Φ.frm v) C.U C.aff (le_comp _ _ _ hU) C.b C.emb
      (fun i => Subalgebra.inclusion (Γ.le _ w hw₁) (C.cf i v)) ⟨i, Γ.unit w _ (by rw [Γ.ev_eq]; exact hi)⟩
      (fun i x' j => C.val i v x' j) C'.U (le_comp _ _ _ hU') (C'.b i')
      (Subalgebra.inclusion (Γ.le _ w hw₂) (C'.cf i' v)) (Γ.unit w _ (by rw [Γ.ev_eq]; exact hi'))
      (fun x' j => C'.val i' v x' j)
    rw [← Category.assoc, ← spMap_comp]
    exact (Over.w (Φ.x v)).trans hgen.symm
  choose z σ hz1 hz2 hz3 hz4 using key
  have hpi : ∀ (w : ℂ) (hw : T < w.im) (v : A.V),
      (spMap (Γ.ev w).toRingHom ≫ z w hw v) ≫ o.t.G.hom = Conv.halfCurve yT w := by
    intro w hw v
    rw [Category.assoc, hz1, ← Category.assoc, ← spMap_comp, Conv.halfCurve_eq yT hw]
    congr 2
    exact RingHom.ext fun r => Γ.ev_eq T w hw r
  exact ⟨{
    T := T
    yT := yT
    yT_gen := hgen
    xt := fun w hw v => Over.homMk (z w hw v) (hz1 w hw v)
    xt_gen := hz2
    τt := fun w v => if hw : T < w.im then σ w hw v else fun _ => 1
    τt_frm := fun w hw v => by rw [dite_eq_left hw]; exact hz3 w hw v
    τt_gen := fun w hw v j hj => by rw [dite_eq_left hw]; exact hz4 w hw v j hj
    yw := Conv.halfCurve yT
    yw_eq := fun w hw => Conv.halfCurve_eq yT hw
    pi := fun w v => if hw : T < w.im then Over.homMk (spMap (Γ.ev w).toRingHom ≫ z w hw v) (hpi w hw v) else 1
    pi_eq := fun w hw v => by rw [dite_eq_left hw]; rfl }⟩

end GlobalTheory.ArcPts.Special
end
end

