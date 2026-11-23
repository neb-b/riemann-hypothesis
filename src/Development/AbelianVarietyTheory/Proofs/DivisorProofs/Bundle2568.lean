module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2481
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2063
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2424
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordLambdaBilinearIntegralCombinations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0168
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTensorPosDefFormPositive
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBaseMatchingMonomialsRatioUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj.PerUnit

theorem dataFrom_ofDeg {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V]
    (T : TautBase o W) (ω : W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ))
    (n : ℕ) (D : DegPre V) (hB : D.TauBimult) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left)
    (β₂ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull β₂))
    (h : From T ω s ε n D e β β₂ w) : DataFrom T ω s ε n (GlobalTheory.PolDeg.Wit.ofDeg D hB) e := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨β, β₂, w, h₁, h₂, h₃, h₄, fun a b => ?_⟩
  obtain ⟨k, hk, hv⟩ := h₅ a b
  exact ⟨k, hk, fun z J J' hJ hJ' => ((GlobalTheory.PolDeg.Wit.exists_tau D a b).choose_spec.2 _ (𝟙 _) z J' hJ').trans (hv z J J' hJ hJ')⟩

theorem exists_good_closed {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (z : (TK V).left) :
    ∃ J : ((TK V).left ⟶ D.P.A.left) → D.P.L.ι, Good D.P.L z J ∧
      ∀ e : Sp V ⟶ D.P.A.left, e (closedPoint V) ∈ D.P.L.U (J ((TK V).hom ≫ e)) := by
  classical
  haveI : IsDominant (jK V) := ReciprocityTheory.ChartRestriction.G.DVR.isDominant_jK
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  haveI : D.P.A.left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from D.P.A.hom]; infer_instance
  have hinj : ∀ e e' : Sp V ⟶ D.P.A.left, (TK V).hom ≫ e = (TK V).hom ≫ e' → e = e' :=
    fun e e' h => ext_of_isDominant (jK V) h
  have hsp : ∀ (e : Sp V ⟶ D.P.A.left) (p : Sp V) (i : D.P.L.ι), e (closedPoint V) ∈ D.P.L.U i → e p ∈ D.P.L.U i :=
    fun e p i h => (((PrimeSpectrum.le_iff_specializes p (closedPoint V)).1
      (IsLocalRing.le_maximalIdeal p.2.ne_top)).map e.continuous).mem_open (D.P.L.U i).isOpen h
  choose pick hpick using exists_chart D.P.isLB
  refine ⟨fun ψ => if h : ∃ e : Sp V ⟶ D.P.A.left, (TK V).hom ≫ e = ψ then pick (h.choose (closedPoint V))
    else pick (ψ z), fun ψ => ?_, fun e => ?_⟩
  · by_cases h : ∃ e : Sp V ⟶ D.P.A.left, (TK V).hom ≫ e = ψ
    · simp only [dif_pos h]
      have e1 : ψ z = ((TK V).hom ≫ h.choose) z :=
        (congrArg (fun q : (TK V).left ⟶ D.P.A.left => q z) h.choose_spec).symm
      rw [e1]
      exact hsp _ _ _ (hpick _)
    · simp only [dif_neg h]
      exact hpick _
  · have h : ∃ e' : Sp V ⟶ D.P.A.left, (TK V).hom ≫ e' = (TK V).hom ≫ e := ⟨e, rfl⟩
    simp only [dif_pos h]
    rw [hinj _ _ h.choose_spec]
    exact hpick _

theorem val_closed {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {X Y : Scheme.{0}} {L : LB X} {K : Type}
    [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (y : Sp V ⟶ Y) (z : (TK V).left)
    (J : ((TK V).left ⟶ X) → L.ι) (hJ : ∀ k, (y ≫ φ k) (closedPoint V) ∈ L.U (J ((TK V).hom ≫ y ≫ φ k))) :
    ∃ w : Vˣ, val t ((TK V).hom ≫ y) z J =
      gm (𝟙 (TK V).left) z ⊤ (unitOn (Units.map (algebraMap V (FractionRing V) : V →* FractionRing V) w)) := by
  have hall : ∀ p : Sp V, y p ∈ LB.wchart L φ (fun k => J (((TK V).hom ≫ y) ≫ φ k)) := by
    intro p
    refine Set.mem_iInter.2 fun k => ?_
    have hsp : p ⤳ closedPoint V :=
      (PrimeSpectrum.le_iff_specializes p (closedPoint V)).1 (IsLocalRing.le_maximalIdeal p.2.ne_top)
    have hm := hJ k
    rw [← Category.assoc] at hm
    exact hsp.map (y ≫ φ k).continuous |>.mem_open (L.U _).isOpen hm
  have hU : y ⁻¹ᵁ LB.wchart L φ (fun k => J (((TK V).hom ≫ y) ≫ φ k)) = ⊤ := top_unique fun p _ => hall p
  have key : ∀ (U : (Sp V).Opens) (_ : U = ⊤) (a : Γ(Sp V, U)ˣ), ∃ w : Vˣ,
      gm (TK V).hom z U a = gm (TK V).hom z ⊤ (unitOn w) := by
    rintro U rfl a
    refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom a, congrArg _ (Units.ext ?_)⟩
    show a.val = (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom a.val)
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  obtain ⟨w, hw⟩ := key _ hU (pullU y _ (t.s (fun k => J (((TK V).hom ≫ y) ≫ φ k))))
  refine ⟨w, ?_⟩
  have q : (toUnit (TK V)).left = (TK V).hom := by simp
  rw [← GlobalTheory.PolDeg.Taut.gm_jK_unitOn, q, ← hw]
  exact (gm_pull (TK V).hom y z _ (hall _) _).symm

end GlobalTheory.TInj.PerUnit

namespace GlobalTheory.TInj.PerUnit


set_option maxHeartbeats 2000000 in
theorem monomial_ratio_unit : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D₁ D₂ : DegPre V) (ω₁ : W →+* V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (ω₂ : W →+* V) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → Match D₁ D₂ b φ F → ∀ y y' : D₁.X, ∃ u : Vˣ, ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (e₂ (φ y)) (e₂ (φ y'))) = algebraMap V (FractionRing V) u * ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (e₁ y) (e₁ y')) := by
  intro o W _ _ _ T I _ ε n V _ _ _ D₁ D₂ ω₁ s₁ e₁ β₁ ββ₁ w₁ ω₂ s₂ e₂ β₂ ββ₂ w₂ b φ F _ _ hB₁ hB₂ f₁ f₂ m y y'
  obtain ⟨k₁, hk₁, U₁, -, hU₁⟩ := GlobalTheory.T.tautologicalBase_periods_factor_mul_generator T ω₁ s₁ ε n (GlobalTheory.PolDeg.Wit.ofDeg D₁ hB₁) e₁
    (dataFrom_ofDeg T ω₁ s₁ ε n D₁ hB₁ e₁ β₁ ββ₁ w₁ f₁) y (φ.symm.toAddMonoidHom (φ y'))
  obtain ⟨k₂, hk₂, U₂, -, hU₂⟩ := GlobalTheory.T.tautologicalBase_periods_factor_mul_generator T ω₂ s₂ ε n (GlobalTheory.PolDeg.Wit.ofDeg D₂ hB₂) e₂
    (dataFrom_ofDeg T ω₂ s₂ ε n D₂ hB₂ e₂ β₂ ββ₂ w₂ f₂) (φ y) (φ y')
  obtain ⟨g, hg⟩ := GlobalTheory.TorusExt.exists_iota (F := F) hB₁ y
  obtain ⟨g', ha, hg'⟩ := m.2.2.2.2 y g hg
  obtain ⟨u, hu⟩ := m.2.2.2.1 (φ y')
  let z : (TK V).left := closedPoint (FractionRing V)
  obtain ⟨J₁, gJ₁, cJ₁⟩ := exists_good_closed D₁ z
  obtain ⟨J₂, gJ₂, cJ₂⟩ := exists_good_closed D₂ z
  obtain ⟨J, hJ, hl, hr⟩ := exists_good_join D₁.P.isLB D₂.P.isLB gJ₁ gJ₂
  have key := act_val_frac V D₂ D₁ b φ.symm.toAddMonoidHom F y (φ y) g g' hg hg' ha (φ y') u hu z J hJ
  have t₁ := ((GlobalTheory.PolDeg.Wit.exists_tau D₁ y (φ.symm.toAddMonoidHom (φ y'))).choose_spec.2 _ (𝟙 _) z (rl J)
    ((isPart_inl _ _).good hJ)).symm.trans (hU₁ z (rl J) ((isPart_inl _ _).good hJ))
  have t₂ := ((GlobalTheory.PolDeg.Wit.exists_tau D₂ (φ y) (φ y')).choose_spec.2 _ (𝟙 _) z (rr J)
    ((isPart_inr _ _).good hJ)).symm.trans (hU₂ z (rr J) ((isPart_inr _ _).good hJ))
  obtain ⟨v₁, hv₁⟩ := val_closed U₁ (𝟙 _) z (rl J) (fun k => by erw [hl]; exact cJ₁ _)
  obtain ⟨v₂, hv₂⟩ := val_closed U₂ (𝟙 _) z (rr J) (fun k => by erw [hr]; exact cJ₂ _)
  obtain ⟨v₃, hv₃⟩ := val_closed u (D₁.c y).left z J (fun k => by
    rcases k with k | k
    · have h1 := cJ₁ ((D₁.c y).left ≫ D₁.Oφ (𝟙 _) (φ.symm.toAddMonoidHom (φ y')) k)
      erw [← hl] at h1
      have h2 := ((isPart_inl D₁.P.L D₂.P.L).mem _ _).2 h1
      simp only [Sum.elim_inl, Category.assoc] at h2 ⊢
      exact h2
    · have h1 := cJ₂ ((D₁.c y).left ≫ D₂.Oφ b (φ y') k)
      erw [← hr] at h1
      have h2 := ((isPart_inr D₁.P.L D₂.P.L).mem _ _).2 h1
      simp only [Sum.elim_inr, Category.assoc] at h2 ⊢
      exact h2)
  have q₁ : (toUnit (TK V)).left = (TK V).hom ≫ 𝟙 (Sp V) := by simp
  have q₃ : ptK (D₁.c y) = (TK V).hom ≫ (D₁.c y).left := by simp [ptK]
  rw [← q₁] at hv₁ hv₂
  rw [← q₃] at hv₃
  have um : ∀ a c : (FractionRing V)ˣ, unitOn (a * c) = unitOn a * unitOn c := fun a c => map_mul _ a c
  have E : gm (𝟙 (TK V).left) z ⊤ (unitOn (k₂ * Units.map (algebraMap V (FractionRing V) : V →* FractionRing V) v₂)) =
      gm (𝟙 (TK V).left) z ⊤ (unitOn (k₁ * Units.map (algebraMap V (FractionRing V) : V →* FractionRing V) v₁ *
        Units.map (algebraMap V (FractionRing V) : V →* FractionRing V) v₃)) := by
    rw [um, um, um, map_mul, map_mul, map_mul, ← hv₁, ← hv₂, ← hv₃, ← t₂, ← t₁]
    exact key
  have inj := GlobalTheory.DefectHom.gm_unitOn_inj z E
  have hc := congrArg (fun x : (FractionRing V)ˣ => (x : FractionRing V)) inj
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at hc
  have hk₁' : (k₁ : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (e₁ y) (e₁ y')) := by
    have h' : (k₁ : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (e₁ y) (e₁ (φ.symm (φ y')))) := by
      exact hk₁
    rw [h', φ.symm_apply_apply]
  have hk₂' : (k₂ : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (e₂ (φ y)) (e₂ (φ y'))) := by
    exact hk₂
  refine ⟨v₁ * v₃ * v₂⁻¹, ?_⟩
  rw [← hk₂', ← hk₁']
  have hv2 : algebraMap V (FractionRing V) (v₂ : V) * algebraMap V (FractionRing V) ((v₂⁻¹ : Vˣ) : V) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  simp only [Units.val_mul, map_mul]
  linear_combination (-(k₂ : FractionRing V)) * hv2 + algebraMap V (FractionRing V) ((v₂⁻¹ : Vˣ) : V) * hc

end GlobalTheory.TInj.PerUnit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataFactorPairingPullback
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensPair

theorem pair_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W), (∃ w₁ : LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) (LB.LinComb D.toPre.P.L (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2) (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2)), w₁.IsGen ∧ ∀ (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = gm (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z _ (w₁.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2), fun I => J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))) * ∏ i, ∏ j, val (D.toPre.tau (T.xe a i) (T.xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j)) → ∀ (i₀ : Fin r), letI := T.mod (symUnitOf W h); ∃ w : LB.Iso (abelian₂ D.toPre.P.A D.toPre.P.L) ((abelian₂ D'.toPre.P.A D'.toPre.P.L).pull (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left), w.IsGen ∧ ∀ a b z J J', Good D'.toPre.P.L z J → Good D.toPre.P.L z J' → val (D.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b)).left z J J' * val (D'.toPre.tau (T.xi i₀ a) (TensO.binv (symUnitOf W h) • T.xi i₀ b)) (𝟙 _) z J := by
  intro R _ _ _ _ D D' r W h _ T hw i₀
  obtain ⟨w₁, hw₁, hv₁⟩ := hw
  have hsum : ∑ j, (W + W.transpose) i₀ j * TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀ = 1 := by
    have hb : (((symUnitOf W h).1 : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) = W + W.transpose :=
      IsUnit.unit_spec _
    have key := congrFun (congrFun (Units.mul_inv (symUnitOf W h).1) i₀) i₀
    rw [hb, Matrix.mul_apply, Matrix.one_apply_eq] at key
    exact key
  obtain ⟨u₀, hu₀, hv₀⟩ := _root_.GlobalTheory.Mum.LamComb.exists_gen_lam_comb D.toPre D.tau_bimult (fun j => (W + W.transpose) i₀ j)
    (fun j => TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀) hsum
  obtain ⟨u, hu, hvu⟩ := exists_gen D.toPre.P.isLB
    (φ' := Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left ≫ GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2) (fun I : ULift (Finset (Fin 2)) => (psum D.toPre.P.A (x2 D.toPre.P.A) I.down).left))
    (ε' := Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => (W + W.transpose) k.1.1 k.1.2 * Oε k.2) (fun I : ULift (Finset (Fin 2)) => -((-1) ^ (2 - I.down.card))))
    (fun U _ hh => by
      clear hv₀ hv₁ hu₀ u₀ hw₁ w₁
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      refine congrArg (· * _) ?_
      simp only [Sum.elim_inl, GlobalTheory.TensPair.lamPts_pull, Fintype.prod_prod_type]
      symm
      rw [Finset.prod_eq_single i₀ ?_ (by simp)]
      · exact Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun l _ => by rw [if_pos rfl]
      · intro i _ hi
        refine Finset.prod_eq_one fun j _ => ?_
        rw [Fin.prod_univ_four, if_neg hi]
        simp only [GlobalTheory.PolDeg.lamPts, Oε, _root_.one_mul]
        simp [zpow_mul, zpow_neg]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow, ofMul_one]
        module)
    u₀ hu₀
  obtain ⟨w, hw, hvw⟩ := _root_.GlobalTheory.Mum.iso_linComb_pull_glue D.toPre.P.isLB (LB.isLB_linComb D'.toPre.P.isLB _ _) _ _ _ _ _ w₁ hw₁ u hu
  refine ⟨w, hw, fun a b z J J' hJ hJ' => ?_⟩

  suffices key : ∀ b' : D'.toPre.X, (∀ j, T.xe b' j = TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀ • b) →
      val (D.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left z J J' *
        val (D'.toPre.tau (T.xi i₀ a) b') (𝟙 _) z J by
    exact key _ (fun j => (Tens.xe_smul T (symUnitOf W h) (TensO.binv _) (T.xi i₀ b) j).trans (by
      rw [Finset.sum_eq_single i₀ (fun k _ hk => by rw [GlobalTheory.TensPair.xe_xi, if_neg hk, smul_zero]) (by simp),
        GlobalTheory.TensPair.xe_xi, if_pos rfl]))
  intro b' hb'
  have hPl : (lift (toUnit (TK R) ≫ D'.toPre.c (T.xi i₀ a)) (toUnit (TK R) ≫ D'.toPre.c b') : TK R ⟶ G2 D'.toPre.P.A).left =
      (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫
        (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left := by
    rw [GlobalTheory.TensPair.pt_pull T i₀ _ a b _ b' (GlobalTheory.TensPair.xe_xi T i₀ · a) hb']; rfl
  have t0 : ∀ x, val (D.toPre.tau 0 x) (𝟙 _) z J' = 1 := fun x => by
    have e := GlobalTheory.TauTwist.val_tau_nsmul (𝟙 (TK R)) hJ' D.tau_bimult 0 x x
    rw [zero_smul] at e
    simpa [cubN] using e
  have hPi : ∏ i, ∏ j, val (D.toPre.tau (T.xe (T.xi i₀ a) i) (T.xe b' j)) (𝟙 _) z J' ^ ((W + W.transpose) i j) =
      ∏ j, val (D.toPre.tau a (TensO.mat _ (TensO.binv (symUnitOf W h)) j i₀ • b)) (𝟙 _) z J' ^ ((W + W.transpose) i₀ j) := by
    rw [Finset.prod_eq_single i₀ (fun i _ hi => Finset.prod_eq_one fun j _ => by
      rw [GlobalTheory.TensPair.xe_xi, if_neg hi, t0, one_zpow]) (by simp)]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [GlobalTheory.TensPair.xe_xi, if_pos rfl, hb']
  have e1 := hv₁ (T.xi i₀ a) b' z J' J hJ' hJ
  rw [hPi, hPl] at e1
  have e2 := hvw _ (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left z J' hJ'
    (fun I => J (((lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫
        (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left) ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))
    (hJ.mem _ _)
  have e3 := hv₀ a b z J' hJ'
  have e4 := hvu _ (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left z J' hJ'
  clear hv₀ hvu hvw hv₁ hPi
  change val _ _ z J = gv w₁ _ z _ _ * _ at e1
  have hj : (fun I : ULift (Finset (Fin 2)) => J ((lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫ (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left)) =
      (fun I => J (((lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫ (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left) ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left)) :=
    funext fun I => by rw [Category.assoc]
  have e5 : GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left z J J' = gw w (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left z (fun I : ULift (Finset (Fin 2)) => J ((lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫ (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))
      (fun I => J' ((lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b) : TK R ⟶ G2 D.toPre.P.A).left ≫ (psum D.toPre.P.A (x2 D.toPre.P.A) I.down).left)) := rfl
  rw [e5, hj, e2, e1, e3, e4]
  have key : ∀ {G : Type} [CommGroup G] (A P X : G), A * P = X⁻¹ * A * (X * P) := fun A P X => by
    rw [_root_.mul_comm X⁻¹ A, _root_.mul_assoc, inv_mul_cancel_left]
  exact key (G := ((TK R).left.presheaf.stalk z)ˣ) _ _ _

end GlobalTheory.TensPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataMumfordSideGeneratorValues
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumSide

open GlobalTheory.TensAct

section Main

theorem mside : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D' W) (A : Matrix (Fin r) (Fin r) ℤ) (f : D'.P.A ⟶ D'.P.A), f = GlobalTheory.TensAct.matAct T A → W = (W + W.transpose) * A → ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun p : Fin 4 × ((Fin r × Fin r) × Fin 4) => (![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left, (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) p.1 ≫ tensφ T.pr p.2) (fun p => (![1, -2, -1, 2] : Fin 4 → ℤ) p.1 * tensε W p.2)), t.IsGen ∧ ∀ (y : D'.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → val t (D'.xK y) z J = ∏ a : Fin 4, (∏ i, ∏ j, val (D.toPre.tau (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) a) i) (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) a) j)) (𝟙 _) z J ^ W i j) ^ (-(![1, -2, -1, 2] : Fin 4 → ℤ) a) := by
  intro R _ _ I D D' r W T A f hf hW
  classical
  let M : Fin 4 → Matrix (Fin r) (Fin r) ℤ := ![1 + A, 1, A, 0]
  let e : Fin 4 → ℤ := ![1, -2, -1, 2]
  let E : Fin 4 × (Fin r × Fin r) → ℤ := fun q => e q.1 * W q.2.1 q.2.2
  have hB := fun q : Fin 4 × (Fin r × Fin r) => _root_.GlobalTheory.MumBil.lam_bilin R I D D'.P.A T.pr (M q.1 q.2.1) (M q.1 q.2.2)
  choose t ht hv using hB
  have hP := fun q : Fin 4 × (Fin r × Fin r) => exists_zpow D.toPre.P.isLB (t q) (ht q) (E q)
  choose s hs hsv using hP
  have hpr : ∀ (a : Fin 4) (i : Fin r), GlobalTheory.TensAct.matAct T (M a) ≫ T.pr i = ∏ k, T.pr k ^ M a i k :=
    fun a i => GlobalTheory.TensAct.matAct_pr T (M a) i
  obtain ⟨t', ht', hv'⟩ := exists_gen D.toPre.P.isLB
    (φ' := fun p : Fin 4 × ((Fin r × Fin r) × Fin 4) => (![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left,
      (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) p.1 ≫ tensφ T.pr p.2)
    (ε' := fun p => (![1, -2, -1, 2] : Fin 4 → ℤ) p.1 * tensε W p.2) (by
      intro U _ h
      let Lh : (D'.P.A ⟶ D.toPre.P.A) → (D'.P.A ⟶ D.toPre.P.A) → U :=
        fun x x' => ∏ l : Fin 4, h (GlobalTheory.PolDeg.lamPts x x' l) ^ Oε l
      let P : Fin 4 → Fin r → (D'.P.A ⟶ D.toPre.P.A) := fun a i => ∏ k, T.pr k ^ M a i k
      have lamS : ∀ k l, Lh (T.pr k) (T.pr l) = Lh (T.pr l) (T.pr k) := by
        intro k l
        simp only [Lh, Fin.prod_univ_four]
        show h (T.pr k * T.pr l).left ^ (1 : ℤ) * h (T.pr k).left ^ (-1 : ℤ) * h (T.pr l).left ^ (-1 : ℤ) *
            h (1 : D'.P.A ⟶ D.toPre.P.A).left ^ (1 : ℤ) =
          h (T.pr l * T.pr k).left ^ (1 : ℤ) * h (T.pr l).left ^ (-1 : ℤ) * h (T.pr k).left ^ (-1 : ℤ) *
            h (1 : D'.P.A ⟶ D.toPre.P.A).left ^ (1 : ℤ)
        rw [mul_comm (T.pr k) (T.pr l)]
        ac_rfl
      have H1 := GlobalTheory.T.prod_four_maps_lam_pow_eq_one U W A (fun k l => Lh (T.pr k) (T.pr l)) lamS hW
      have H2 : ∏ q : Fin 4 × (Fin r × Fin r), (∏ k, ∏ l, Lh (T.pr k) (T.pr l) ^
          (M q.1 q.2.1 k * M q.1 q.2.2 l)) ^ E q = 1 := by
        rw [Fintype.prod_prod_type]
        exact Eq.trans (Finset.prod_congr rfl fun a _ => Fintype.prod_prod_type _) H1
      have hR : ∏ p : Fin 4 × ((Fin r × Fin r) × Fin 4), h ((![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left,
          (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) p.1 ≫ tensφ T.pr p.2) ^
          ((![1, -2, -1, 2] : Fin 4 → ℤ) p.1 * tensε W p.2) =
          ∏ q : Fin 4 × (Fin r × Fin r), Lh (P q.1 q.2.1) (P q.1 q.2.2) ^ E q := by
        rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun a _ => ?_
        rw [Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun ij _ => ?_
        rw [← Finset.prod_zpow]
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [four_eq T A f hf a, comp_tensφ', hpr, hpr, ← zpow_mul]
        congr 1
        simp only [tensε, E, e]
        ring
      have hL : ∀ q : Fin 4 × (Fin r × Fin r), ∏ κ : Fin 4 ⊕ ((Fin r × Fin r) × Fin 4),
          h (Sum.elim (GlobalTheory.PolDeg.lamPts (P q.1 q.2.1) (P q.1 q.2.2))
            (fun m : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (T.pr m.1.1) (T.pr m.1.2) m.2) κ) ^
          (E q * Sum.elim Oε (fun m : (Fin r × Fin r) × Fin 4 => -(M q.1 q.2.1 m.1.1 * M q.1 q.2.2 m.1.2 * Oε m.2)) κ) =
          Lh (P q.1 q.2.1) (P q.1 q.2.2) ^ E q * ((∏ k, ∏ l, Lh (T.pr k) (T.pr l) ^
            (M q.1 q.2.1 k * M q.1 q.2.2 l)) ^ E q)⁻¹ := by
        intro q
        rw [Fintype.prod_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr]
        congr 1
        · rw [← Finset.prod_zpow]
          refine Finset.prod_congr rfl fun l _ => ?_
          rw [← zpow_mul, mul_comm]
        · rw [← zpow_neg, ← Finset.prod_zpow, Fintype.prod_prod_type, Fintype.prod_prod_type]
          refine Finset.prod_congr rfl fun k _ => ?_
          rw [← Finset.prod_zpow]
          refine Finset.prod_congr rfl fun l _ => ?_
          rw [← zpow_mul, ← Finset.prod_zpow]
          refine Finset.prod_congr rfl fun l' _ => ?_
          rw [← zpow_mul]
          congr 1
          ring
      rw [hR, Fintype.prod_prod_type]
      refine (Finset.prod_congr rfl fun q _ => hL q).trans ?_
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, H2, inv_one, _root_.mul_one]) (GeneratorPullback.finProdGen D.toPre.P.L _ _ s)
    (finProd_isGen _ _ s hs)
  refine ⟨t', ht', fun y z J hJ => ?_⟩
  let ρ : TK R ⟶ D'.P.A := toUnit (TK R) ≫ D'.c y
  have hρ : ∀ k, ρ ≫ T.pr k = toUnit (TK R) ≫ D.toPre.c (T.xe y k) := fun k => by
    rw [Category.assoc, T.c_pr]
  have lamS : ∀ k l, val (D.toPre.tau (T.xe y k) (T.xe y l)) (𝟙 _) z J =
      val (D.toPre.tau (T.xe y l) (T.xe y k)) (𝟙 _) z J := fun k l => DVR.tauK_symm hJ _ _
  have H1 := GlobalTheory.T.prod_four_maps_lam_pow_eq_one _ W A _ lamS hW
  have H2 : ∏ q : Fin 4 × (Fin r × Fin r), (∏ k, ∏ l, val (D.toPre.tau (T.xe y k) (T.xe y l)) (𝟙 _) z J ^
      (M q.1 q.2.1 k * M q.1 q.2.2 l)) ^ E q = 1 := by
    rw [Fintype.prod_prod_type]
    refine Eq.trans (Finset.prod_congr rfl fun a _ => Fintype.prod_prod_type _) H1
  have hq : ∀ q : Fin 4 × (Fin r × Fin r), val (s q) (D'.xK y) z J =
      ((val (D.toPre.tau (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) q.1) q.2.1) (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) q.1) q.2.2)) (𝟙 _) z J)⁻¹ *
        ∏ k, ∏ l, val (D.toPre.tau (T.xe y k) (T.xe y l)) (𝟙 _) z J ^ (M q.1 q.2.1 k * M q.1 q.2.2 l)) ^ E q := fun q => by
    rw [hsv q _ _ z J hJ, show D'.xK y = ρ.left from rfl, hv q ρ (fun k => T.xe y k) hρ z J hJ, xe_four, xe_four]
  rw [hv' _ _ z J hJ, val_finProd _ _ _ _ _ hJ, Finset.prod_congr rfl fun q _ => hq q]
  simp only [mul_zpow, Finset.prod_mul_distrib]
  rw [H2, _root_.mul_one, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Fintype.prod_prod_type, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [inv_zpow', ← zpow_mul]
  congr 1
  simp only [E, e]
  ring

end Main

end GlobalTheory.MumSide
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiScalarEqUnitMulProdPeriods
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol

noncomputable section

namespace GlobalTheory.Mum.TensPol

theorem scalar_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : GlobalTheory.PolDeg.Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)) (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → ∀ (k : Q.X → Q.X → (FractionRing R)ˣ), (∀ a b, Q.TauCoord a b (k a b)) → ∀ (ga' : ∀ χ : D'.X, LB.Gen (LB.LinComb D'.P.L (K := PUnit) (fun _ => (D'.c χ).left) (fun _ => -1))) (a' : D'.X → (FractionRing R)ˣ), GlobalTheory.UU.PsiScal D' ga' a' → ∀ y : D'.X, ∃ u ∈ unitsK R, a' y = u * ∏ i, ∏ j, k (xe y i) (xe y j) ^ W i j := by
  intro R _ _ _ Q D' r W pr xe w hpsi k hk ga' a' h' y
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  haveI := Q.isAb.proper
  obtain ⟨J, hJ, iJ⟩ := GlobalTheory.Mum.TensPol.exists_int Q.B Q.M.L Q.M.isLB z
  obtain ⟨J', hJ', iJ'⟩ := GlobalTheory.Mum.TensPos.exists_int D'.P z
  let E : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk z)ˣ := Units.map (ev z).toMonoidHom
  have hE : Function.Injective E := Units.map_injective (ev_inj z)
  have hψ' : val (D'.psi y) (𝟙 _) z J' = E (a' y) * val (ga' y) (toUnit (TK R)).left z J' :=
    Units.ext (((h' y).2 (TK R) (𝟙 _) z J' hJ').trans (congrArg₂ (· * ·) (ev_eq z _) rfl))
  have mg' : val (ga' y) (toUnit (TK R)).left z J' ∈ unitsS z := GlobalTheory.Mum.TensPos.val_mem D'.P z iJ' _ _ _
  have mτ : ∀ b c : Q.X, ∃ u ∈ unitsS z, val (Q.tau b c) (𝟙 _) z J = u * E (k b c) := fun b c => by
    obtain ⟨u, -, hu⟩ := hk b c
    refine ⟨_, GlobalTheory.Mum.TensPol.val_mem z iJ (lamPts (Q.c b) (Q.c c)) (fun i => ?_) negε u, ?_⟩
    · fin_cases i <;> exact Over.w _
    · rw [hu z J hJ, gm_unitOn, _root_.mul_comm]
  choose u hu eu using mτ
  have e := hpsi y z J J' hJ hJ'
  have hφ : ∀ k, tensφ pr k ≫ Q.B.hom = D'.P.A.hom := by
    rintro ⟨⟨i, j⟩, k⟩
    fin_cases k <;> exact Over.w _
  have mw : gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) ∈ unitsS z := by
    refine gm_mem z (D'.c y).left
      (LB.wchart Q.M.L (tensφ pr) (fun k => J (D'.xK y ≫ tensφ pr k)) ⊓ D'.P.L.U (J' (D'.xK y)))
      ⟨Set.mem_iInter.2 fun k => ?_, iJ' _ (Over.w _)⟩ _
    have := iJ ((D'.c y).left ≫ tensφ pr k) (by rw [Category.assoc, hφ]; exact Over.w _)
    rw [← Category.assoc] at this
    exact this
  rw [hψ'] at e
  simp only [eu, mul_zpow, Finset.prod_mul_distrib] at e
  obtain ⟨v, hv, ev'⟩ := mul_mem (mul_mem (inv_mem mg') mw)
    (prod_mem fun i (_ : i ∈ Finset.univ) => prod_mem fun j (_ : j ∈ Finset.univ) => zpow_mem (hu (xe y i) (xe y j)) (W i j))
  refine ⟨v, hv, hE ?_⟩
  rw [map_mul, map_prod]
  simp only [map_prod, map_zpow]
  rw [show E v = _ from ev', eq_mul_inv_of_mul_eq e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.Mum.TensPol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupActionCompatFibreIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

namespace GlobalTheory.ThetaMove

theorem isActOf_of_fibreIso : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} (hL : L.IsLB) (hL' : L'.IsLB) {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) [IsIso f] (k : ℤ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : f ≫ (translT A θ.pt).left = (translT A' θ'.pt).left ≫ f) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (σ σ' : LB.Sec (LPow A' L' k T')) (τ τ' : LB.Sec (LPow A L k T)) (hσ : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) τ (q ≫ f) z J = (Ψ q z J J' ^ k).val * sval (L := L') (φ := fun _ : Fin 1 => (snd T' A').left) (ε := fun _ => k) σ q z J') (hσ' : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) τ' (q ≫ f) z J = (Ψ q z J J' ^ k).val * sval (L := L') (φ := fun _ : Fin 1 => (snd T' A').left) (ε := fun _ => k) σ' q z J') (hact : IsActOf A' L' k θ' σ σ'), IsActOf A L k θ τ τ' := by
  intro S S' A A' _ _ L L' hL hL' T T' f _ k θ θ' Ψ hT H σ σ' τ τ' hσ hσ' hact
  refine GlobalTheory.ThetaNu.isActOf_of_sval hL fun y J hJ => ?_
  choose J' hJ' using fun χ : (T ⊗ A).left ⟶ A'.left => exists_chart hL' (χ y)
  have gJ' : Good L' y J' := hJ'
  have e1 := hσ' _ (inv f) y J J' hJ gJ'
  have e2 := twist_val hact (inv f) y gJ'
  have e3 := H _ (inv f) y J J' hJ gJ'
  have e4 := hσ _ (inv f ≫ (translT A' θ'.pt).left) y J J' hJ gJ'
  have c : (inv f ≫ (translT A' θ'.pt).left) ≫ f = 𝟙 _ ≫ (translT A θ.pt).left := by
    rw [Category.assoc, ← hT, ← Category.assoc, IsIso.inv_hom_id]
  rw [IsIso.inv_hom_id] at e1 e3
  rw [c] at e4
  rw [e1, e2, e4, e3]
  generalize Ψ (inv f ≫ (translT A' θ'.pt).left) y J J' ^ k = a
  generalize Ψ (inv f) y J J' ^ k = b
  generalize val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ (inv f) y J' = v
  generalize sval (L := L') (φ := fun _ : Fin 1 => (snd T' A').left) (ε := fun _ => k) σ
    (inv f ≫ (translT A' θ'.pt).left) y J' = w
  rw [Units.val_mul, Units.val_mul]
  linear_combination (-(b.val * v.val * w)) * a.mul_inv

end GlobalTheory.ThetaMove
end

