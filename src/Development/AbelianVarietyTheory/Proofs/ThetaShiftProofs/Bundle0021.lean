module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.AnalyticTorusPointBaseEqHolUnifEx
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnVecTorusLetter
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
open scoped Classical

namespace GlobalTheory.ArcQ.TorusLetter

open MonoidalCategory CartesianMonoidalCategory MonObj

theorem valR_eq_mul {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {ε : K → ℤ}
    {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    {t' : LB.Gen (LB.LinComb L φ' ε)} (ht' : t'.IsGen) {F : Type} [Field F] (r : Sp F ⟶ Y) (r' : Sp F ⟶ Y')
    (h : ∀ k, r ≫ φ k = r' ≫ φ' k) (c : F)
    (hv : ∀ z J, Good L z J → (val t r z J).val = TorusExt.stalkConst z c * (val t' r' z J).val)
    (j : K → L.ι) (hj : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ j) :
    ⊤ ≤ r' ⁻¹ᵁ LB.wchart L φ' j ∧ valR r _ (t.s j).val = c * valR r' _ (t'.s j).val := by
  have hj' : ⊤ ≤ r' ⁻¹ᵁ LB.wchart L φ' j := fun z hz => Set.mem_iInter.2 fun k => by
    have : (r ≫ φ k) z ∈ L.U (j k) := Set.mem_iInter.1 (hj hz) k
    rw [h k] at this
    exact this
  let z : Sp F := IsLocalRing.closedPoint F
  choose J hJ using fun q : Sp F ⟶ X => exists_chart hL (q z)
  replace hJ : Good L z J := hJ
  refine ⟨hj', (TorusExt.stalkConst z).injective ?_⟩
  have e₁ : TorusExt.stalkConst z (valR r _ (t.s j).val) = (gm r z (LB.wchart L φ j) (t.s j)).val :=
    (TorusExt.gs_eq_stalkConst r z hj _).symm.trans (gs_unit r z _ (hj trivial) _)
  have e₂ : TorusExt.stalkConst z (valR r' _ (t'.s j).val) = (gm r' z (LB.wchart L φ' j) (t'.s j)).val :=
    (TorusExt.gs_eq_stalkConst r' z hj' _).symm.trans (gs_unit r' z _ (hj' trivial) _)
  have e₃ : trF φ ε r z j (fun k => J (r ≫ φ k)) = trF φ' ε r' z j (fun k => J (r' ≫ φ' k)) :=
    Finset.prod_congr rfl fun k _ =>
      congrArg (fun q => gm q z (L.U (j k) ⊓ L.U (J q)) (L.g (j k) (J q)) ^ ε k) (h k)
  rw [map_mul, e₁, e₂, gen_trans ht r z (hj trivial) (hJ.mem φ r), gen_trans ht' r' z (hj' trivial) (hJ.mem φ' r'),
    e₃, Units.val_mul, Units.val_mul]
  exact (congrArg (_ * ·) (hv z J hJ)).trans (mul_left_comm _ _ _)

theorem gtφT_eq {R : Type} [CommRing R] [IsDomain R] (D : Out.DegPre R) {T : Over (Sp R)} (b : T ⟶ D.P.A) (x : D.X)
    (k : Fin 4) : Out.DegPre.gtφT D T b x k = b.left ≫ Out.DegPre.gtφT D D.P.A (𝟙 _) x k := by
  have h : ∀ p : 𝟙_ (Over (Sp R)) ⟶ D.P.A, b ≫ toUnit D.P.A ≫ p = toUnit T ≫ p := fun p => by
    rw [← Category.assoc, comp_toUnit]
  fin_cases k
  · change (toUnit _ ≫ D.c x * b).left = (b ≫ (toUnit _ ≫ D.c x * 𝟙 D.P.A)).left
    rw [MonObj.comp_mul, h, Category.comp_id]
  · change (toUnit _ ≫ D.c x).left = (b ≫ toUnit _ ≫ D.c x).left
    rw [h]
  · exact (Category.comp_id _).symm
  · change (toUnit _ ≫ η[D.P.A]).left = (b ≫ toUnit _ ≫ η[D.P.A]).left
    rw [h]

theorem zeroT_left {R : Type} [CommRing R] [IsDomain R] (D : Out.DegPre R) (T : Over (Sp R)) :
    (Out.DegPre.zeroT D T).left = T.hom ≫ (η[D.P.A]).left := by
  have := Over.w (toUnit T)
  exact congrArg (· ≫ (η[D.P.A]).left) ((Category.comp_id _).symm.trans this)

theorem tf_hom [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] :
    (show Sp ℂ ⟶ Sp ℂ from (Out.TF (R := ℂ) ℂ).hom) = 𝟙 (Sp ℂ) := by
  refine (Spec.map_comp _ _).symm.trans ?_
  refine Eq.trans (congrArg Spec.map ?_) (Spec.map_id _)
  ext x
  exact (IsScalarTower.algebraMap_apply ℂ (FractionRing ℂ) ℂ x).symm

theorem fderiv_of_exp {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : V → ℂ} (hf : DifferentiableAt ℂ f 0)
    (v : V) (m : ℂ) (h : ∀ s : ℂ, f (s • v) = eTwoPi (s * m) * f 0) :
    fderiv ℂ f 0 v = 2 * Real.pi * Complex.I * m * f 0 := by
  have h₁ : HasDerivAt (fun s : ℂ => f (s • v)) (fderiv ℂ f 0 v) 0 := by
    have a : HasDerivAt (fun s : ℂ => s • v) v 0 := by simpa using (hasDerivAt_id (0 : ℂ)).smul_const v
    exact HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hf.hasFDerivAt a (zero_smul _ _).symm
  have h₂ : HasDerivAt (fun s : ℂ => eTwoPi (s * m) * f 0) (2 * Real.pi * Complex.I * m * f 0) 0 := by
    have := ((((hasDerivAt_id (0 : ℂ)).mul_const m).const_mul (2 * Real.pi * Complex.I)).cexp).mul_const (f 0)
    refine HasDerivAt.congr_deriv this ?_
    simp
  rw [funext h] at h₁
  exact h₁.unique h₂

theorem sum_dual_mul {E : Type} [Field E] [NumberField E] (τ ρ : E →+* ℂ) :
    ∑ i, τ ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (integralBasis E) i) *
      ρ (integralBasis E i) = if τ = ρ then 1 else 0 := by
  have := idempotent_evaluation E ℂ _ (integralBasis E) ρ τ
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [TB.evAt, TB.idemOf, TB.trDual, map_sum, Algebra.TensorProduct.productMap_apply_tmul,
      AlgHom.id_apply, RingHom.toRatAlgHom_apply] using this

end GlobalTheory.ArcQ.TorusLetter

namespace GlobalTheory.ArcQ

open TorusLetter MonoidalCategory CartesianMonoidalCategory MonObj

theorem anVec_torusLetter : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (ξ : Module.Dual ℤ a.D₀.X) (t : (Fu.Di Ha.i).La) (τ : E →+* ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)), (∀ v', -(Fu.Di Ha.i).EF t v' = ξ (Ha.y v')) → GtTanR ν → ν.b = Out.DegPre.zeroT a.D₀ (epsR ℂ) → (∀ x, DlogTan ν x (xiVal τ ξ x)) → AnVec Ha ν (fun j => if ty j = conjEmb τ then (2 * Real.pi * Complex.I)⁻¹ * Ha.P₀ t j else 0) := by
  intro _ E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha ξ t τ ν ht hν hb hd
  obtain ⟨nn, hN, -, -, hnn, -, -⟩ := holArc_nilpotent E H Dw l Xo c σ O β Y a χ W g ty Fu Ha
  let b := RingOfIntegers.basis E
  let cf := fun i => τ ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (integralBasis E) i)
  have hbar : ∀ u : 𝓞 E, H.bar (H.bar u) = u := fun u => Subtype.ext (by
    change ((H.bar (H.bar u) : 𝓞 E) : E) = (u : E)
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply])
  have hEF : ∀ i v', -(Fu.Di Ha.i).EF (H.bar (b i) • t) v' = ξ (b i • Ha.y v') := fun i v' => by
    rw [(Fu.Di Ha.i).adj, hbar, ht, map_smul]
  have hr := fun i => (Ha.riemann (H.bar (b i) • t)).1 fun v' hv' => by
    have := hEF i v'
    rwa [hv', smul_zero, map_zero, neg_eq_zero] at this
  have htor : ∀ i (s : ℂ), IsTorusPt (Ha.ex₀ (s • Ha.P₀ (H.bar (b i) • t)))
      (fun x => eTwoPi (s * (ξ (b i • x) : ℤ))) := fun i s => by
    obtain ⟨x, hx, hx'⟩ := (hr i).2 s
    have hxe : x = fun z => eTwoPi (s * (ξ (b i • z) : ℤ)) := funext fun z => by
      obtain ⟨v', rfl⟩ := Ha.y_onto z
      rw [hx', ← hEF]
      congr 1
      push_cast
      ring
    exact hxe ▸ hx
  have hyt : Ha.y t = 0 := ((Ha.riemann t).1 fun v' hv' => by
    have := ht v'
    rwa [hv', map_zero, neg_eq_zero] at this).1
  have hP : ∀ (u : 𝓞 E) j, Ha.P₀ (u • t) j = ty j (u : E) * Ha.P₀ t j := fun u j => by
    have h := (Ha.period (((Ha.T + 1 : ℝ) : ℂ) * Complex.I) (by simp)).1 u t j
    rwa [Ha.Pw_eq, Ha.Pw_eq, hN, hN, hnn t hyt, hnn _ (by rw [map_smul, hyt, smul_zero]), map_zero, smul_zero,
      add_zero, add_zero] at h
  have hz : (fun j => if ty j = conjEmb τ then (2 * Real.pi * Complex.I)⁻¹ * Ha.P₀ t j else 0) =
      ∑ i, ((2 * Real.pi * Complex.I)⁻¹ * cf i) • Ha.P₀ (H.bar (b i) • t) := funext fun j => by
    have h := sum_dual_mul τ (conjEmb (ty j))
    have e : ∀ i, ty j ((H.bar (b i) : 𝓞 E) : E) = conjEmb (ty j) (integralBasis E i) := fun i => by
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, integralBasis_apply]
      rfl
    have hc : ty j = conjEmb τ ↔ τ = conjEmb (ty j) := by
      constructor <;> (intro q; rw [q]; ext u; simp [conjEmb])
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hP, e]
    calc _ = (2 * Real.pi * Complex.I)⁻¹ * (if τ = conjEmb (ty j) then 1 else 0) * Ha.P₀ t j := by
          simp only [hc]; split_ifs <;> simp
      _ = _ := by
          rw [← h, Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by simp only [cf]; ring
  rw [hz]
  have h0 : (Ha.ex₀ 0).IsZero := (Ha.ker 0).2 ⟨0, map_zero _, (map_zero _).symm⟩
  have hzF : ∀ p : Out.GtPtF a.D₀ ℂ, p.b = Out.DegPre.zeroF a.D₀ ℂ →
      (show Sp ℂ ⟶ _ from p.b.left) = (η[a.D₀.P.A]).left := fun p hp => by
    rw [hp]
    exact (zeroT_left a.D₀ _).trans ((congrArg (· ≫ (η[a.D₀.P.A]).left) tf_hom).trans (Category.id_comp _))
  have hνb : ν.b.left = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (η[a.D₀.P.A]).left := by
    rw [hb]; exact zeroT_left a.D₀ _
  obtain ⟨g₀, hg₀, hp⟩ := hν
  have hfst : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ ν.b.left = (Ha.ex₀ 0).b.left := by
    rw [← hp.1, hg₀.1]
    exact (zeroT_left a.D₀ _).trans ((Category.id_comp _).trans (hzF _ h0.1).symm)
  refine ⟨⟨hfst, fun U hU f => ?_⟩, fun x j hj => ?_⟩
  · have hU0 : ⊤ ≤ (show Sp ℂ ⟶ _ from (Ha.ex₀ 0).b.left) ⁻¹ᵁ U :=
      hfst ▸ (ZH.CrdCalc.valR_spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom _ U hU).1
    have hdf : DifferentiableAt ℂ (fun z => valAt' (show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left) U f) 0 :=
      (Ha.hol_b U f).2.differentiableAt ((Ha.hol_b U f).1.mem_nhds ⟨trivial, hU0⟩)
    have hl : valR (A := DualNumber ℂ) ν.b.left U f = algebraMap ℂ _ (valR (A := ℂ) (η[a.D₀.P.A]).left U f) := by
      rw [hνb]
      exact (ZH.CrdCalc.valR_spMap _ _ U (hzF _ h0.1 ▸ hU0)).2 f
    refine (congrArg TrivSqZeroExt.snd ((ZH.CrdCalc.valR_eq _ U hU f).symm.trans hl)).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Eq.trans rfl (Finset.sum_eq_zero fun i _ => ?_).symm
    rw [map_smul, fderiv_of_exp hdf _ 0 fun s => ?_]
    · simp
    · rw [hzF _ (htor i s).1, hzF _ h0.1]
      simp [eTwoPi]
  · have hL := a.D₀.P.isLB
    obtain ⟨-, hv0⟩ := (isZero_iff _).1 h0
    obtain ⟨hj0, e0⟩ := valR_eq_mul hL (ν.isGen x) ((Ha.ex₀ 0).isGen x)
      (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) (𝟙 (Sp ℂ)) (fun k => by
        rw [gtφT_eq, ← Category.assoc, hfst]
        exact (gtφT_eq a.D₀ (Ha.ex₀ 0).b x k).symm.trans (Category.id_comp _).symm) 1 (fun z J hJ => by
        have e₁ := (val_corr hJ (hg₀.2 x) (𝟙 _)).trans (val_one _)
        have e₂ := (val_corr hJ (hp.2 x) (𝟙 _)).trans (val_pull hJ _ _ _)
        rw [Category.id_comp] at e₂
        rw [map_one, _root_.one_mul]
        exact congrArg Units.val ((e₂.symm.trans e₁).trans (hv0 x z J hJ).symm)) j (fun z _ => hj trivial)
    have hf : TrivSqZeroExt.fst (valR (A := DualNumber ℂ) (𝟙 _) _ ((ν.s x).s j).val) = chiVal (Ha.ex₀ 0) x j := by
      have := (ZH.CrdCalc.valR_spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom (𝟙 _)
        (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) j) hj).2 ((ν.s x).s j).val
      rw [Category.comp_id] at this
      exact this.symm.trans (e0.trans (_root_.one_mul _))
    have hset : ∀ z, (⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Ha.ex₀ z).b x) j) ↔
        ⊤ ≤ (show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left) ⁻¹ᵁ
          LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ a.D₀.P.A (𝟙 _) x) j := fun z => by
      have e : Out.DegPre.gtφ a.D₀ ℂ (Ha.ex₀ z).b x =
          fun k => (Ha.ex₀ z).b.left ≫ Out.DegPre.gtφT a.D₀ a.D₀.P.A (𝟙 _) x k :=
        funext fun k => gtφT_eq a.D₀ (Ha.ex₀ z).b x k
      rw [e]
      exact ⟨fun h y _ => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (h trivial) k,
        fun h y _ => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (h trivial) k⟩
    have hdf : DifferentiableAt ℂ (fun z => chiVal (Ha.ex₀ z) x j) 0 := by
      refine (Ha.hol_chi x j).differentiableAt (IsOpen.mem_nhds ?_ hj0)
      simpa only [hset, Set.mem_univ, true_and] using
        (Ha.hol_b (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ a.D₀.P.A (𝟙 _) x) j) 0).1
    have hder : ∀ i, fderiv ℂ (fun z => chiVal (Ha.ex₀ z) x j) 0 (Ha.P₀ (H.bar (b i) • t)) =
        2 * Real.pi * Complex.I * (ξ (b i • x) : ℤ) * chiVal (Ha.ex₀ 0) x j := fun i =>
      fderiv_of_exp hdf _ _ fun s => by
        obtain ⟨hb₁, hv₁⟩ := (TorusExt.isTorusPtF_iff_val _ _).1
          ((TorusExt.isTorusPtF_iff_isTorusPt _ _).2 (htor i s))
        have hφ : Out.DegPre.gtφ a.D₀ ℂ (Ha.ex₀ (s • Ha.P₀ (H.bar (b i) • t))).b x =
            Out.DegPre.gtφ a.D₀ ℂ (Ha.ex₀ 0).b x := by rw [(htor i s).1, h0.1]
        exact (valR_eq_mul hL ((Ha.ex₀ (s • Ha.P₀ (H.bar (b i) • t))).isGen x) ((Ha.ex₀ 0).isGen x)
          (𝟙 (Sp ℂ)) (𝟙 (Sp ℂ)) (fun k => by rw [hφ]) _ (fun z J hJ => (hv₁ x z J hJ).trans
            ((_root_.mul_one _).symm.trans (congrArg₂ (fun p q : (Sp ℂ).presheaf.stalk z => p * q) rfl
              (congrArg Units.val (hv0 x z J hJ)).symm))) j
          (by rw [hφ]; exact hj0)).2
    refine TrivSqZeroExt.ext (by simpa using hf) ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hd x j hj, hf, map_sum]
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, map_smul, hder,
      smul_eq_mul, xiVal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := Complex.two_pi_I_ne_zero
    simp only [cf, b]
    field_simp

end GlobalTheory.ArcQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnalyticDictionaryExpAdditiveSurjectiveLinear
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

theorem ex0_additive_surjective_equivariant : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F)
    [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b)
    (Λ : GtAn a), (∀ z z', (Λ.ex0 z).IsAdd (Λ.ex0 z') (Λ.ex0 (z + z'))) ∧ Function.Surjective Λ.ex0 ∧
      ∀ (x : 𝓞 E) z, @GtAct ℂ _ _ (𝓞 E) _ H.starRing a.D₀ ℂ _ _ _ a.oa x (Λ.ex0 z) (Λ.ex0 (Λ.A.actV x z)) := by
  intro _ _ E _ _ _ H inst D l c O _ β _ _ b a Λ
  refine ⟨GtAnModel.isAdd Λ, GtAnModel.analyticTorusPoint_surjective Λ, ?_⟩
  obtain rfl : inst = H.starRing := Λ.star_eq
  exact GtAnModel.gtAct Λ

end GlobalTheory.ArcPts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnalyticDictionaryExpHolomorphicOverUnif
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

section Lift

variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]

theorem gtHol_toUnit_left :
    (show Sp ℂ ⟶ Sp ℂ from (toUnit (Out.TF (R := ℂ) ℂ)).left) = 𝟙 (Sp ℂ) := by
  have h : (show Sp ℂ ⟶ Sp ℂ from (toUnit (Out.TF (R := ℂ) ℂ)).left) =
      Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ := by
    have := Over.w (toUnit (Out.TF (R := ℂ) ℂ))
    exact (Category.comp_id _).symm.trans this
  refine h.trans ((Spec.map_comp _ _).symm.trans ?_)
  refine Eq.trans (congrArg Spec.map ?_) (Spec.map_id _)
  ext x
  exact (IsScalarTower.algebraMap_apply ℂ (FractionRing ℂ) ℂ x).symm

theorem gtHol_isLift (D₀ : Out.DegPre ℂ) {g : ℕ} (u : HolUnif D₀.P.A D₀.P.L g) (p : Out.TF (R := ℂ) ℂ ⟶ D₀.P.A)
    (χ : D₀.X) (c z : Fin g → ℂ) (hc : u.ex c = D₀.c χ) (hp : (show Sp ℂ ⟶ _ from p.left) = (u.ex z).left) :
    FrameValue.IsLift u (Out.DegPre.gtφ D₀ ℂ p χ) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![c + z, c, z, 0] := by
  have e : ∀ w, (show Sp ℂ ⟶ _ from (toUnit (Out.TF (R := ℂ) ℂ) ≫ u.ex w).left) = (u.ex w).left := fun w =>
    (congrArg (fun q : Sp ℂ ⟶ Sp ℂ => q ≫ (u.ex w).left) gtHol_toUnit_left).trans (Category.id_comp _)
  have hp' : p = toUnit _ ≫ u.ex z := Over.OverMorphism.ext (hp.trans (e z).symm)
  have h0 : u.ex 0 = η[D₀.P.A] := by
    rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def]
    simp
  intro k
  refine (Category.id_comp _).trans ?_
  fin_cases k
  · refine Eq.trans ?_ (e (c + z))
    refine congrArg (fun m : Out.TF (R := ℂ) ℂ ⟶ D₀.P.A => m.left) ?_
    rw [u.ex_add, MonObj.comp_mul, hc, ← hp']
    rfl
  · refine Eq.trans ?_ (e c)
    rw [hc]
    rfl
  · exact hp
  · refine Eq.trans ?_ (e 0)
    rw [h0]
    rfl

end Lift

theorem analyticDictionaryExp_holomorphic_over_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a), IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (Λ.ex0 z).b.left)) ∧ ∀ x j, DifferentiableOn ℂ (fun z => chiVal (Λ.ex0 z) x j) {z | ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 z).b x) j} ∧ ∀ z, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 z).b x) j → chiVal (Λ.ex0 z) x j = eTwoPi (z.1 (Λ.ε.symm x)) * FrameValue.frameProd Λ.u Out.DegPre.gtε ![Λ.A.ct (Λ.ε.symm x) + z.2, Λ.A.ct (Λ.ε.symm x), z.2, 0] j := by
  intro E _ _ _ H _ D l c O _ β _ _ b a Λ
  have hl : ∀ (z : Λ.A.V) (x : a.D₀.X), FrameValue.IsLift Λ.u (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 z).b x)
      (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![Λ.A.ct (Λ.ε.symm x) + z.2, Λ.A.ct (Λ.ε.symm x), z.2, 0] := fun z x =>
    gtHol_isLift a.D₀ Λ.u _ x _ _ (by rw [Λ.ct, LinearEquiv.apply_symm_apply]) (Λ.ex0_b z)
  have hv : ∀ x j z, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 z).b x) j →
      chiVal (Λ.ex0 z) x j = eTwoPi (z.1 (Λ.ε.symm x)) * FrameValue.frameProd Λ.u Out.DegPre.gtε
        ![Λ.A.ct (Λ.ε.symm x) + z.2, Λ.A.ct (Λ.ε.symm x), z.2, 0] j := by
    intro x j z hj
    have h₁ := FrameValue.valAt'_gen a.D₀.P.isLB ((Λ.ex0 z).isGen x) (hl z x) (j := j) hj
    obtain ⟨y, rfl⟩ := Λ.ε.surjective x
    rw [LinearEquiv.symm_apply_apply] at h₁ ⊢
    rw [Λ.arcDict_expZero_section] at h₁
    exact h₁
  refine ⟨fun U f => ?_, fun x j => ⟨?_, hv x j⟩⟩
  · obtain ⟨ho, hd⟩ := Λ.u.hol U f
    simp only [Λ.ex0_b, Set.mem_univ, true_and]
    exact ⟨ho.preimage continuous_snd, hd.comp differentiable_snd.differentiableOn (fun _ h => h)⟩
  · refine DifferentiableOn.congr ?_ (hv x j)
    refine DifferentiableOn.fun_mul ?_ ?_
    · have : Differentiable ℂ (fun z : Λ.A.V => z.1 (Λ.ε.symm x)) :=
        (Λ.A.evalCLM (Λ.ε.symm x)).differentiable.comp differentiable_fst
      exact ((this.const_mul _).cexp).differentiableOn
    · intro z₀ hz₀
      refine DifferentiableAt.differentiableWithinAt ?_
      have hd : ∀ k, Differentiable ℂ fun z : Λ.A.V =>
          (![Λ.A.ct (Λ.ε.symm x) + z.2, Λ.A.ct (Λ.ε.symm x), z.2, 0] : Fin 4 → Fin Λ.A.gB → ℂ) k := fun k => by
        fin_cases k
        · exact differentiable_snd.const_add _
        · exact differentiable_const _
        · exact differentiable_snd
        · exact differentiable_const _
      have h : ∀ k, DifferentiableAt ℂ (fun z : Λ.A.V => Λ.u.fr (j k)
          ((![Λ.A.ct (Λ.ε.symm x) + z.2, Λ.A.ct (Λ.ε.symm x), z.2, 0] : Fin 4 → Fin Λ.A.gB → ℂ) k) ^
            Out.DegPre.gtε k) z₀ := fun k => by
        have hk := ((hl z₀ x).le_iff j).1 hz₀ k
        refine DifferentiableAt.zpow ?_ (Or.inl (Λ.u.fr_ne _ _ hk))
        exact ((Λ.u.fr_hol (j k)).differentiableAt ((Λ.u.hol _ 0).1.mem_nhds hk)).comp z₀ (hd k z₀)
      exact (HasFDerivAt.finsetProd (u := Finset.univ) fun k _ => (h k).hasFDerivAt).differentiableAt

end GlobalTheory.ArcPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnalyticDictionaryExpKernelIotaTorusPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts.GtKer

theorem ker_iota_torus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a), (∀ z, (Λ.ex0 z).IsZero ↔ ∃ la : Λ.A.La, la.y = 0 ∧ z = Λ.A.P0 la) ∧ (∀ la : Λ.A.La, Out.GtPtF.IsIota (Λ.ε la.y) (Λ.ex0 (Λ.A.P0 la))) ∧ (∀ lam : Λ.A.X →+ ℂ, IsTorusPt (Λ.ex0 (lam, 0)) (fun x => eTwoPi (lam (Λ.ε.symm x)))) ∧ ∀ z x, IsTorusPt (Λ.ex0 z) x → z.2 ∈ Λ.A.abelian₂ := by
  intro E _ _ _ H _ D l c O _ β _ _ b a Λ
  refine ⟨GtAnModel.isZero_iff Λ, GtAnModel.isIota Λ, fun lam => ⟨?_, fun x j hc hj => ?_⟩, fun z x h => ?_⟩
  · rw [GtAnModel.analyticTorusPoint_base_eq_holUnif_ex, GtAnModel.ex_zero]
  · obtain ⟨x, rfl⟩ := Λ.ε.surjective x
    have hz := GtAnModel.isLift_gt Λ (lam, 0) x
    have h := FrameValue.valAt'_gen a.D₀.P.isLB ((Λ.ex0 (lam, 0)).isGen _) hz (j := j) hj
    have h1 := Λ.arcDict_expZero_section (lam, 0) x
    have e : ∀ k k', ![Λ.A.ct x + (0 : Fin Λ.A.gB → ℂ), Λ.A.ct x, 0, 0] k = ![Λ.A.ct x + 0, Λ.A.ct x, 0, 0] k' →
        j k = j k' := fun k k' hk =>
      hc k k' (((Category.id_comp _).symm.trans (hz k)).trans
        ((congrArg (fun w => (Λ.u.ex w).left) hk).trans ((Category.id_comp _).symm.trans (hz k')).symm))
    have e₁ : j 0 = j 1 := e 0 1 (by simp)
    have e₂ : j 2 = j 3 := e 2 3 (by simp)
    have n₁ := Λ.u.fr_ne _ _ ((hz.le_iff j).1 hj 1)
    have n₃ := Λ.u.fr_ne _ _ ((hz.le_iff j).1 hj 3)
    have hf : FrameValue.frameProd Λ.u Out.DegPre.gtε ![Λ.A.ct x + (0 : Fin Λ.A.gB → ℂ), Λ.A.ct x, 0, 0] j = 1 := by
      simp only [Matrix.cons_val] at n₁ n₃
      simp only [FrameValue.frameProd, Fin.prod_univ_four, Out.DegPre.gtε, Matrix.cons_val, e₁, e₂, add_zero,
        zpow_neg, zpow_one]
      field_simp
    refine h.trans ((congrArg₂ (· * ·) h1 hf).trans ?_)
    simp
  · have h0 : Λ.u.ex z.2 = 1 := Over.OverMorphism.ext ((Λ.ex0_b z).symm.trans ((congrArg (·.left) h.1).trans
      ((toUnit_TF_comp_left _).trans (by rw [Hom.one_def, toUnit_unit, Category.id_comp]))))
    exact Λ.lam.le ((Λ.u.ker _).1 h0)

end GlobalTheory.ArcPts.GtKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterRingOverDVRPolynomialDenominatorsStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcLetterRingOverDVR_polynomial_denominators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Tv : CDVR) (ϖ : Tv.V), ϖ ≠ 0 → IsDomain (ArcSR Dw Tv.V ϖ) ∧ Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)) (ArcSR Dw Tv.V ϖ)) ∧ ((arcιR Dw Tv.V ϖ).comp (PowerSeries.C (R := Tv.V))).Flat ∧ (∃ ψ : ArcSR Dw Tv.V ϖ →+* ArcS Dw Tv.Fr, ψ.comp (arcιR Dw Tv.V ϖ) = (arcι Dw Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr)) ∧ ∀ x : ArcLt Dw, ψ (arcXR Dw Tv.V ϖ x) = arcX Dw Tv.Fr x.1 x.2.1 x.2.2) ∧ ∀ ψ : ArcSR Dw Tv.V ϖ →+* ArcS Dw Tv.Fr, ψ.comp (arcιR Dw Tv.V ϖ) = (arcι Dw Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr)) → (∀ x : ArcLt Dw, ψ (arcXR Dw Tv.V ϖ x) = arcX Dw Tv.Fr x.1 x.2.1 x.2.2) → ∀ f : ArcSR Dw Tv.V ϖ, (∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries Tv.Fr), algebraMap _ (ArcS Dw Tv.Fr) P = ψ f) → ∃ (N : ℕ) (G : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)), f * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) ^ N = algebraMap _ (ArcSR Dw Tv.V ϖ) G := by
  first | exact @GlobalTheory.LetterDenom.main | exact GlobalTheory.LetterDenom.main | (intros; apply GlobalTheory.LetterDenom.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcPointTangentPart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.Frames.ChgBC

noncomputable section

namespace GlobalTheory.ArcQ.TanPart

section Mul

variable {B B' Z Z' : Scheme.{0}} {G : Over B} [GrpObj G] {G' : Over B'} [GrpObj G'] {f : B' ⟶ B}
  {φ : G'.left ⟶ G.left}

end Mul

section Eps

variable {S : Type} [CommRing S]

theorem fst_alg : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S :=
  RingHom.ext fun x => by simp [TrivSqZeroExt.algebraMap_eq_inl]

end Eps

section Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S : Type} [CommRing S]

end Comb

section Gt

open GlobalTheory.TorusModel

variable {A : Type} [CommRing A] [IsDomain A] {D₀ : Out.DegPre A}

theorem isZero_of_isAdd {T : Over (Spec (CommRingCat.of A))} {g : Out.GtPt D₀ T} (h : g.IsAdd g g) : g.IsZero := by
  obtain ⟨hb, hv⟩ := (GlobalTheory.TorusModel.isAdd_iff _ _ _).1 h
  have hb1 : g.b = 1 := by
    exact (mul_eq_left.1 hb.symm)
  refine ⟨hb1, fun χ => corr_of_val D₀.P.isLB fun y J hJ => ?_⟩
  have e := hv χ y J hJ
  have face (x x' : T ⟶ D₀.P.A) : cubV D₀.cub y J 1 x x' = 1 := by
    have q := val_corr hJ (D₀.cub.face 0) (lift x x').left
    rw [val_one] at q
    refine (Eq.trans ?_ (val_cub D₀.cub (lift x x') hJ (pzero D₀.P.A _) (x2 D₀.P.A 0) (x2 D₀.P.A 1)).symm).trans q
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  have swap01 (x x' w : T ⟶ D₀.P.A) : cubV D₀.cub y J x x' w = cubV D₀.cub y J x' x w := by
    have q := (val_corr hJ D₀.cub.cubeSymmetric_swap_first (lift x (lift x' w)).left).trans (val_cub D₀.cub (lift x (lift x' w)) hJ _ _ _)
    refine q.trans ?_
    congr 1 <;> simp [x3]
  have swap12 (x x' w : T ⟶ D₀.P.A) : cubV D₀.cub y J x x' w = cubV D₀.cub y J x w x' := by
    have q := (val_corr hJ D₀.cub.cubeSymmetric_swap_last (lift x (lift x' w)).left).trans (val_cub D₀.cub (lift x (lift x' w)) hJ _ _ _)
    refine q.trans ?_
    congr 1 <;> simp [x3]
  have face3 (x x' : T ⟶ D₀.P.A) : cubV D₀.cub y J x x' 1 = 1 :=
    (swap12 _ _ _).trans ((swap01 _ _ _).trans (face _ _))
  rw [hb1] at e
  change cv g χ y J * cubV D₀.cub y J (DVR.cP D₀ T χ) 1 1 = _ at e
  rw [face3, _root_.mul_one] at e
  exact (mul_eq_left.1 e.symm).trans (val_one _).symm

end Gt

section ThetaShiftProofs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {K₁ : Type} [Field K₁] [Algebra c.F K₁] {b : O →+* K₁} {a : ArcIn Dw l β K₁ b} {χ : Sp (PowerSeries K₁) ⟶ Y.X}

end ThetaShiftProofs

end GlobalTheory.ArcQ.TanPart
end
end

