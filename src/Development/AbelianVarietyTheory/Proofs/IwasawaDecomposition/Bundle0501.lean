module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicArcAgreesAnalyticDictionary
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolArcEqFlowOrbit
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.SubsingletonRankIndicatorIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcFramedPointExtendsToModelBoundary
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

namespace GlobalTheory.CuspFrom

theorem arc_bdExt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) [Algebra c.F ℂ⸨X⸩] (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (y : FrPt Xo c ℂ⸨X⸩), (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → ArcBasis W (fun τ => σ.comp (embK c τ)) e → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → χ (IsLocalRing.closedPoint (PowerSeries ℂ)) ∉ abLocus Y.t.G → BdExt Y ((PowerSeries.C (R := ℂ)).comp σ) y := by
  intro E _ _ _ H Dw l Xo c σ O _ β Y a χ W _ e th y hF hχ hβ hB hA hab
  have hι : algebraMap (PowerSeries ℂ) ℂ⸨X⸩ = HahnSeries.ofPowerSeries ℤ ℂ := rfl
  have hFr : algebraMap c.F ℂ⸨X⸩ = ((HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.C (R := ℂ))).comp σ :=
    RingHom.ext hF
  have hcond : χ ≫ Y.s = spMap ((PowerSeries.C (R := ℂ)).comp σ) ≫ spMap β := by
    rw [hχ, OpenReg.spMap_comp, OpenReg.spMap_comp]
  let χ' : Sp (PowerSeries ℂ) ⟶ gen Y := pullback.lift χ (spMap ((PowerSeries.C (R := ℂ)).comp σ)) hcond
  have hχ'1 : χ' ≫ genι Y = χ := pullback.lift_fst _ _ _
  have hχ'2 : χ' ≫ genStr Y = spMap ((PowerSeries.C (R := ℂ)).comp σ) := pullback.lift_snd _ _ _
  obtain ⟨v, hvL, hv⟩ := hB
  obtain ⟨z, t', m1, m2, φ, hz, hzx, hφ, h0, hm, hu, -⟩ := hA
  have hG : Out.GlobalFnsSt := known_holds.laws.globalFns

  have hzF : z = GlobalTheory.AllWt.ptF y := by
    apply pullback.hom_ext
    · rw [hzx, Descent.ptF_fst]
    · rw [Descent.ptF_snd]
      apply hβ.right_cancellation
      have e1 : z ≫ pullback.snd _ _ = z ≫ Y.jQ ≫ pullback.snd _ _ := by rw [Y.jQ_over]
      rw [e1, Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc z, ← Category.assoc (z ≫ Y.jQ)]
      change (z ≫ Y.j) ≫ Y.s = _
      rw [hz, Category.assoc, hχ, OpenReg.spMap_comp, OpenReg.spMap_comp, OpenReg.spMap_comp, hFr]
  have hw : ∀ τ k, (v τ k).left ≫ W.t.G.hom = spMap (algebraMap (PowerSeries ℂ) (DualNumber (PowerSeries ℂ))) ≫ 𝟙 _ :=
    fun τ k => (Over.w (v τ k)).trans (Category.comp_id _).symm
  let g : EigFrame Y ((PowerSeries.C (R := ℂ)).comp σ) (χ' ≫ genι Y) :=
    { v := fun τ k => (v τ k).left ≫ W.m.φ
      tan := fun τ k => by
        rw [hχ'1]
        exact (OpenReg.tan_iff W.m (Category.id_comp χ) (hw τ k)).2
          ((DepthExt.tan_iff W.t (v τ k)).1 ((hv τ).1 k).1)
      eig := fun τ k x => by
        exact (OpenReg.eig_iff W.m (hw τ k) x _).2 (((hv τ).1 k).2 x)
      basis := fun τ w htan heig => by
        rw [hχ'1] at htan ⊢
        obtain ⟨w0, hw01, hw02⟩ := OpenReg.exists_lift W.m (spMap (algebraMap (PowerSeries ℂ) (DualNumber (PowerSeries ℂ))))
          w (by rw [htan.1])
        subst hw02
        have hw0 : w0 ≫ W.t.G.hom = spMap (algebraMap (PowerSeries ℂ) (DualNumber (PowerSeries ℂ))) ≫ 𝟙 _ :=
          hw01.trans (Category.comp_id _).symm
        let W0 : epsR (PowerSeries ℂ) ⟶ W.t.G := Over.homMk w0 hw01
        have t0 : IsTangent W0 := (DepthExt.tan_iff W.t W0).2 ((OpenReg.tan_iff W.m (Category.id_comp χ) hw0).1 htan)
        have e0 : ∀ x : 𝓞 E, (W0 ≫ W.t.act.act x).left =
            spMap (epsScaleR (PowerSeries.C (R := ℂ) ((σ.comp (embK c τ)) x))) ≫ W0.left := fun x =>
          (OpenReg.eig_iff W.m hw0 x _).1 (heig x)
        obtain ⟨cf, hcf, hu1⟩ := (hv τ).2 W0 t0 e0
        refine ⟨cf, ?_, fun cf' hcf' => hu1 cf' ?_⟩
        · exact (OpenReg.comb_iff W.m (Category.id_comp χ) (hw τ) cf hw0).2
            ((DepthExt.comb_iff W.t (v τ) cf W0).1 hcf)
        · exact (DepthExt.comb_iff W.t (v τ) cf' W0).2
            ((OpenReg.comb_iff W.m (Category.id_comp χ) (hw τ) cf' hw0).1 hcf') }
  refine ⟨χ', g, hχ'2, ?_, fun τ k => ?_, ?_⟩
  · rw [← hzF]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hχ'1]
      exact hz
    · rw [Category.assoc, Category.assoc, hχ'2, Y.jQ_over, hzF, Descent.ptF_snd, OpenReg.spMap_comp, hFr]
  · obtain ⟨v1, u', hL, h1, h2, h3⟩ := hu τ k
    obtain rfl : v1 = v τ k := (ConstLie.main hG E H Dw l Xo c O β Y ℂ (σ.comp β) a χ W (e τ k)).1.unique hL (hvL τ k)
    refine ⟨u' ≫ φ, ?_, ?_, ?_⟩
    · rw [Category.assoc, hφ, ← Category.assoc, h3, hzF]
    · rw [Category.assoc, h0, h1]
    · rw [Category.assoc, hm, ← Category.assoc, h2, Category.assoc]
  · rw [mem_genBd_iff]
    rw [← hχ'1] at hab
    exact hab

end GlobalTheory.CuspFrom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcOffBoundaryDescendsToModuliLocalization
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

noncomputable section

namespace GlobalTheory.ShFam.BdArc

theorem exists_basicOpen_subset_of_pt {A : Type} [CommRing A] (f : A →+* ℂ) (U : Set (Sp A)) (hU : IsOpen U)
    (h : ∀ s, spMap f s ∈ U) :
    ∃ a : A, f a ≠ 0 ∧ Set.range (spMap (algebraMap A (Localization.Away a))) ⊆ U := by
  let s₀ : PrimeSpectrum ℂ := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨_, ⟨a, rfl⟩, h1, h2⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := A)).exists_subset_of_mem_open (h s₀) hU
  refine ⟨a, ?_, ?_⟩
  · intro h0
    apply h1
    show f a ∈ (⊥ : Ideal ℂ)
    simp [h0]
  · have := PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
    rintro _ ⟨s, rfl⟩
    apply h2
    show _ ∈ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A))
    rw [← this]
    exact ⟨s, rfl⟩

theorem exists_hol_away {A : Type} [CommRing A] (ψ : ℂ → (A →+* ℂ)) (V : Set ℂ)
    (hψ : ∀ b, DifferentiableOn ℂ (fun u => ψ u b) V) (a : A) (ha : ∀ u ∈ V, ψ u a ≠ 0) (u₀ : ℂ) (h₀ : u₀ ∈ V) :
    ∃ ev : ℂ → (Localization.Away a →+* ℂ), (∀ u ∈ V, (ev u).comp (algebraMap A _) = ψ u) ∧
      ∀ t, DifferentiableOn ℂ (fun u => ev u t) V := by
  classical
  let ev : ℂ → (Localization.Away a →+* ℂ) := fun u =>
    if h : u ∈ V then IsLocalization.Away.lift a (g := ψ u) (Ne.isUnit (ha u h))
    else IsLocalization.Away.lift a (g := ψ u₀) (Ne.isUnit (ha u₀ h₀))
  have hev : ∀ u ∈ V, (ev u).comp (algebraMap A _) = ψ u := fun u hu => by
    simp only [ev, dif_pos hu]
    exact IsLocalization.Away.lift_comp a _
  refine ⟨ev, hev, fun t => ?_⟩
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj a t
  refine (((hψ b).div ((hψ a).pow n) fun u hu => pow_ne_zero n (ha u hu))).congr fun u hu => ?_
  have h1 := congrArg (ev u) hb
  have h2 : ∀ z, ev u (algebraMap A _ z) = ψ u z := fun z => RingHom.congr_fun (hev u hu) z
  rw [map_mul, map_pow, h2, h2] at h1
  show _ = ψ u b / ψ u a ^ n
  rw [eq_div_iff (pow_ne_zero n (ha u hu)), h1]

theorem spMap_comp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem dualMap_comp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) :=
  by
    ext z <;> simp [dualMap]

theorem spMap_dualMap_sq {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    spMap (dualMap f) ≫ spMap (algebraMap A (DualNumber A)) = spMap (algebraMap B (DualNumber B)) ≫ spMap f := by
  rw [spMap_comp_comp, spMap_comp_comp]
  congr 1
  exact RingHom.ext fun z => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem arc_descends_to_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)), IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → ∀ u₀ ∈ Metric.ball (0 : ℂ) r, u₀ ≠ 0 → ∃ (R : Type) (_ : CommRing R) (xR : Sp R ⟶ Xo.X) (vR : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)) (ev : ℂ → (R →+* ℂ)) (V : Set ℂ), IsOpen V ∧ u₀ ∈ V ∧ (∀ t, DifferentiableOn ℂ (fun u => ev u t) V) ∧ ∀ u ∈ V, (y u).x = spMap (show R →+* CAt σ from ev u) ≫ xR ∧ ∀ τ i, (y u).u τ i = spMap (dualMap (show R →+* CAt σ from ev u)) ≫ vR τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ A _ φ x fr ψ r y harc hm u₀ hu₀ hne
  haveI := Z.jQ_open
  obtain ⟨a, ha, hsub⟩ := exists_basicOpen_subset_of_pt (ψ u₀) (x ⁻¹' Set.range Z.jQ)
    ((IsOpenImmersion.isOpen_range Z.jQ).preimage x.continuous) (fun s => by
      have h := (hm u₀ hu₀ hne).1
      refine ⟨GlobalTheory.AllWt.ptF (y u₀) s, ?_⟩
      exact (congrArg (fun g => g s) h :))
  have hopen : IsOpen {u | u ∈ Metric.ball (0 : ℂ) r ∧ ψ u a ≠ 0} :=
    ((harc.1.2 a).continuousOn).isOpen_inter_preimage Metric.isOpen_ball (isOpen_ne (x := (0 : ℂ)))
  let V : Set ℂ := {u | u ∈ Metric.ball (0 : ℂ) r ∧ ψ u a ≠ 0} ∩ {u | u ≠ 0}
  obtain ⟨ev, hev, hd⟩ := exists_hol_away ψ V (fun b => (harc.1.2 b).mono fun u hu => hu.1.1) a
    (fun u hu => hu.1.2) u₀ ⟨⟨hu₀, ha⟩, hne⟩
  let R := Localization.Away a
  let ι : A →+* R := algebraMap A R
  have hr : Set.range (spMap ι ≫ x) ⊆ Set.range Z.jQ := by
    rintro _ ⟨s, rfl⟩
    exact hsub ⟨s, rfl⟩
  let x' : Sp R ⟶ Xo.XF c := IsOpenImmersion.lift Z.jQ (spMap ι ≫ x) hr
  have hx' : x' ≫ Z.jQ = spMap ι ≫ x := IsOpenImmersion.lift_fac _ _ _
  have P : IsPullback Z.m.φ Z.oF.t.G.hom Z.t.G.hom (Z.jQ ≫ genι Z) := Z.m.cart.1
  have hw : ∀ τ i, (spMap (dualMap ι) ≫ fr.v τ i) ≫ Z.t.G.hom =
      (spMap (algebraMap R (DualNumber R)) ≫ x') ≫ Z.jQ ≫ genι Z := fun τ i => by
    rw [Category.assoc, (fr.tan τ i).1, ← Category.assoc, spMap_dualMap_sq, Category.assoc, Category.assoc,
      ← Category.assoc x', hx', Category.assoc]
  refine ⟨R, inferInstance, x' ≫ pullback.fst _ _, fun τ i => P.lift _ _ (hw τ i) ≫ Z.m0.toSABMap.φ, ev, V,
    hopen.inter isOpen_ne, ⟨⟨hu₀, ha⟩, hne⟩, hd, fun u hu => ?_⟩
  obtain ⟨h1, h2⟩ := hm u hu.1.1 hu.2
  let e : R →+* CAt σ := ev u
  have he : e.comp ι = (show A →+* CAt σ from ψ u) := hev u hu
  have hp : GlobalTheory.AllWt.ptF (y u) = spMap e ≫ x' := by
    rw [← cancel_mono Z.jQ, h1, Category.assoc, hx', ← Category.assoc, spMap_comp_comp, he]
  refine ⟨?_, fun τ i => ?_⟩
  · show _ = spMap e ≫ x' ≫ _
    rw [← Category.assoc, ← hp]
    exact (pullback.lift_fst _ _ _).symm
  · obtain ⟨w, hw1, hw2, hw3⟩ := h2 τ i
    show _ = spMap (dualMap e) ≫ P.lift _ _ (hw τ i) ≫ _
    rw [← hw2, ← Category.assoc]
    congr 1
    apply P.hom_ext
    · rw [hw3, Category.assoc, P.lift_fst, ← Category.assoc, spMap_comp_comp, dualMap_comp_comp, he]
    · rw [hw1, Category.assoc, P.lift_snd, ← Category.assoc, spMap_dualMap_sq, Category.assoc, hp]

end GlobalTheory.ShFam.BdArc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcsOnFlowLinesOfAnalyticModelOnOrbit
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

namespace GlobalTheory.CuspFrom

theorem linearIndependent_symm_single {g : ℕ} {T : Type} {m : T → ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ))
    (L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : T) :
    LinearIndependent ℂ (fun i : Fin (m τ) => L.symm (Pi.single (e.symm ⟨τ, i⟩) 1)) := by
  have hinj : Function.Injective fun i : Fin (m τ) => e.symm ⟨τ, i⟩ :=
    e.symm.injective.comp sigma_mk_injective
  have := ((Pi.basisFun ℂ (Fin g)).linearIndependent.comp _ hinj).map' L.symm.toLinearMap L.symm.ker
  have hf : (fun i : Fin (m τ) => L.symm (Pi.single (e.symm ⟨τ, i⟩) 1)) =
      L.symm.toLinearMap ∘ ((Pi.basisFun ℂ (Fin g)) ∘ fun i : Fin (m τ) => e.symm ⟨τ, i⟩) := by
    funext i
    simp
  rw [hf]
  exact this

theorem point_exp_eq_of_isometry_levels (hK : Known) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty) (i i' : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ))
    (P' : (Fu.Di i').La →+ (Fin g → ℂ)) (gm : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i').La)
    (L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hpq : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H D.p D.q ty) (hA' : ∀ a, ∃ x, gm (Fu.t i a) = Fu.t i' a + l.A • x)
    (hP : IsPeriod (Fu.Di i) ty P) (hP' : IsPeriod (Fu.Di i') ty P')
    (hiso : ∀ u v, (Fu.Di i').EF (gm u) (gm v) = (Fu.Di i).EF u v)
    (hM : ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gm (Fu.t i v) = Fu.t i' v + l.M • e)
    (hL : ∀ u, P' (gm u) = L (P u)) : Fu.u i P = Fu.u i' P' ∧ ∀ z, (Fu.ex i' P' (L z)).left = (Fu.ex i P z).left := by
  have hu : Fu.u i P = Fu.u i' P' :=
    (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed hK.theta hK.laws E H D l Xo σ g ty hpq hσ hty (Fu.Di i) (Fu.Di i')
      (Fu.t i) (Fu.t i') P P' (Fu.u i P) (Fu.u i' P') (Fu.ex i P) (Fu.ex i' P')
      ⟨Fu.over_σ i P hP, hP, ⟨Fu.ex_add i P hP, Fu.ex_onto i P hP, GlobalTheory.ArcCM.isHolTo_exp_of_isPeriod Fu i P hP,
        (Fu.ex_diff i P hP).1, (Fu.ex_diff i P hP).2⟩, Fu.ex_ker i P hP, Fu.ex_lin i P hP, Fu.ex_weil i P hP,
        Fu.ex_eta i P hP, Fu.ex_etaA i P hP⟩
      ⟨Fu.over_σ i' P' hP', hP', ⟨Fu.ex_add i' P' hP', Fu.ex_onto i' P' hP', GlobalTheory.ArcCM.isHolTo_exp_of_isPeriod Fu i' P' hP',
        (Fu.ex_diff i' P' hP').1, (Fu.ex_diff i' P' hP').2⟩, Fu.ex_ker i' P' hP', Fu.ex_lin i' P' hP',
        Fu.ex_weil i' P' hP', Fu.ex_eta i' P' hP', Fu.ex_etaA i' P' hP'⟩).2 ⟨gm, L, hiso, hM, hA', hL⟩
  obtain rfl : i = i' := Fu.disj i i' P P' hP hP' hu
  letI : StarRing (𝓞 E) := H.starRing
  exact GlobalTheory.ArcPts.exp_eq_of_matching_markings E H D l Xo σ g ty Fu i P P' gm L rfl hP hP' hiso hM hA' hL

theorem flowTie_of_onOrbit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn₀ aC), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → letI := H.starRing; ∀ (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] Λ.A.La) (ξ : Module.Dual ℤ Λ.A.X), OnOrbit Uw k ξ' x Λ.A gam ξ → ξ ≠ 0 → Module.finrank (𝓞 E) Λ.A.X = 1 → (∀ v, Λ.Lifts (aC.eta v) (gam (Uw.F.t (Uw.ik k) v))) → (∀ v, Λ.Lifts (aC.etaA v) (gam (Uw.F.t (Uw.ik k) v))) → ∀ (O : Type) [CommRing O] (β : O →+* c.F), FlowTie Uw (aC.restrict β) k ξ' x := by
  intro E _ _ _ H Dw l Xo c _ _ σ r U Uw k ξ' x aC Λ hσ hU hξ hx gam ξ hO hξ0 hY hLM hLA O _ β Y χ W Ha
  have hK : Known := GlobalTheory.ArcCM.known_holds
  let := H.starRing
  let Λ' : GtAn₀ (aC.restrict β) := ⟨Λ.toGtDict, Λ.be_eq⟩
  obtain ⟨g₁, h₁, e1, e2, e3, e4⟩ :=
    GlobalTheory.ArcCompare.holArc_agrees hK E H Dw l Xo c σ O β Y (aC.restrict β) χ W Uw.g _ Uw.F Ha Λ'
  obtain ⟨o1, ⟨t', o2, o3⟩, T₀, o4⟩ := hO
  have hw : max Ha.T T₀ < (((max Ha.T T₀ + 1 : ℝ) : ℂ) * Complex.I).im := by simp
  generalize (((max Ha.T T₀ + 1 : ℝ) : ℂ) * Complex.I) = w₁ at hw
  obtain ⟨hw1, hw2⟩ := max_lt_iff.1 hw
  obtain ⟨s₁, hs₁, h, hh⟩ := o4 w₁ hw2
  let gm : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La := g₁.trans gam.symm
  let L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ) := h₁.trans h.symm
  have hgm : ∀ u, gam (gm u) = g₁ u := fun u => gam.apply_symm_apply _
  have hg1 : ∀ v, g₁ (gm.symm v) = gam v := fun v => by rw [← hgm, gm.apply_symm_apply]
  have hEF : ∀ u v, (Uw.F.Di (Uw.ik k)).EF (gm u) (gm v) = (Uw.F.Di Ha.i).EF u v := fun u v => by
    rw [← o1, hgm, hgm]; exact e4 u v
  have hEF' : ∀ u v, (Uw.F.Di (Uw.ik k)).EF u v = (Uw.F.Di Ha.i).EF (gm.symm u) (gm.symm v) := fun u v => by
    rw [← hEF, gm.apply_symm_apply, gm.apply_symm_apply]
  have hP : ∀ u, Uw.Pm k ⟨_, hs₁⟩ (gm u) = L (Ha.Pw w₁ u) := fun u => by
    apply h.injective
    rw [hh, hgm]
    exact (e3 w₁ u).symm.trans (h.apply_symm_apply _).symm
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact absurd (Subsingleton.elim _ _) hξ.2.2
    · exact hr
  have hpq : 1 ≤ Dw.p + Dw.q := by
    rw [← hU.1]
    exact hr
  have hty := (GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw Uw.g Uw.e
  have h0 : ∀ v, h₁ (Ha.P₀ (Uw.F.t Ha.i v)) = Λ.A.P0 (g₁ (Uw.F.t Ha.i v)) := fun v => by
    have := e3 0 (Uw.F.t Ha.i v)
    rw [Ha.Pw_eq, zero_smul, add_zero] at this
    exact this.trans (by rw [AnArc.Pw_apply, zero_smul, add_zero])
  have hlev : ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∃ e, gm (Uw.F.t Ha.i v) = Uw.F.t (Uw.ik k) v + l.M • e := by
    intro v hv
    obtain ⟨q, q1, q2, q3⟩ := Ha.levelM v hv
    have hq : q = Λ.toGtDict.qk l.M (g₁ (Uw.F.t Ha.i v)) := by
      refine TorusExt.qk_ext (q1.trans (e2 _).symm) (q2.trans ?_)
      rw [← e1, map_smul, h0]
      rfl
    have l1 : Λ.Lifts (aC.eta v) (g₁ (Uw.F.t Ha.i v)) := fun q' hq' => hq ▸ q3 q' hq'
    obtain ⟨la, hla⟩ := Λ.exists_lifts (aC.eta v)
    obtain ⟨m₁, hm₁⟩ := (hla _).1 l1
    obtain ⟨m₂, hm₂⟩ := (hla _).1 (hLM v)
    refine ⟨gam.symm (m₁ - m₂), gam.injective ?_⟩
    rw [hgm, map_add (f := _), map_nsmul, gam.apply_symm_apply, hm₂, nsmul_sub]
    exact hm₁.trans (by abel)
  have hlevA : ∀ v, ∃ e, gm (Uw.F.t Ha.i v) = Uw.F.t (Uw.ik k) v + l.A • e := by
    intro v
    obtain ⟨q, q1, q2, q3⟩ := Ha.levelA v
    have hq : q = Λ.toGtDict.qk l.A (g₁ (Uw.F.t Ha.i v)) := by
      refine TorusExt.qk_ext (q1.trans (e2 _).symm) (q2.trans ?_)
      rw [← e1, map_smul, h0]
      rfl
    have l1 : Λ.Lifts (aC.etaA v) (g₁ (Uw.F.t Ha.i v)) := fun q' hq' => hq ▸ q3 q' hq'
    obtain ⟨la, hla⟩ := Λ.exists_lifts (aC.etaA v)
    obtain ⟨m₁, hm₁⟩ := (hla _).1 l1
    obtain ⟨m₂, hm₂⟩ := (hla _).1 (hLA v)
    refine ⟨gam.symm (m₁ - m₂), gam.injective ?_⟩
    rw [hgm, map_add (f := _), map_nsmul, gam.apply_symm_apply, hm₂, nsmul_sub]
    exact hm₁.trans (by abel)
  obtain ⟨-, p2⟩ := point_exp_eq_of_isometry_levels hK Uw.F Ha.i (Uw.ik k) (Ha.Pw w₁) (Uw.Pm k ⟨_, hs₁⟩) gm L hpq
    hσ hty hlevA (Ha.period w₁ hw1) (Uw.period k _) hEF hlev hP
  obtain ⟨nn, n1, n2, n3, n4, n5, n6⟩ :=
    GlobalTheory.ArcQ.holArc_nilpotent E H Dw l Xo c σ O β Y (aC.restrict β) χ W _ _ Uw.F Ha
  have hlin : ∀ w w' v, Ha.Pw w v = Ha.Pw w' v + (w - w') • Ha.Pw w' (nn v) := by
    intro w w' v
    rw [Ha.Pw_eq, Ha.Pw_eq, Ha.Pw_eq, n1 (nn v), n4 _ (n3 v), map_zero, smul_zero, add_zero, ← n1, sub_smul]
    abel
  have hyg : ∀ u, Ha.y u = Λ.eX (g₁ u).y := fun u => (e2 u).symm
  let nn' : (Uw.F.Di (Uw.ik k)).La →ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La :=
    gm.toLinearMap ∘ₗ nn ∘ₗ gm.symm.toLinearMap
  have hnn'e : ∀ v, gm.symm (nn' v) = nn (gm.symm v) := fun v => gm.symm_apply_apply _
  let y'' : (Uw.F.Di (Uw.ik k)).La →ₗ[𝓞 E] Λ.A.X := Λ.A.yLin ∘ₗ gam.toLinearMap
  have hy'' : Function.Surjective y'' := Λ.A.yLin_surjective.comp gam.surjective
  have hnn'' : ∀ v v', -(Uw.F.Di (Uw.ik k)).EF (nn' v) v' = Λ.A.be (y'' v) (y'' v') := by
    intro v v'
    rw [hEF', hnn'e, n2, hyg, hyg, hg1, hg1]
    exact Λ.be_eq _ _
  have hrep'' : ∀ η : Module.Dual ℤ Λ.A.X, ∃ t, ∀ v, -(Uw.F.Di (Uw.ik k)).EF t v = η (y'' v) := by
    intro η
    obtain ⟨t, ht, -⟩ := n6 (η.toAddMonoidHom.comp Λ.eX.symm.toLinearMap.toAddMonoidHom).toIntLinearMap
    refine ⟨gm t, fun v => ?_⟩
    rw [hEF', gm.symm_apply_apply, ht, hyg, hg1]
    show η (Λ.eX.symm (Λ.eX _)) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have hyt : y'' t' = 0 := by
    have hy0 := n5 (gm.symm t') fun v' hv' => by
      have h3 := o3 (gm v')
      have h4 : (g₁ v').y = 0 := (map_eq_zero_iff _ Λ.eX.injective).1 (by rw [← hyg]; exact hv')
      rw [hgm, h4, map_zero] at h3
      rw [← hEF, gm.apply_symm_apply]
      exact neg_eq_zero.1 h3
    rw [hyg, hg1] at hy0
    exact (map_eq_zero_iff _ Λ.eX.injective).1 hy0
  let x₀ : (U.X k).dom := ⟨_, hs₁⟩
  obtain ⟨-, -, -, -, Hm, hHm⟩ := Uw.period k x₀
  have hκ := (_root_.GlobalTheory.RiemMaj.riemann_eq_majorant E H Dw l Xo c σ r U Uw k x₀ Hm hσ hU hHm).2.1 hr
  obtain ⟨sE, -, hbe, hsp, -, hform⟩ := GlobalTheory.ArcFlow.rank_one (U.X k) (Uw.φ k) _ (Uw.iso k) y'' hY hκ hy''
    Λ.A.be Λ.A.be_symm Λ.A.be_pos nn' hnn'' hrep'' ξ hξ0 t' o3 hyt
  have hform' : ∀ v, (Uw.φ k (nn' v) : Fin r → E) =
      (-(sE * (U.X k).κ0 * herm (U.X k).Gm (Uw.φ k v : Fin r → E) ξ')) • ξ' := fun v => by
    rw [hform v, o2]
  have hξ'0 : herm (U.X k).Gm ξ' ξ' = 0 := hξ.2.1
  have hLs : ∀ z, (Uw.F.ex Ha.i (Ha.Pw w₁) (L.symm z)).left = (Uw.F.ex (Uw.ik k) (Uw.Pm k x₀) z).left := fun z => by
    rw [← p2 (L.symm z), L.apply_symm_apply]
  refine ⟨Ha.T, fun τ => s₁ τ - w₁ * (((τ.1 sE).re : ℝ) : ℂ), fun τ => (τ.1 sE).re,
    fun τ i => L.symm (Pi.single (Uw.e.symm ⟨τ, i⟩) 1), fun τ => hsp τ.1, fun τ => ⟨?_, fun i jj hij => ?_⟩,
    fun w hw => ?_⟩
  · exact linearIndependent_symm_single Uw.e L τ
  · refine GlobalTheory.DerivativeDetermination.type_map Uw.e Uw.F (Uw.period k x₀) (Ha.period w₁ hw1) L.symm.toLinearMap hLs τ _
      (fun j hj => ?_) jj hij
    by_cases hjj : j = Uw.e.symm ⟨τ, i⟩
    · subst hjj; simp
    · exact absurd (Pi.single_eq_of_ne hjj _) hj
  · let Pw' : (Uw.F.Di (Uw.ik k)).La →+ (Fin Uw.g → ℂ) :=
      L.toLinearMap.toAddMonoidHom.comp ((Ha.Pw w).comp gm.symm.toLinearMap.toAddMonoidHom)
    have hg' : ∀ a b, (Uw.F.Di Ha.i).EF (gm.symm a) (gm.symm b) = (Uw.F.Di (Uw.ik k)).EF a b :=
      fun a b => (hEF' a b).symm
    have hPer : IsPeriod (Uw.F.Di (Uw.ik k)) (fun j => relab c σ (Uw.e j).1) Pw' := by
      have := GlobalTheory.UnifCompare.isPeriod_move
        (GlobalTheory.ClassUniq.isPeriod_comp_isometry gm.symm hg' (Ha.period w₁ hw1)) (Uw.period k x₀)
        (GlobalTheory.ClassUniq.isPeriod_comp_isometry gm.symm hg' (Ha.period w hw)) (LinearEquiv.refl _ _) L
        (fun _ _ => rfl) (fun a => by
          show Uw.Pm k x₀ a = L (Ha.Pw w₁ (gm.symm a))
          rw [← hP, gm.apply_symm_apply])
      exact this
    have hPx : ∀ v, Pw' v = Uw.Pm k x₀ v + (w - w₁) • Uw.Pm k x₀ (nn' v) := by
      intro v
      have a1 := hP (gm.symm v)
      rw [gm.apply_symm_apply] at a1
      have a2 := hP (nn (gm.symm v))
      show L (Ha.Pw w (gm.symm v)) = _
      rw [hlin w w₁, map_add (f := _), map_smul, ← a1, ← a2]
      rfl
    obtain ⟨hxw, hPw'⟩ := GlobalTheory.ArcFlow.flow_period Uw hσ hU k hκ nn' ξ' hξ'0 sE hbe.1 hform' x₀ (w - w₁) Pw' hPer hPx
    have heq : (U.X k).flow ξ' (fun τ => (w - w₁) * ((τ.1 sE).re : ℂ)) x₀.1 =
        (U.X k).flow ξ' (fun τ => (s₁ τ - w₁ * (((τ.1 sE).re : ℝ) : ℂ)) + w * (((τ.1 sE).re : ℝ) : ℂ)) x := by
      rw [ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.flow_flow (U.X k) hξ'0]
      congr 1
      funext τ
      simp only [Pi.add_apply]
      ring
    obtain ⟨q1, q2⟩ := point_exp_eq_of_isometry_levels hK Uw.F Ha.i (Uw.ik k) (Ha.Pw w) (Uw.Pm k ⟨_, hxw⟩) gm L
      hpq hσ hty hlevA (Ha.period w hw) (Uw.period k _) hEF hlev (fun u => by
        rw [hPw']
        show L (Ha.Pw w (gm.symm (gm u))) = _
        rw [gm.symm_apply_apply])
    refine ⟨heq ▸ hxw, ?_⟩
    have hpt : (⟨_, heq ▸ hxw⟩ : (U.X k).dom) = ⟨_, hxw⟩ := Subtype.ext heq.symm
    rw [hpt]
    have hlie := Uw.lie k ⟨_, hxw⟩
    refine ⟨hlie.1.trans q1.symm, fun τ i => ?_⟩
    refine (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ _ _ Uw.F Ha.i (Ha.Pw w) (Ha.period w hw) (Uw.ik k)
      (Uw.Pm k ⟨_, hxw⟩) L.toLinearMap (Uw.period k _) q2 _ _).2 ?_
    rw [show L.toLinearMap (L.symm (Pi.single (Uw.e.symm ⟨τ, i⟩) 1)) = Pi.single (Uw.e.symm ⟨τ, i⟩) 1 from
      L.apply_symm_apply _]
    exact hlie.2 τ i

end GlobalTheory.CuspFrom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspPnormLeExpNegOfIsIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pnorm_le_exp_neg_of_mem_SS_of_isIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (la : Wt X.Ψ N) (P : Frame X.Ψ N → ℂ) (ξ : Fin N → E), P ∈ X.SS la → X.IsIso ξ → ∃ C c : ℝ, 0 < c ∧ ∀ x ∈ X.dom, ∀ t : ℝ, 1 ≤ t → (∀ τ, t ≤ X.tt ξ x τ) → X.pnorm la P x ≤ C * Real.exp (-c * t) := by
  first | exact @GlobalTheory.cusp_pnorm_le_exp_neg_of_isIso | exact GlobalTheory.cusp_pnorm_le_exp_neg_of_isIso | (intros; apply GlobalTheory.cusp_pnorm_le_exp_neg_of_isIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseChange
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

theorem GlobalTheory.ShFam.EigFrame.exists_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (A B : Type) [CommRing A] [CommRing B] (φ : c.F →+* A) (x : Sp A ⟶ Z.X) (fr : EigFrame Z φ x) (ψ : A →+* B), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z A B _ _ φ x fr ψ
  open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.LocM GlobalTheory.LocM.FrameBC in
  have h : GlobalTheory.LocM.IsFrame Z.t (ψ.comp φ) (spMap ψ ≫ x) ((fun τ i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i)) := by
    letI : Algebra c.F A := φ.toAlgebra
    letI : Algebra c.F B := (ψ.comp φ).toAlgebra
    let v : ∀ τ, Fin (Dw.mult τ) → TanM x Z.t.G := fun τ i => tanOf (fr.tan τ i)
    have eps_dual (a : A) : spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (epsMul a) = spMap (epsMul (ψ a)) ≫ spMap (Formalism.L2.Pj.dualMap ψ) := by
      rw [spMap_comp_spMap, spMap_comp_spMap]
      congr 1
      refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [Formalism.L2.Pj.dualMap, epsMul, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map, smul_eq_mul, mul_comm]
    have he : ∀ τ i (a : 𝓞 E), (fun τ i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i) τ i ≫ (Z.t.act.act a).left =
        spMap (epsMul ((ψ.comp φ) (embK c τ a))) ≫ (fun τ i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i) τ i := fun τ i a => by
      show (spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i) ≫ _ = _ ≫ spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i
      rw [Category.assoc, fr.eig τ i a, ← Category.assoc, eps_dual, Category.assoc, RingHom.comp_apply]
    have h1 := full_of_eig c v (fun τ i => (eig_iff c τ (v τ i)).1 (fr.eig τ i)) fun τ n hn => by
      exact (existsUnique_congr fun a => LieMet.isComb_iff (v τ) a n).1 (fr.basis τ _ (isTan_tv n) ((eig_iff c τ n).2 hn))
    have h2 : Full fun k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => resM ψ (v k.1 k.2) := by
      have h := full_equiv (eB Dw).symm (full_bc ψ (full_equiv (eB Dw) h1))
      exact (funext fun k => congrArg (fun j : IxB Dw => resM ψ (v j.1 j.2)) ((eB Dw).apply_symm_apply k)) ▸ h
    refine ⟨fun τ i => ⟨isTan_map ψ rfl (fr.tan τ i), he τ i⟩, fun τ w hw hwe => ?_⟩
    have h3 := eig_of_full c (fun τ i => resM ψ (v τ i)) (fun τ i => (eig_iff c τ _).1 (he τ i)) h2 τ (tanOf hw)
      ((eig_iff c τ _).1 hwe)
    exact (existsUnique_congr fun a => LieMet.isComb_iff (fun i => resM ψ (v τ i)) a (tanOf hw)).2 h3
  exact ⟨⟨_, fun τ i => (h.1 τ i).1, fun τ i => (h.1 τ i).2, h.2⟩, fun _ _ => rfl⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocExtANat
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM

namespace GlobalTheory.LocM

theorem exists_loc_extA_nat :
    ∀ (D : D7) (N j p : ℕ), ∃ L : ModuliIntegralCharts.Loc D N j p, Nonempty (ModuliIntegralCharts.ExtA D L) :=
  fun D N j p =>
    ⟨Formalism.MainNotions.DIV.Inh.LocalProvisionModel.locM D N j p (Formalism.MainNotions.DIV.Inh.LocalProvisionModel.mpTrivialAb D p (Formalism.MainNotions.DIV.Inh.nonempty_coefficient_field p).some),
      ⟨Formalism.MainNotions.DIV.Inh.LocalProvisionModel.extM D N j p (Formalism.MainNotions.DIV.Inh.LocalProvisionModel.mpTrivialAb D p (Formalism.MainNotions.DIV.Inh.nonempty_coefficient_field p).some)⟩⟩

end GlobalTheory.LocM
end

