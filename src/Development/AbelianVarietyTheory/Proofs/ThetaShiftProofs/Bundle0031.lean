module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PmapsOfGenRelR
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsGtPtGenRelRField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmpCongrOfExEq
section
noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem cmp_congr_of_ex_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (Fu.Di i) ty P) (k : ℕ) (hk : 0 < k) (a b : (Fu.Di i).La)
    (hab : Fu.ex i P ((k : ℂ)⁻¹ • P a) = Fu.ex i P ((k : ℂ)⁻¹ • P b)) : ∃ e, a = b + k • e := by
  have h1 : Fu.ex i P ((k : ℂ)⁻¹ • P a - (k : ℂ)⁻¹ • P b) = 1 := by
    have h2 := Fu.ex_add i P hP ((k : ℂ)⁻¹ • P a - (k : ℂ)⁻¹ • P b) ((k : ℂ)⁻¹ • P b)
    rw [sub_add_cancel, hab] at h2
    exact mul_eq_right.1 h2.symm
  obtain ⟨e, he⟩ := (Fu.ex_ker i P hP _).1 h1
  refine ⟨e, hP.2.1 ?_⟩
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [map_add (f := _), map_nsmul, he, ← Nat.cast_smul_eq_nsmul ℂ, smul_sub, smul_inv_smul₀ hk', smul_inv_smul₀ hk']
  abel

theorem cmp_level {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty)
    (A : AnArc (𝓞 E)) (w : ℂ) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (Fu.Di i) ty P) (y₀ : Sp ℂ ⟶ Xo.X) (hy : Fu.u i P = y₀)
    (π : A.V → (Over.mk y₀ ⟶ Xo.univ.t.G)) (h : A.V ≃L[ℂ] (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[𝓞 E] A.La)
    (hex : ∀ v, (Fu.ex i P (h v)).left = (π v).left) (hPg : ∀ u, P u = h (A.Pw w (gam u)))
    (k : ℕ) (hk : 0 < k) (x : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (a : (Fu.Di i).La) (la : A.La)
    (h1 : toUnit _ ≫ x = Fu.ex i P ((k : ℂ)⁻¹ • P a)) (h2 : toUnit _ ≫ x = π ((k : ℂ)⁻¹ • A.Pw w la)) :
    ∃ e, gam a = la + k • e := by
  subst hy
  have h3 : ∀ v, Fu.ex i P (h v) = π v := fun v => Over.OverMorphism.ext (hex v)
  obtain ⟨e, he⟩ := cmp_congr_of_ex_eq Fu i P hP k hk a (gam.symm la) (by
    rw [← h1, h2, ← h3, map_smul, hPg (gam.symm la), gam.apply_symm_apply])
  exact ⟨gam e, by rw [he, map_add (f := _), map_nsmul, gam.apply_symm_apply]⟩

theorem exists_cmp : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (A : AnArc (𝓞 E)) (lin : ℂ → A.La → A.V →ₗ[ℂ] ℂ) (cst : ℂ → A.La → ℂ) (T : ℝ) (yw : ℂ → (Sp ℂ ⟶ Xo.X)) (π : ∀ w, A.V → (Over.mk (yw w) ⟶ Xo.univ.t.G)) (fr : ℂ → Xo.univ.t.PP.L.ι → A.V → ℂ) (laA laM : D.La → A.La), (inferInstance : StarRing (𝓞 E)) = H.starRing → (∀ w la la', lin w la (A.Pw w la') - lin w la' (A.Pw w la) = -(2 * Real.pi * Complex.I) * A.EF la la') → Module.finrank ℂ A.V = g → IsHolTo {w : ℂ | T < w.im} yw → (∀ w : ℂ, T < w.im → yw w ≫ Xo.s = spMap σ ∧ IsFibAt A Xo.univ.t lin cst w (yw w) (π w) (fr w) ∧ (Function.Surjective (π w) → (∀ v, toUnit _ ≫ Xo.univ.etaA v = π w ((l.A : ℂ)⁻¹ • A.Pw w (laA v))) ∧ ∀ v ∈ idealPart D l, toUnit _ ≫ Xo.univ.eta v = π w ((l.M : ℂ)⁻¹ • A.Pw w (laM v)))) → ∃ K : Cmp Fu A yw π laA laM, T ≤ K.T := by
  intro hL hL2 E _ _ _ H _ D l Xo σ g ty Fu A lin cst T yw π fr laA laM hstar hlin hrk hhol hw
  obtain ⟨i, hi⟩ := GlobalTheory.familyUnif_component_const E H D l Xo σ g ty Fu T yw hhol fun w h => (hw w h).1
  obtain ⟨T₀, hT₀⟩ := GlobalTheory.fibre_comparison hL hL2 E H D l Xo σ g ty Fu A lin cst hlin hrk
  obtain ⟨T₁, hT₁⟩ := A.exists_BwMat_posDef
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le

  have key : ∀ w : ℂ, max T (max T₀ T₁) < w.im →
      ∃ (P : (Fu.Di i).La →+ (Fin g → ℂ)) (h : A.V ≃L[ℂ] (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[𝓞 E] A.La),
        IsPeriod (Fu.Di i) ty P ∧ Fu.u i P = yw w ∧ (∀ v, (Fu.ex i P (h v)).left = (π w v).left) ∧
        (∀ u, P u = h (A.Pw w (gam u))) ∧ (∀ u v, A.EF (gam u) (gam v) = (Fu.Di i).EF u v) ∧
        (∀ (e : 𝓞 E) v k, h (A.actV e v) k = ty k (e : E) * h v k) ∧
        (∀ v, ∃ e, gam (Fu.t i v) = laA v + l.A • e) ∧
        ∀ v ∈ idealPart D l, ∃ e, gam (Fu.t i v) = laM v + l.M • e := by
    intro w hwT
    have h1 : T < w.im := lt_of_le_of_lt (le_max_left _ _) hwT
    have h2 : T₀ < w.im := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hwT
    obtain ⟨P, hP, hu⟩ := hi w h1
    obtain ⟨-, hfib, hlev⟩ := hw w h1
    obtain ⟨hs, h, gam, hex, hPg, hEF, hact⟩ := hT₀ w i P (yw w) (π w) (fr w) h2 hP hu hfib
    obtain ⟨hA, hMM⟩ := hlev hs
    exact ⟨P, h, gam, hP, hu, hex, hPg, hEF, hact,
      fun v => cmp_level Fu A w i P hP _ hu (π w) h gam hex hPg l.A l.A_pos _ _ _ (Fu.ex_etaA i P hP v) (hA v),
      fun v hv => cmp_level Fu A w i P hP _ hu (π w) h gam hex hPg l.M hM _ _ _ (Fu.ex_eta i P hP v hv) (hMM v hv)⟩
  obtain ⟨-, h₁, gam₁, -, -, -, -, hEF₁, hact₁, hA₁, hM₁⟩ :=
    key (((max T (max T₀ T₁) + 1 : ℝ) : ℂ) * Complex.I) (by simp)
  let Pw : ℂ → ((Fu.Di i).La →+ (Fin g → ℂ)) := fun w =>
    (h₁.toLinearEquiv.toLinearMap.toAddMonoidHom.comp (A.Pw w)).comp gam₁.toLinearMap.toAddMonoidHom
  have hPw : ∀ w u, Pw w u = h₁ (A.Pw w (gam₁ u)) := fun _ _ => rfl
  have hper : ∀ w : ℂ, max T (max T₀ T₁) < w.im → IsPeriod (Fu.Di i) ty (Pw w) := fun w hwT =>
    A.isPeriod (hT₁ w (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hwT)) (Fu.Di i) ty
      h₁.toLinearEquiv hact₁ gam₁.toAddEquiv (fun a x => gam₁.map_smul a x) hEF₁ (Pw w) (hPw w)
  have hmod : ∀ (gam : (Fu.Di i).La ≃ₗ[𝓞 E] A.La) (k : ℕ) (a : (Fu.Di i).La) (la : A.La),
      (∃ e, gam a = la + k • e) → (∃ e, gam₁ a = la + k • e) → ∃ e, (gam.trans gam₁.symm) a = a + k • e := by
    rintro gam k a la ⟨e, he⟩ ⟨e₁, he₁⟩
    refine ⟨gam₁.symm (e - e₁), gam₁.injective ?_⟩
    rw [LinearEquiv.trans_apply, gam₁.apply_symm_apply, map_add (f := _), map_nsmul, gam₁.apply_symm_apply, he, he₁, smul_sub]
    abel
  have hrig : ∀ w : ℂ, max T (max T₀ T₁) < w.im →
      Fu.u i (Pw w) = yw w ∧ ∀ v, (Fu.ex i (Pw w) (h₁ v)).left = (π w v).left := by
    intro w hwT
    obtain ⟨P, h, gam, hP, hu, hex, hPg, hEF, -, hA, hMM⟩ := key w hwT
    obtain ⟨r1, r2⟩ := _root_.GlobalTheory.ArcPts.exp_eq_of_matching_markings E H D l Xo σ g ty Fu i P (Pw w) (gam.trans gam₁.symm)
      (h.symm.trans h₁).toLinearEquiv hstar hP (hper w hwT)
      (fun u v => by
        rw [← hEF₁, LinearEquiv.trans_apply, LinearEquiv.trans_apply, gam₁.apply_symm_apply, gam₁.apply_symm_apply, hEF])
      (fun v hv => hmod gam _ _ _ (hMM v hv) (hM₁ v hv)) (fun v => hmod gam _ _ _ (hA v) (hA₁ v))
      (fun u => by rw [hPw, hPg]; simp)
    refine ⟨r1.symm.trans hu, fun v => ?_⟩
    have := r2 (h v)
    rw [hex] at this
    rw [← this]
    simp
  exact ⟨⟨i, max T (max T₀ T₁), gam₁, h₁, hEF₁, hact₁, Pw, hPw, hper, fun w hwT => (hrig w hwT).1,
    fun w hwT => (hrig w hwT).2, hA₁, hM₁⟩, le_max_left _ _⟩

end GlobalTheory.ArcPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantPointFrameIsFrameWithRigidification
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstFrame

theorem valR_g_self {A : Type} [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} {L : LB Z} (hL : L.IsLB) (x : Sp A ⟶ Z)
    (j : L.ι) (h : ⊤ ≤ x ⁻¹ᵁ L.U j) : valR x (L.U j ⊓ L.U j) (L.g j j).val = 1 := by
  have toStkA_valR {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (z : Sp A) (ht : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
      toStkA z (valR x U a.val) = (gm x z U a).val := by
    have hz : x z ∈ U := ht (show z ∈ (⊤ : (Sp A).Opens) from trivial)
    have e1 : ∀ c, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom c) = c :=
      fun c => congrArg (fun f => CommRingCat.Hom.hom f c) (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of A)))
    rw [valR, dif_pos ht, gm, dif_pos hz]
    show ((Sp A).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ ht).hom a.val))) =
      ((Sp A).presheaf.germ (x ⁻¹ᵁ U) z hz).hom ((x.app U).hom a.val)
    rw [e1]
    exact TopCat.Presheaf.germ_res_apply (Sp A).presheaf (homOfLE ht) z trivial ((x.app U).hom a.val)
  apply toStkA_injective
  rw [toStkA_valR x (L.U j ⊓ L.U j) _ (fun _ hz => ⟨h hz, h hz⟩), map_one]
  exact congrArg Units.val (gm_self hL x _ (h trivial))

theorem valR_rig {A A₀ : Type} [CommRing A] [IsLocalRing A] [CommRing A₀] {B : Over (Sp A)} {B₀ : Over (Sp A₀)}
    [GrpObj B] [IsCommMonObj B] [GrpObj B₀] [IsCommMonObj B₀] {M : LB B.left} {M₀ : LB B₀.left} (f : A₀ →+* A)
    {φ : B.left ⟶ B₀.left} (he : eSec B ≫ φ = spMap f ≫ eSec B₀) (w : LB.Iso M (M₀.pull φ))
    (r : LB.Gen (M.pull (eSec B))) (r₀ : LB.Gen (M₀.pull (eSec B₀)))
    (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec B) (fun _ => 1)) r (rigPullOf φ (spMap f) he M₀ r₀))
    (j : M.ι) (j₀ : M₀.ι) (hj : ⊤ ≤ (show Sp A ⟶ _ from eSec B) ⁻¹ᵁ (LB.div (M₀.pull φ) M).U (fun _ => j₀, j))
    (hj₀ : ⊤ ≤ (M₀.pull (eSec B₀)).U (fun _ => j₀)) :
    f (valR (𝟙 (Sp A₀)) ((M₀.pull (eSec B₀)).U (fun _ => j₀)) (r₀.s (fun _ => j₀)).val) =
      valR (A := A) (eSec B) _ (w.s (fun _ => j₀, j)).val *
        valR (𝟙 (Sp A)) ((M.pull (eSec B)).U (fun _ => j)) (r.s (fun _ => j)).val := by
  have hc := hj (show cpt A ∈ (⊤ : (Sp A).Opens) from trivial)
  have e := gm_maps_pt h (𝟙 (Sp A)) (cpt A) (fun _ => j₀) j hc.1 hc.2
  have hr : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ (M.pull (eSec B)).U (fun _ => j) := fun z hz => mem_pull.2 (hj hz).2
  have h₀ : ⊤ ≤ (𝟙 (Sp A₀)) ⁻¹ᵁ (M₀.pull (eSec B₀)).U (fun _ => j₀) := hj₀
  have h₁ := FormalValue.top_le_comp h₀ (spMap f)
  apply toStkA_injective
  refine Eq.trans ?_ ((congrArg Units.val e).trans ?_)
  · refine (congrArg _ (FormalValue.valR_spMap f _ _ h₀ _).symm).trans ((toStkA_valR _ _ _ h₁ _).trans
      (congrArg Units.val ?_))
    have hm : (𝟙 (Sp A) : Sp A ⟶ Sp A) (cpt A) ∈ ((M₀.pull φ).pull (eSec B)).U (fun _ _ => j₀) := mem_pull.2 hc.1
    refine Eq.trans ?_ ((gm_res (𝟙 (Sp A)) _ _ hm _).trans (gm_pull (𝟙 (Sp A)) (spMap f) _ _ (hj₀ trivial) _)).symm
    rw [Category.id_comp, Category.comp_id]
  · refine Eq.trans ?_ (map_mul _ _ _).symm
    exact (Units.val_mul _ _).trans (congrArg₂ (· * ·) (toStkA_valR (A := A) (eSec B) _ _ hj _).symm
      (toStkA_valR _ _ _ hr _).symm)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] {Y : Model Xo c β} {b : O →+* ℂ} {a : ArcIn D l β ℂ b} {χ : Sp ℂ⟦X⟧ ⟶ Y.X}
  {W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ} {Λ : GtAn a}
  (Ξ : ConstPts W Λ)


omit [Algebra (FractionRing ℂ) ℂ] in
theorem complete : IsAdicComplete ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) ℂ⟦X⟧ := by
  rw [Algebra.algebraMap_self, Ideal.map_id]
  infer_instance

theorem base_comp (v : Λ.A.V) :
    (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.u.ex v.2).left :=
  ((Ξ.g_rel v 0).1 2).trans (congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) (Λ.ex0_b v))

theorem exists_charts (v : Λ.A.V) : ∃ (jM : W.P.D.toPre.P.L.ι) (j₀ : a.D₀.P.L.ι),
    ⊤ ≤ (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) ∧
    ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ a.D₀.P.L.U j₀ := by
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) (cpt ℂ⟦X⟧))
  have h₀ := FrameValue.le_chartAt a.D₀.P.isLB (Λ.u.ex v.2).left
  refine ⟨jM, _, (top_le_iff_cpt _ _).2 ⟨mem_pull.2 ?_, hM⟩, h₀⟩
  exact (congrArg (fun q => q (cpt ℂ⟦X⟧) ∈ a.D₀.P.L.U _) (base_comp Ξ v)).mpr (FormalValue.top_le_comp h₀ _ trivial)

theorem isFrm (v : Λ.A.V) : IsFrm W.P.U.LG.L (Ξ.x v).left (Ξ.τ v) := by
  haveI := complete
  obtain ⟨jM, j₀, hj, h₀⟩ := exists_charts Ξ v
  have hw := FormalValue.isUnit_valR (A := ℂ⟦X⟧) (Ξ.g v).b.left _ hj (W.w.s (fun _ => j₀, jM))
  have hM : ⊤ ≤ FormalValue.basePt (Ξ.g v) ⁻¹ᵁ W.P.D.toPre.P.L.U jM := fun z hz => (hj hz).2
  refine ⟨fun j h => ?_, fun j j' h => ?_⟩
  · refine isUnit_of_mul_isUnit_right ((congrArg IsUnit (Ξ.τ_eq v j jM j₀ h hj)).mpr ?_)
    exact (Units.isUnit _).mul ((Ne.isUnit (Λ.u.fr_ne j₀ v.2 h₀)).map _)
  · have h₁ : ⊤ ≤ (Ξ.x v).left ⁻¹ᵁ W.P.U.LG.L.U j := fun z hz => (h hz).1
    have h₂ : ⊤ ≤ (Ξ.x v).left ⁻¹ᵁ W.P.U.LG.L.U j' := fun z hz => (h hz).2
    have t := FormalValue.tau_trans (Ξ.x_fm v) h₁ h₂ hM hM
    rw [valR_g_self W.P.D.toPre.P.isLB _ jM hM, _root_.mul_one] at t
    have e₁ := Ξ.τ_eq v j jM j₀ h₁ hj
    have e₂ := Ξ.τ_eq v j' jM j₀ h₂ hj
    refine hw.mul_left_cancel (e₁.trans ?_)
    refine (congrArg (· * _) t).trans ?_
    rw [_root_.mul_assoc, mul_left_comm]
    exact (mul_left_comm _ _ _).trans ((congrArg (_ * ·) e₂.symm).trans (mul_left_comm _ _ _))

theorem tau_zero (hx : Ξ.x 0 = 1) (j : W.P.U.LG.L.ι) (h : ⊤ ≤ (Ξ.x 0).left ⁻¹ᵁ W.P.U.LG.L.U j) :
    Ξ.τ 0 j = valR (𝟙 (Sp ℂ⟦X⟧)) ((W.P.U.LG.L.pull (eSec W.t.G)).U (fun _ => j))
      (W.P.U.LG.rig.s (fun _ => j)).val := by
  haveI := complete
  have hs : spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = 𝟙 _ := Spec.map_id _
  obtain ⟨jM, j₀, hj, h₀⟩ := exists_charts Ξ 0
  have hw := FormalValue.isUnit_valR (A := ℂ⟦X⟧) (Ξ.g 0).b.left _ hj (W.w.s (fun _ => j₀, jM))
  have hM : ⊤ ≤ FormalValue.basePt (Ξ.g 0) ⁻¹ᵁ W.P.D.toPre.P.L.U jM := fun z hz => (hj hz).2
  have hx' : (Ξ.x 0).left = spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) ≫ eSec W.t.G := by
    refine (congrArg Over.Hom.left hx).trans ?_
    exact congrArg (· ≫ eSec W.t.G) ((Category.comp_id _).symm.trans (Over.w (toUnit selfR)))
  have hu : (Λ.u.ex (0 : Λ.A.V).2).left = eSec a.D₀.P.A := by
    refine (congrArg Over.Hom.left ((Λ.u.ker 0).2 Λ.u.Λ.zero_mem)).trans ?_
    rw [Hom.one_def]; simp [eSec]
  have hb : FormalValue.basePt (Ξ.g 0) = eSec W.P.D.toPre.P.A := by
    refine W.spec.1.1.hom_ext ?_ ?_
    · exact (base_comp Ξ 0).trans ((congrArg (_ ≫ ·) hu).trans W.he.symm)
    · exact (Over.w (Ξ.g 0).b).trans (hs.trans (Over.w η[W.P.D.toPre.P.A]).symm)
  have hb' : FormalValue.basePt (Ξ.g 0) = spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) ≫ eSec W.P.D.toPre.P.A :=
    hb.trans ((Category.id_comp _).symm.trans (congrArg (· ≫ _) hs.symm))
  have hf := Ξ.x_fm 0
  have e := Ξ.τ_eq 0 j jM j₀ h hj
  rw [hx'] at hf h e
  have t := FormalValue.tau_rig hf hb' h hM
  have hj₀ : ⊤ ≤ (a.D₀.P.L.pull (eSec a.D₀.P.A)).U (fun _ => j₀) := fun z hz =>
    mem_pull.2 ((congrArg (fun q => q z ∈ a.D₀.P.L.U j₀) hu).mp (h₀ hz))
  have r := valR_rig (PowerSeries.C (R := ℂ)) W.he W.w W.P.D.toPre.rig a.D₀.rig W.spec.2.2.1 jM j₀ (hb ▸ hj) hj₀
  have f := (congrArg (PowerSeries.C (R := ℂ)) (Λ.rig (fun _ => j₀) hj₀)).trans r
  replace f := f.trans (congrArg (fun q => valR (A := ℂ⟦X⟧) q _ (W.w.s (fun _ => j₀, jM)).val * _) hb.symm)
  refine hw.mul_left_cancel (e.trans ((congrArg (_ * ·) f).trans ((mul_left_comm _ _ _).trans (congrArg (_ * ·) ?_))))
  have t' := t
  generalize FormalValue.tau W.P.U.toUnifPre ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧))
    (spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) ≫ eSec W.t.G) j jM = q at t' ⊢
  rw [hs] at t'
  exact t'


omit [Algebra (FractionRing ℂ) ℂ] in
theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) , (∀ v, IsFrm W.P.U.LG.L (Ξ.x v).left (Ξ.τ v)) ∧ ∀ j, ⊤ ≤ (Ξ.x 0).left ⁻¹ᵁ W.P.U.LG.L.U j → Ξ.τ 0 j = valR (𝟙 (Sp ℂ⟦X⟧)) ((W.P.U.LG.L.pull (eSec W.t.G)).U (fun _ => j)) (W.P.U.LG.rig.s (fun _ => j)).val := by
  intro h₁ h₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ
  refine ⟨isFrm Ξ, tau_zero Ξ ?_⟩
  have h := (GlobalTheory.ArcPts.constPts_add_smul h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ).1 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

end GlobalTheory.ConstFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantSectionMulCoordDualNumberPoint
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.ConstTanAlg

open ConstTerm

theorem core {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I} {S : Type} [CommRing S]
    {R₀ : Type} [CommRing R₀] [IsDomain R₀] {D₀ : Out.DegPre R₀} {S₀ : Type} [CommRing S₀] {σ₀ : Sp S₀ ⟶ Sp R₀}
    (κ : R →+* S) (ρ : S₀ →+* S) {φ : D.toPre.P.A.left ⟶ D₀.P.A.left}
    (w : LB.Iso D.toPre.P.L (D₀.P.L.pull φ)) (g : Out.GtPt D.toPre (Over.mk (spMap κ)))
    (g₀ : Out.GtPt D₀ (Over.mk σ₀)) {α : D.toPre.X} {α₀ : D₀.X}
    (hg : GenRelR (A := S) w (g.s α) (LB.pullGen _ _ _ (g₀.s α₀) (spMap ρ))) {j : ℕ} (s₀ : D₀.SecB j α₀)
    (f : D.toPre.SecB j α) (r : R)
    (hf : ∀ (p : Sp S ⟶ D.toPre.P.A.left) (jf : Fin 4 → D.toPre.P.L.ι) (j₀ : Fin 4 → D₀.P.L.ι),
      p ≫ D.toPre.P.A.hom = spMap κ →
      (∀ i, ⊤ ≤ (p ≫ D.toPre.famφB α i) ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => j₀ i, jf i)) →
      ∃ t : Fin 4 → Sˣ, (∀ i, (t i : S) = valR (p ≫ D.toPre.famφB α i) _ (w.s (fun _ => j₀ i, jf i)).val) ∧
        (∏ i, t i ^ Out.DegPre.famε j i : Sˣ) * valR p (LB.wchart D.toPre.P.L (D.toPre.famφB α) jf) (f.f jf) =
          κ r * valR (p ≫ φ) (LB.wchart D₀.P.L (D₀.famφB α₀) j₀) (s₀.f j₀))
    (jM : D.toPre.P.L.ι) (jf jt : Fin 4 → D.toPre.P.L.ι) (k : Fin 4 → D₀.P.L.ι)
    (hj : FormalValue.CohCharts g α jM jf jt)
    (cg : ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφT D₀ (Over.mk σ₀) g₀.b α₀) k) :
    valR (A := S) g.b.left _ (w.s (fun _ => k 2, jM)).val ^ j *
        (FormalValue.famVal g f jf * FormalValue.coordVal g α jt) =
      κ r * ρ (valR (A := S₀) g₀.b.left (LB.wchart D₀.P.L (D₀.famφB α₀) ![k 2, k 0, k 1, k 3])
        (s₀.f ![k 2, k 0, k 1, k 3]) *
        valR (A := S₀) (𝟙 _) (LB.wchart D₀.P.L (Out.DegPre.gtφT D₀ (Over.mk σ₀) g₀.b α₀) k) ((g₀.s α₀).s k).val) := by
  have hφ : ∀ i, FormalValue.coordφ g α i ≫ φ =
      spMap ρ ≫ (show Sp S₀ ⟶ _ from Out.DegPre.gtφT D₀ (Over.mk σ₀) g₀.b α₀ i) := hg.1
  have hq : ∀ i, FormalValue.basePt g ≫ D.toPre.famφB α i = FormalValue.coordφ g α (![2, 0, 1, 3] i) :=
    comp_famφB D.toPre g.b α
  have hq₀ := comp_famφB D₀ g₀.b α₀
  have ejf : ∀ i, jf i = jt (![2, 0, 1, 3] i) := fun i => hj.2.2 (.inr (.inl i)) (.inr (.inr _)) (hq i)
  have ejM : jM = jt 2 := hj.2.2 (.inl PUnit.unit) (.inr (.inr 2)) rfl
  have hk : ∀ i, ⊤ ≤ (show Sp S₀ ⟶ _ from Out.DegPre.gtφT D₀ (Over.mk σ₀) g₀.b α₀ i) ⁻¹ᵁ D₀.P.L.U (k i) :=
    fun i => cg.trans (LB.wchart_le _ _ _ i)
  have ek : ![k 2, k 0, k 1, k 3] = fun i => k (![2, 0, 1, 3] i) := by
    funext i; fin_cases i <;> rfl
  rw [ek]
  subst ejM
  obtain rfl : jf = fun i => jt (![2, 0, 1, 3] i) := funext ejf
  have hd : ∀ i, ⊤ ≤ FormalValue.coordφ g α i ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => k i, jt i) :=
    fun i => le_div _ (hφ i ▸ FormalValue.top_le_comp (hk i) _) (hj.2.1.trans (LB.wchart_le _ _ _ i))
  obtain ⟨t, ht, e₁⟩ := hf (FormalValue.basePt g) (fun i => jt (![2, 0, 1, 3] i)) (fun i => k (![2, 0, 1, 3] i))
    (Over.w g.b) (fun i => by rw [hq i]; exact hd _)
  simp only [hq] at ht
  have cf : ⊤ ≤ (show Sp S₀ ⟶ _ from g₀.b.left) ⁻¹ᵁ D₀.P.L.wchart (D₀.famφB α₀) (fun i => k (![2, 0, 1, 3] i)) :=
    fun z hz => Set.mem_iInter.2 fun i =>
      (congrArg (fun q => q z ∈ D₀.P.L.U (k (![2, 0, 1, 3] i))) (hq₀ i)).mpr (hk _ hz)
  have e₂ : valR (FormalValue.basePt g ≫ φ) _ (s₀.f fun i => k (![2, 0, 1, 3] i)) = _ :=
    (congrArg (fun q => valR q _ (s₀.f fun i => k (![2, 0, 1, 3] i))) (hφ 2)).trans
      (FormalValue.valR_spMap ρ (show Sp S₀ ⟶ _ from g₀.b.left) _ cf _)
  have e₃ : FormalValue.coordVal g α jt = _ := (hg.2 jt k hd).trans (congrArg₂ (· * ·)
    (Finset.prod_congr rfl fun i _ => valR_zpow _ _ (hd i) _ (![t 1, t 2, t 0, t 3] i)
      (by fin_cases i; exacts [ht 1, ht 2, ht 0, ht 3]) _)
    (valR_pullGen ρ (g₀.s α₀) k cg))
  have e₅ : (t 0 : S) ^ j * ∏ i, ((![t 1, t 2, t 0, t 3] i ^ (-Out.DegPre.gtε i) : Sˣ) : S) =
      ((∏ i, t i ^ Out.DegPre.famε j i : Sˣ) : S) := by
    rw [← Units.coe_prod, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← prod_factors t j]
    simp only [zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel_right]
  replace e₁ := e₁.trans (congrArg (κ r * ·) e₂)
  refine (congrArg₂ (fun a b => a ^ j * (_ * b)) (ht 0).symm e₃).trans ?_
  rw [← e₅] at e₁
  rw [map_mul, ← _root_.mul_assoc (κ r)]
  refine Eq.trans ?_ (congrArg (· * _) e₁)
  exact (congrArg (_ * ·) (_root_.mul_left_comm _ _ _)).trans
    ((_root_.mul_assoc _ _ _).symm.trans (_root_.mul_assoc _ _ _).symm)

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)) (j : ℕ) (x : a.D₀.X) (s₀ : a.D₀.SecB j x) (f : W.P.D.toPre.SecB j (W.e x)) (r : ℂ⟦X⟧) (jM : W.P.D.toPre.P.L.ι) (jf jt : Fin 4 → W.P.D.toPre.P.L.ι) (jt₀ : Fin 4 → a.D₀.P.L.ι), TanRel W ν g₁ → IsConstMul W j x s₀ f r → FormalValue.CohCharts g₁ (W.e x) jM jf jt → ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) jt₀ → valR (A := DualNumber ℂ⟦X⟧) g₁.b.left _ (W.w.s (fun _ => jt₀ 2, jM)).val ^ j * (FormalValue.famVal g₁ f jf * FormalValue.coordVal g₁ (W.e x) jt) = TrivSqZeroExt.inl r * constEps (valR (A := DualNumber ℂ) ν.b.left (LB.wchart a.D₀.P.L (a.D₀.famφB x) ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) (s₀.f ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) * valR (A := DualNumber ℂ) (𝟙 _) (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) jt₀) ((ν.s x).s jt₀).val) := by
  intro E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W ν g₁ j x s₀ f r jM jf jt jt₀ hg hf hj hc
  have := isLocalRing_dual ℂ⟦X⟧
  exact core (algebraMap ℂ⟦X⟧ (DualNumber ℂ⟦X⟧)) constEps W.w g₁ ν (hg x) s₀ f r (fun p => hf _ p _) jM jf jt jt₀
    hj hc

end GlobalTheory.ConstTanAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTangentEqFormalPointTransported
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

namespace GlobalTheory.ConstTanFormal

theorem corr_of_genRelR {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A']
    {B B₀ Y₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} (hw : w.IsGen)
    (hM : M.IsLB) (hM₀ : M₀.IsLB) {K : Type} [Fintype K] {ε : K → ℤ} {pt : K → (Sp A ⟶ B)} {pt' : K → (Sp A' ⟶ B)}
    {pt₀ : K → (Y₀ ⟶ B₀)} {g : LB.Gen (LB.LinComb M pt ε)} {t : LB.Gen (LB.LinComb M pt' ε)}
    {ν : LB.Gen (LB.LinComb M₀ pt₀ ε)} (hg : g.IsGen) (ht : t.IsGen) (hν : ν.IsGen) {r : Sp A' ⟶ Sp A}
    {κ : Sp A ⟶ Y₀} {κ' : Sp A' ⟶ Y₀} (hκ : r ≫ κ = κ') (hp : ∀ k, pt' k = r ≫ pt k)
    (h : GenRelR w g (LB.pullGen _ _ _ ν κ)) (h' : GenRelR w t (LB.pullGen _ _ _ ν κ')) :
    LB.Gen.Corr M _ _ _ _ t (LB.pullGen M _ _ g r) := by
  have hw' := (isGen_iff w).1 hw
  have H := ConstGrp.pmaps_of_genRelR hw' hM hM₀ hg (DVR.pullGen_isGen _ _ _ _ hν κ) h
  have H' := ConstGrp.pmaps_of_genRelR hw' hM hM₀ ht (DVR.pullGen_isGen _ _ _ _ hν κ') h'
  refine corr_of_val hM fun y J' hJ' => ?_
  choose J hJ using fun ψ : Sp A' ⟶ B₀ => exists_chart hM₀ (ψ y)
  have v := CubTransport.val_pmaps (fun k => (h.1 k).trans (Category.id_comp _).symm) H r hJ hJ'
  have v' := CubTransport.val_pmaps (fun k => (h'.1 k).trans (Category.id_comp _).symm) H' (𝟙 _) hJ hJ'
  rw [val_pull hJ, Category.comp_id, hκ] at v
  rw [val_pull hJ, Category.comp_id, Category.id_comp] at v'
  rw [val_pull hJ', Category.id_comp]
  simp only [Category.id_comp, hp] at v'
  exact mul_left_cancel (v'.symm.trans v)

theorem dualMapR_surjective {R R' : Type} [CommRing R] [CommRing R'] {φ : R →+* R'} (h : Function.Surjective φ) :
    Function.Surjective (dualMapR φ) := fun a => by
  obtain ⟨x, hx⟩ := h a.fst
  obtain ⟨y, hy⟩ := h a.snd
  exact ⟨TrivSqZeroExt.inl x + TrivSqZeroExt.inr y, by ext <;> simp [hx, hy]⟩

theorem ker_dualMapR_mk {R : Type} [CommRing R] (I : Ideal R) :
    RingHom.ker (dualMapR (Ideal.Quotient.mk I)) ≤ I.map (algebraMap R (DualNumber R)) := fun a ha => by
  have h₁ : a.fst ∈ I := Ideal.Quotient.eq_zero_iff_mem.1 (by
    simpa using congrArg TrivSqZeroExt.fst (RingHom.mem_ker.1 ha))
  have h₂ : a.snd ∈ I := Ideal.Quotient.eq_zero_iff_mem.1 (by
    simpa using congrArg TrivSqZeroExt.snd (RingHom.mem_ker.1 ha))
  have e : a = algebraMap R (DualNumber R) a.fst + algebraMap R (DualNumber R) a.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [e]
  exact Ideal.add_mem _ (Ideal.mem_map_of_mem _ h₁) (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h₂))

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (g : ℕ) (ex₀ : (Fin g → ℂ) → Out.GtPtF a.D₀ ℂ) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (v : epsR ℂ⟦X⟧ ⟶ W.t.G) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)), DiffHyp W ex₀ z₀ ν v → TanRel W ν g₁ → FormalValue.IsFormalPt W.P.U.toUnifPre idealEps g₁ v.left := by
  intro E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W g ex₀ z₀ ν v g₁ hD hT
  refine FormalValue.isFormalPt_of_surjective _ fun e => ?_
  let I : Ideal ℂ⟦X⟧ := Ideal.span {PowerSeries.X}
  have hI : I ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact PowerSeries.X_prime.not_isUnit
  have : IsLocalRing (ℂ⟦X⟧ ⧸ I ^ (e + 1)) := isLocalRing_quotient_pow hI e
  have := isLocalRing_dual (ℂ⟦X⟧ ⧸ I ^ (e + 1))
  have := isLocalRing_dual ℂ⟦X⟧
  let ρ : DualNumber ℂ⟦X⟧ →+* DualNumber (ℂ⟦X⟧ ⧸ I ^ (e + 1)) := dualMapR (Ideal.Quotient.mk _)
  let s : Sp (DualNumber (ℂ⟦X⟧ ⧸ I ^ (e + 1))) ⟶ Sp (ℂ⟦X⟧ ⧸ I ^ (e + 1)) := spMap (algebraMap _ _)
  have hs : s ≫ Out.thick ℂ⟦X⟧ I e = spMap ρ ≫ (epsR ℂ⟦X⟧).hom := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext fun r => (dualMapR_inl (Ideal.Quotient.mk (I ^ (e + 1))) r).symm)
  let xe : Sp (DualNumber (ℂ⟦X⟧ ⧸ I ^ (e + 1))) ⟶ (Out.thickObj ℂ⟦X⟧ I e W.t.G).left :=
    pullback.lift (spMap ρ ≫ v.left) s (by rw [Category.assoc, Over.w v, hs])
  have hx : xe ≫ (Out.fstG I e W.t.G).left = spMap ρ ≫ v.left := pullback.lift_fst _ _ _
  have hx' : xe ≫ ((Over.map (Out.thick ℂ⟦X⟧ I e)).obj (Out.thickObj ℂ⟦X⟧ I e W.t.G)).hom =
      spMap ρ ≫ (epsR ℂ⟦X⟧).hom :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (pullback.lift_snd _ _ _)).trans hs)
  have hκ : spMap ρ ≫ spMap constEps = spMap (ρ.comp constEps) := (Spec.map_comp _ _).symm
  have h' := hD.2.2 e ρ (ρ.comp constEps) xe (dualMapR_inl _) (dualMapR_eps _)
    (fun r => (congrArg ρ (dualMapR_inl _ r)).trans (dualMapR_inl _ _))
    ((congrArg ρ (dualMapR_eps _)).trans (dualMapR_eps _)) hx
  have hp : ∀ x k, xe ≫ W.P.D.toPre.Oφ (W.P.U.gt e).pG (W.e x) k =
      spMap ρ ≫ Out.DegPre.gtφT W.P.D.toPre (epsR ℂ⟦X⟧) g₁.b (W.e x) k := fun x k => by
    refine W.spec.1.1.hom_ext ?_ ?_
    · refine ((h' x).1 k).trans ?_
      exact (congrArg (· ≫ _) hκ.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (spMap ρ ≫ ·) ((hT x).1 k).symm).trans (Category.assoc _ _ _).symm))
    · rw [Category.assoc, Category.assoc]
      refine Eq.trans ?_ (hx'.trans ?_)
      · refine congrArg (xe ≫ ·) ?_
        fin_cases k <;> exact Over.w _
      · refine congrArg (spMap ρ ≫ ·) ?_
        fin_cases k <;> exact (Over.w _).symm
  refine ⟨_, inferInstance, ρ, xe, dualMapR_surjective Ideal.Quotient.mk_surjective, ?_, hx, hp 0 2, fun y => ?_⟩
  · rw [idealEps, ← Ideal.map_pow]
    exact ker_dualMapR_mk _
  · obtain ⟨x, rfl⟩ := W.e.surjective y
    exact corr_of_genRelR W.spec.2.1 W.P.D.toPre.P.isLB a.D₀.P.isLB (g₁.isGen _)
      (DVR.pullGen_isGen _ _ _ _ ((W.P.U.gt e).t_gen _) xe) (ν.isGen x) hκ (hp x) (hT x) (h' x)

end GlobalTheory.ConstTanFormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantTorusExtensionTangentRel
section
namespace GlobalTheory.ConstTan

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem exists_tanRel : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (ν : Out.GtPt a.D₀ (epsR ℂ)), ∃ g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧), TanRel W ν g₁ := by
  intro _ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W ν
  haveI := isLocalRing_dual ℂ⟦X⟧
  obtain ⟨gp, hw, -, -, hc, -⟩ := W.spec
  obtain ⟨g, hg⟩ := ConstPoint.exists_gtPt_genRelR (A := DualNumber ℂ⟦X⟧) globalFns_holds gp hw
    W.e.symm.toAddEquiv.toAddMonoidHom
    (fun y => by have := hc (W.e.symm y); rwa [LinearEquiv.apply_symm_apply] at this)
    (T := epsR ℂ) (spMap (algebraMap ℂ⟦X⟧ (DualNumber ℂ⟦X⟧))) (spMap constEps)
    ((spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun r => dualMapR_inl _ r)).trans (spMap_comp _ _))) ν
  refine ⟨g, fun x => ?_⟩
  have := hg (W.e x)
  rw [show W.e.symm.toAddEquiv.toAddMonoidHom (W.e x) = x from W.e.symm_apply_apply x] at this
  exact this

end GlobalTheory.ConstTan
end

