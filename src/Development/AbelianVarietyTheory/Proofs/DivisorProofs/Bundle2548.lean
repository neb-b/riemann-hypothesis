module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0017
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0016
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogResolutionMultLtOfConnectedness
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.LogResConn

theorem mult_le_ord_of_regularAt {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {F : CartierDiv Y} {v : Y} {f : Y.functionField} (h : (-F).RegularAt v f) (hf : f ≠ 0)
    (hv : Order.coheight v = 1) : F.mult v ≤ Scheme.ord f v := by
  obtain ⟨g, hg⟩ := F.exists_isEqn v
  obtain ⟨a, ha⟩ := hg.neg.regularAt_iff.1 h
  have hg0 : ((g⁻¹ : Y.functionFieldˣ) : Y.functionField) ≠ 0 := Units.ne_zero _
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact mul_ne_zero hf hg0 ha.symm
  have h2 := ord_algebraMap hv ha0
  rw [ha, Scheme.ord_mul hf hg0] at h2
  have h3 := Scheme.ord_mul (x := v) (Units.ne_zero g) hg0
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, (unitAt_one v).ord_eq_zero] at h3
  rw [hg.mult_eq]
  have : (0 : ℤ) ≤ ((Module.length (Y.presheaf.stalk v) (Y.presheaf.stalk v ⧸ Ideal.span {a})).toNat : ℤ) :=
    Int.natCast_nonneg _
  omega

theorem mem_ring_of_regularAt {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} {E : DivOver q} {F : CartierDiv Y} {w : Y}
    {f : Y.functionField} (hE : E.IsAt w) (h : (-F).RegularAt w f) (hF : 0 ≤ F.mult w) :
    f ∈ E.ring := by
  by_cases hf : f = 0
  · rw [hf]; exact zero_mem _
  have h1 := mult_le_ord_of_regularAt h hf hE.coheight_eq_one
  have h2 := hE.ord_eq (Units.mk0 f hf)
  have h3 := (E.ord_nonneg_iff (Units.mk0 f hf)).1 (by rw [h2]; simpa using hF.trans h1)
  simpa using h3

variable {k : Type} [Field k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  [IsLocallyNoetherian Y] [GlobalTheory.IsNormalScheme Y]

theorem regAt_pull {p : X ⟶ Sp k} (s : Y ⟶ X) [IsDominant s] [LocallyOfFiniteType (s ≫ p)]
    (hbir : Function.Bijective (functionFieldMap s)) {v : Y} {y : X} (hv : Order.coheight v = 1)
    (hsv : s v ⤳ y) {f : X.functionField} (hf : RegAt y f) : RegAt v (functionFieldMap s f) := by
  obtain ⟨E', hE'⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := s ≫ p) hv
  obtain ⟨E, hE⟩ := _root_.GlobalTheory.Discrepancy.DivOver.exists_over_of_bijective k X Y p s hbir E'
  have ht := _root_.GlobalTheory.Discrepancy.DivOver.Over.through_image k X Y p s E' E hE v (hE'.through specializes_rfl)
  exact (hE' _).1 ((hE f).1 ((ht.of_specializes hsv) f hf))

theorem unitAt_pull {p : X ⟶ Sp k} (s : Y ⟶ X) [IsDominant s] [LocallyOfFiniteType (s ≫ p)]
    (hbir : Function.Bijective (functionFieldMap s)) {v : Y} {y : X} (hv : Order.coheight v = 1)
    (hsv : s v ⤳ y) {f : X.functionField} (hf : UnitAt y f) : UnitAt v (functionFieldMap s f) := by
  have hf0 := hf.ne_zero
  obtain ⟨h1, h2⟩ := (unitAt_iff hf0).1 hf
  refine (unitAt_iff ((map_ne_zero _).2 hf0)).2 ⟨regAt_pull (p := p) s hbir hv hsv h1, ?_⟩
  rw [← map_inv₀]
  exact regAt_pull (p := p) s hbir hv hsv h2

end GlobalTheory.LogResConn

namespace GlobalTheory.LogResConn

theorem mult_lt_of_connected : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G N : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) → ∀ (y : X) (σ : Y), IsIntegrallyClosed (X.presheaf.stalk y) → (∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z → ∀ g, G.IsEqn z g → discrep E η m g ≤ 0) → (pullCart s G - m • K).mult σ = m → s σ ⤳ y → (∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → (pullCart s G - m • K).mult v < m) → ∀ v : Y, v ≠ σ → s v ⤳ y → (pullCart s G - m • K).mult v < m := by
  intro X _ _ p n hp hn η m G N Y _ _ s _ K B F hη hm hres hF hcoh y σ hyint hdisc hσ hsσ hnear
    v hvσ hsv
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hFσ : F.mult σ = 1 := by rw [hF, hσ]; exact Int.ediv_self hm'.ne'
  have hFle : ∀ z, F.mult z ≤ 0 ↔ (pullCart s G - m • K).mult z < m := fun z => by
    rw [hF, ← Int.lt_add_one_iff, zero_add, Int.ediv_lt_iff_lt_mul hm', one_mul]
  have hFnn : ∀ z, 0 ≤ (pullCart s G - m • K).mult z → 0 ≤ F.mult z := fun z hz => by
    rw [hF]; exact Int.ediv_nonneg hz hm'.le
  by_cases hvc : Order.coheight v ≠ 1
  · have : (pullCart s G - m • K).mult v = 0 := by
      by_contra h0
      exact hvc (CartierDiv.coheight_eq_one_of_mult_ne_zero h0)
    rw [this]; exact hm'
  push_neg at hvc
  haveI := hres.smooth
  haveI : Smooth (s ≫ p) := SmoothOfRelativeDimension.smooth n _
  haveI : GlobalTheory.IsNormalScheme Y := GlobalTheory.ModifSections.isNormalScheme_of_smooth (s ≫ p)
  haveI : IsProper (s ≫ p) := ((isProjOver_iff_isProper_and_exists_isAmpleLB (s ≫ p)).1 hres.proj).1
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  haveI : IsProper s := IsProper.of_comp s p
  have hbir := hres.bir
  have hσc : Order.coheight σ = 1 :=
    CartierDiv.coheight_eq_one_of_mult_ne_zero (by rw [hσ]; exact_mod_cast hm.ne')
  obtain ⟨h, hσreg, hreg⟩ := _root_.GlobalTheory.PairStep.exists_lifted_fn X p n hp hn η m G N Y s K B F hres hcoh y σ
    (fun v w h1 h2 h3 h4 => (hFle v).2 (hnear v w h1 h2 h3 h4)) hsσ hσc
  obtain ⟨h₀, rfl⟩ := hbir.2 h

  have hη' : EtaleKlt.ratPull p s n η ≠ 0 := fun h0 =>
    hη ((EtaleKlt.ratPull_bijective_of_birational ℂ X Y p s hbir n).1 (h0.trans (map_zero _).symm))

  have hDnn : ∀ (z : X), z ⤳ y → ∀ (E : DivOver p) (E' : DivOver (s ≫ p)), E.IsAt z →
      DivOver.Over s E' E → ∀ w, s w = z → E'.IsAt w → 0 ≤ F.mult w := by
    intro z hz E E' hE hE'E w hwz hw
    subst hwz
    obtain ⟨g, hg⟩ := G.exists_isEqn (s w)
    have hd := hdisc (s w) hz E hE g hg
    have h1 := GlobalTheory.T.discrepancy_formula_divisor ℂ Y (s ≫ p) n (EtaleKlt.ratPull p s n η) hη' K (pullCart s G) m hm
      hres.div E' w (fnPull s g) hw (isEqn_pullCart s hg)
    have h2 : discrep E' (EtaleKlt.ratPull p s n η) m (fnPull s g) = discrep E η m g := by
      have hform : E'.formOrd (EtaleKlt.ratPull p s n η) = E.formOrd η := by
        simpa only [DivOver.formOrd] using
          (GlobalTheory.T.form_order_birational_pullback ℂ X Y p s hbir E' E hE'E n η hη)
      unfold discrep
      rw [hform, _root_.GlobalTheory.Discrepancy.DivOver.Over.ord_fnPull_of_bijective ℂ X Y p s hbir E' E hE'E g]
    rw [h2] at h1
    rw [h1] at hd
    have hmq : (0 : ℚ) < m := by exact_mod_cast hm
    have : (0 : ℚ) ≤ ((pullCart s G - m • K).mult w : ℚ) := by
      rw [neg_div, neg_nonpos] at hd
      exact (div_nonneg_iff.1 hd).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hmq))
    exact hFnn w (by exact_mod_cast this)

  have hreg0 : RegAt y h₀ := by
    refine _root_.GlobalTheory.Discrepancy.regAt_of_isIntegrallyClosed_stalk X p hp y hyint h₀ fun z hz E hE => ?_
    obtain ⟨E', hE'E⟩ := _root_.GlobalTheory.Discrepancy.DivOver.exists_over ℂ X Y p s hbir E
    obtain ⟨w, hwz, hw⟩ := GlobalTheory.T.divisor_point_proper_lift ℂ X Y p s hbir inferInstance E' E hE'E z hE
    have hFw := hDnn z hz E E' hE hE'E w hwz hw
    have hsw : s w ⤳ y := hwz ▸ hz
    rw [hE'E h₀]
    by_cases hwσ : w = σ
    · subst hwσ
      have := mem_ring_of_regularAt hw hσreg hFw
      simpa using add_mem this (one_mem E'.ring)
    · exact mem_ring_of_regularAt hw (hreg w hwσ hw.coheight_eq_one hsw) hFw

  have hunit0 : UnitAt y h₀ := by
    by_cases hh1 : functionFieldMap s h₀ - 1 = 0
    · have : h₀ = 1 := hbir.1 (by rw [map_one]; exact sub_eq_zero.1 hh1)
      rw [this]; exact unitAt_one y
    have hnu : ¬ UnitAt y (h₀ - 1) := fun hu => by
      have hu' := unitAt_pull (p := p) s hbir hσc hsσ hu
      rw [map_sub, map_one] at hu'
      have := mult_le_ord_of_regularAt hσreg hh1 hσc
      rw [hu'.ord_eq_zero, hFσ] at this
      omega
    obtain ⟨a, ha, e⟩ := zeroAt_iff.2 ⟨hreg0.add ⟨-1, by rw [map_neg, map_one]⟩, by
      rwa [sub_eq_add_neg] at hnu⟩
    have h1a : (1 + a) ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := fun h' => by
      have h1 : (1 : X.presheaf.stalk y) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
        simpa using sub_mem h' ha
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
        (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
    exact ⟨1 + a, IsLocalRing.notMem_maximalIdeal.1 h1a, by rw [map_add (f := _), map_one, e]; ring⟩
  have hu := unitAt_pull (p := p) s hbir hvc hsv hunit0
  have := mult_le_ord_of_regularAt (hreg v hvσ hvc hsv) hu.ne_zero hvc
  rw [hu.ord_eq_zero] at this
  exact (hFle v).1 this

end GlobalTheory.LogResConn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpOfVal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Point

section Reg

variable {X X' Y W : Scheme.{0}} (L : LB X) (L' : LB X')

def tr {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (I : (Y ⟶ X) → L.ι) (ψ : Y ⟶ X) :
    (Z.presheaf.stalk z)ˣ :=
  gm (r ≫ ψ) z (L.U (J (r ≫ ψ)) ⊓ L.U (I ψ)) (L.g (J (r ≫ ψ)) (I ψ))

def Reg (F : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z), ((Z ⟶ X) → L.ι) → ((Z ⟶ X') → L'.ι) → (Z.presheaf.stalk z)ˣ)
    (c : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → ((Y ⟶ X') → U) → U) : Prop :=
  ∀ (y : Y) I I', Good L y I → Good L' y I' → ∃ V : Y.Opens, y ∈ V ∧ ∃ u : Γ(Y, V)ˣ,
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', r z ∈ V → Good L z J → Good L' z J' →
      F Z r z J J' = c _ (tr L r z J I) (tr L' r z J' I') * gm r z V u

variable {L L'}
variable {F G : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z), ((Z ⟶ X) → L.ι) → ((Z ⟶ X') → L'.ι) → (Z.presheaf.stalk z)ˣ}
  {c d : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → ((Y ⟶ X') → U) → U}

theorem Reg.mul (hF : Reg L L' F c) (hG : Reg L L' G d) :
    Reg L L' (fun Z r z J J' => F Z r z J J' * G Z r z J J') (fun U _ h h' => c U h h' * d U h h') := by
  intro y I I' hI hI'
  obtain ⟨V, hV, u, hu⟩ := hF y I I' hI hI'
  obtain ⟨V', hV', u', hu'⟩ := hG y I I' hI hI'
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, res inf_le_left u * res inf_le_right u', fun Z r z J J' hz hJ hJ' => ?_⟩
  rw [map_mul, gm_res r z _ hz, gm_res r z _ hz]
  show F Z r z J J' * G Z r z J J' = _
  rw [hu Z r z J J' hz.1 hJ hJ', hu' Z r z J J' hz.2 hJ hJ', _root_.mul_mul_mul_comm]

theorem Reg.inv (hF : Reg L L' F c) :
    Reg L L' (fun Z r z J J' => (F Z r z J J')⁻¹) (fun U _ h h' => (c U h h')⁻¹) := by
  intro y I I' hI hI'
  obtain ⟨V, hV, u, hu⟩ := hF y I I' hI hI'
  refine ⟨V, hV, u⁻¹, fun Z r z J J' hz hJ hJ' => ?_⟩
  show (F Z r z J J')⁻¹ = _
  rw [map_inv, hu Z r z J J' hz hJ hJ', mul_inv]

theorem good_exists {M : LB X} (hM : M.IsLB) {Z : Scheme.{0}} (z : Z) : ∃ J, Good M z J := by
  choose I hI using fun χ : Z ⟶ X => exists_chart hM (χ z)
  exact ⟨I, hI⟩

theorem Reg.glue (hL : L.IsLB) (hL' : L'.IsLB) (hF : Reg L L' F c)
    (hc : ∀ (U : Type) [CommGroup U] h h', c U h h' = 1) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', Good L z J → Good L' z J' →
      F Z r z J J' = gm r z ⊤ a := by
  have H : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ u : Γ(Y, V)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', r z ∈ V → Good L z J → Good L' z J' → F Z r z J J' = gm r z V u := by
    intro y
    obtain ⟨I, hI⟩ := good_exists hL y
    obtain ⟨I', hI'⟩ := good_exists hL' y
    obtain ⟨V, hV, u, hu⟩ := hF y I I' hI hI'
    exact ⟨V, hV, u, fun Z r z J J' hz hJ hJ' => by rw [hu Z r z J J' hz hJ hJ', hc, _root_.one_mul]⟩
  choose V hV u hu using H
  obtain ⟨a, ha⟩ := glue_unit ⊤ V (fun _ => le_top) (fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hV y⟩) u
    (fun i j x hx => by
      obtain ⟨I, hI⟩ := good_exists hL x
      obtain ⟨I', hI'⟩ := good_exists hL' x
      exact (hu i _ (𝟙 Y) x I I' hx.1 hI hI').symm.trans (hu j _ (𝟙 Y) x I I' hx.2 hI hI'))
  refine ⟨a, fun Z r z J J' hJ hJ' => ?_⟩
  rw [hu (r z) Z r z J J' (hV _) hJ hJ', ← ha, gm_res r z _ (hV _)]

theorem Reg.rigid (hL : L.IsLB) (hL' : L'.IsLB) (hF : Reg L L' F c)
    (hc : ∀ (U : Type) [CommGroup U] h h', c U h h' = 1) {S : Scheme.{0}} (p : Y ⟶ S)
    (hp : Function.Surjective p.appTop.hom) {Z : Scheme.{0}} (r r' : Z ⟶ Y) (hr : r ≫ p = r' ≫ p) (z : Z) {J J'}
    (hJ : Good L z J) (hJ' : Good L' z J') : F Z r z J J' = F Z r' z J J' := by
  obtain ⟨a, ha⟩ := hF.glue hL hL' hc
  obtain ⟨a₀, e⟩ := hp a.val
  rw [ha Z r z J J' hJ hJ', ha Z r' z J J' hJ hJ']
  apply Units.ext
  have k : ∀ q : Z ⟶ Y, (gm q z ⊤ a).val = gs (q ≫ p) z ⊤ a₀ := fun q => by
    rw [← gs_unit q z ⊤ trivial, ← e]
    exact gs_pull q p z ⊤ trivial a₀
  rw [k, k, hr]

variable {K : Type} [Fintype K]

theorem reg_val {φ : K → (W ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (p : Y ⟶ W) :
    Reg L L' (fun _ r z J _ => val t (r ≫ p) z J) (fun _ _ h _ => ∏ k, h (p ≫ φ k) ^ ε k) := by
  intro y I I' hI _
  refine ⟨p ⁻¹ᵁ LB.wchart L φ (fun k => I (p ≫ φ k)), hI.mem φ p, pullU p _ (t.s _), fun Z r z J J' hz hJ _ => ?_⟩
  refine Eq.trans ?_ (congrArg (_ * ·) (gm_pull r p z _ hz _).symm)
  refine (gen_trans ht (r ≫ p) z (hJ.mem φ (r ≫ p)) hz).trans (congrArg (· * _) ?_)
  rfl

theorem reg_val' {φ : K → (W ⟶ X')} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L' φ ε)} (ht : t.IsGen) (p : Y ⟶ W) :
    Reg L L' (fun _ r z _ J' => val t (r ≫ p) z J') (fun _ _ _ h' => ∏ k, h' (p ≫ φ k) ^ ε k) := by
  intro y I I' _ hI
  refine ⟨p ⁻¹ᵁ LB.wchart L' φ (fun k => I' (p ≫ φ k)), hI.mem φ p, pullU p _ (t.s _), fun Z r z J J' hz _ hJ => ?_⟩
  refine Eq.trans ?_ (congrArg (_ * ·) (gm_pull r p z _ hz _).symm)
  refine (gen_trans ht (r ≫ p) z (hJ.mem φ (r ≫ p)) hz).trans (congrArg (· * _) ?_)
  rfl

def wv {pr : K → (X' ⟶ X)} {ε : K → ℤ} (w : LB.Iso L' (LB.LinComb L pr ε)) {Z : Scheme.{0}} (q : Z ⟶ X') (z : Z)
    (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) : (Z.presheaf.stalk z)ˣ :=
  gv w q z (fun k => J (q ≫ pr k)) (J' q)

theorem reg_wv {pr : K → (X' ⟶ X)} {ε : K → ℤ} {w : LB.Iso L' (LB.LinComb L pr ε)} (hw : w.IsGen) (p : Y ⟶ X') :
    Reg L L' (fun _ r z J J' => wv w (r ≫ p) z J J') (fun _ _ h h' => (∏ k, h (p ≫ pr k) ^ ε k) * (h' p)⁻¹) := by
  intro y I I' hI hI'
  refine ⟨p ⁻¹ᵁ (LB.wchart L pr (fun k => I (p ≫ pr k)) ⊓ L'.U (I' p)), ⟨hI.mem pr p, hI' p⟩,
    pullU p _ (w.s (fun k => I (p ≫ pr k), I' p)), fun Z r z J J' hz hJ hJ' => ?_⟩
  refine Eq.trans ?_ (congrArg (_ * ·) (gm_pull r p z _ hz _).symm)
  refine (gm_isGen hw (r ≫ p) z _ (fun k => I (p ≫ pr k)) _ (I' p) (hJ.mem pr (r ≫ p)) hz.1 (hJ' _) hz.2).trans
    (congrArg (· * _) (congrArg₂ (· * ·) ?_ rfl))
  refine (gm_linComb L pr ε (r ≫ p) z _ _ (hJ.mem pr (r ≫ p)) hz.1).trans ?_
  rfl

end Reg

open GlobalTheory.LamBiext GlobalTheory.LamRigid GlobalTheory.PolDeg in
theorem reg_lam {S S' Y : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B']
    [IsCommMonObj B'] {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    {w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)} (hw : w.IsGen) (p : Y ⟶ (G2 B').left) :
    Reg M M' (fun _ r z J J' => lamVal w (r ≫ p) z J J')
      (fun _ _ h h' => (∏ k, h ((p ≫ β₂) ≫ lamφ B k) ^ lamε k) * (∏ k, h' (p ≫ lamφ B' k) ^ lamε k)⁻¹) := by
  intro y I I' hI hI'
  refine ⟨p ⁻¹ᵁ (((abelian₂ B M).pull β₂).U (fun _ => ind B I (p ≫ β₂)) ⊓ (abelian₂ B' M').U (ind B' I' p)),
    ⟨mem_pull.2 (good_ind hI (p ≫ β₂)), good_ind hI' p⟩,
    pullU p _ (w.s (fun _ => ind B I (p ≫ β₂), ind B' I' p)), fun Z r z J J' hz hJ hJ' => ?_⟩
  refine Eq.trans ?_ (congrArg (_ * ·) (gm_pull r p z _ hz _).symm)
  refine (lamVal_eq w (r ≫ p) z J J').trans ?_
  refine ((isGen_iff w).1 hw Z (r ≫ p) z _ (ind B I (p ≫ β₂)) _ (ind B' I' p) (good_ind hJ ((r ≫ p) ≫ β₂))
    (mem_pull.1 hz.1) (good_ind hJ' _) hz.2).trans (congrArg (· * _) (congrArg₂ (· * ·) ?_ (congrArg (·⁻¹) ?_)))
  · refine (gm_linComb M (lamφ B) lamε ((r ≫ p) ≫ β₂) z _ _ (good_ind hJ ((r ≫ p) ≫ β₂)) (mem_pull.1 hz.1)).trans ?_
    rfl
  · refine (gm_linComb M' (lamφ B') lamε (r ≫ p) z _ _ (good_ind hJ' _) hz.2).trans ?_
    rfl

section Scale

variable {Y : Scheme.{0}} {M : LB Y}

def scale (a : Γ(Y, ⊤)ˣ) (t : LB.Gen M) : LB.Gen M := ⟨fun i => res le_top a * t.s i⟩

theorem gm_scale (a : Γ(Y, ⊤)ˣ) (t : LB.Gen M) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (i : M.ι) (h : r z ∈ M.U i) :
    gm r z (M.U i) ((scale a t).s i) = gm r z ⊤ a * gm r z (M.U i) (t.s i) :=
  (map_mul _ _ _).trans (congrArg (· * _) (gm_res r z _ h a))

theorem scale_isGen (a : Γ(Y, ⊤)ˣ) {t : LB.Gen M} (ht : t.IsGen) : (scale a t).IsGen := fun i j =>
  unit_ext fun y hy => by
    have e := congrArg (gm (𝟙 Y) y _) (ht i j)
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy] at e
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_scale a t _ y i hy.1, gm_scale a t _ y j hy.2, e, mul_left_comm]

end Scale

theorem mapsAtExp_of_val {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB) {K : Type}
    [Fintype K] {pr : K → (X' ⟶ X)} {ε : K → ℤ} {w : LB.Iso L' (LB.LinComb L pr ε)} (hw : w.IsGen) {p : Y ⟶ X'} {n : ℤ}
    {a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p) (fun _ => n))} (ha : a.IsGen)
    {b : LB.Gen (LB.LinComb L (K := K) (fun i => p ≫ pr i) (fun i => n * ε i))} (hb : b.IsGen)
    (H : ∀ (y : Y) J J', Good L y J → Good L' y J' → val b (𝟙 Y) y J = wv w p y J J' ^ n * val a (𝟙 Y) y J') :
    MapsAtExp L L' pr ε w p n a b := by
  intro jN jL
  refine unit_ext fun y hy => ?_
  obtain ⟨J, hJ⟩ := good_exists hL y
  obtain ⟨J', hJ'⟩ := good_exists hL' y
  have e := H y J J' hJ hJ'
  rw [val_of b _ y J (fun i => J (p ≫ pr i)) (fun i => by rw [Category.id_comp]),
    val_of a _ y J' (fun _ => J' p) (fun i => by rw [Category.id_comp])] at e
  have m₁ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun i => p ≫ pr i) (fun i => J (p ≫ pr i)) := Set.mem_iInter.2 fun i => hJ _
  have m₂ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L' (fun _ : PUnit => p) (fun _ => J' p) := Set.mem_iInter.2 fun i => hJ' _
  have eb := gen_trans hb (𝟙 Y) y (mapsAtExp_le_b L L' pr ε p jN jL hy) m₁
  have ea := gen_trans ha (𝟙 Y) y (mapsAtExp_le_a L L' pr ε p jN jL hy) m₂
  have ew := gm_isGen hw p y jN (fun i => J (p ≫ pr i)) jL (J' p) hy.1 (hJ.mem pr p) hy.2 (hJ' p)
  have el := gm_linComb L pr ε p y jN (fun i => J (p ≫ pr i)) hy.1 (hJ.mem pr p)
  refine (gm_res _ y _ hy _).trans (eb.trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((map_zpow _ _ _).trans (congrArg (· ^ n) ((gm_pull (𝟙 Y) p y _ hy _).trans
      ((congrArg (fun q : Y ⟶ X' => gv w q y jN jL) (Category.id_comp p)).trans
        (ew.trans (congrArg (fun x => x * _ * _) el)))))) ((gm_res _ y _ hy _).trans ea))).symm))
  rw [e]
  simp only [trF, wv, Category.id_comp, Fintype.prod_unique, mul_zpow, ← Finset.prod_zpow, inv_zpow, ← zpow_mul,
    mul_comm n]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.MumCmp.Point
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MdbarZeroOfHolo
section
set_option autoImplicit false

noncomputable section

open Filter Topology Matrix
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.HermFrame
open scoped Matrix ContDiff

namespace GlobalTheory.ChernCalc.FrameChange

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
variable {r : Type*} [Fintype r] [DecidableEq r] {H A B : E → Matrix r r ℂ} {z : E}

theorem conn_mul_mul (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det)
    (hA : MContDiffAt 1 A z) (hAu : IsUnit (A z).det) (hB : MContDiffAt 1 B z) (hBu : IsUnit (B z).det)
    (hB0 : ∀ η, mdbar B z η = 0) (ξ : E) :
    conn (fun x => A x * H x * (B x)ᴴ) z ξ = (A z)ᵀ⁻¹ * (conn H z ξ * (A z)ᵀ + (mdel A z ξ)ᵀ) := by
  refine (eq_conn_of_compatible ?_ ?_).symm
  · simp only [det_mul, det_conjTranspose]
    exact (hAu.mul hu).mul hBu.star
  · rw [mdel_mul (hA.mul h) hB.conjTranspose, mdel_mul hA h, mdel_conjTranspose, hB0, ← conn_transpose_mul hu,
      transpose_mul, transpose_nonsing_inv]
    simp only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hAu, transpose_add, transpose_mul, Matrix.add_mul,
      conjTranspose_zero, transpose_transpose, Matrix.mul_zero, zero_add]

theorem curv_mul_mul (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det)
    (hA : MContDiffAt 2 A z) (hAu : IsUnit (A z).det) (hA0 : ∀ᶠ x in 𝓝 z, ∀ η, mdbar A x η = 0)
    (hB : MContDiffAt 2 B z) (hBu : IsUnit (B z).det) (hB0 : ∀ᶠ x in 𝓝 z, ∀ η, mdbar B x η = 0) (ξ η : E) :
    curv (fun x => A x * H x * (B x)ᴴ) z ξ η = (A z)ᵀ⁻¹ * curv H z ξ η * (A z)ᵀ := by
  have he : (fun x => conn (fun x => A x * H x * (B x)ᴴ) x ξ) =ᶠ[𝓝 z]
      fun x => (A x)ᵀ⁻¹ * (conn H x ξ * (A x)ᵀ + (mdel A x ξ)ᵀ) := by
    filter_upwards [h.eventually_two, h.eventually_isUnit hu, hA.eventually_two,
      hA.eventually_isUnit hAu, hB.eventually_two, hB.eventually_isUnit hBu, hB0] with x h1 h2 h3 h4 h5 h6 h7
    exact conn_mul_mul (h1.of_le one_le_two) h2 (h3.of_le one_le_two) h4 (h5.of_le one_le_two) h6 h7 ξ
  have hA1 : MContDiffAt 1 (fun x => (A x)ᵀ) z := (hA.of_le one_le_two).transpose
  have hAu' : IsUnit (A z)ᵀ.det := by rwa [det_transpose]
  have hc : MContDiffAt 1 (fun x => conn H x ξ) z := h.conn hu (by norm_num) ξ
  have hd : MContDiffAt 1 (fun x => (mdel A x ξ)ᵀ) z := (hA.mdel (by norm_num) ξ).transpose
  have h0 : mddbar A z ξ η = 0 := by
    rw [← mdel_mdbar hA, mdel_congr (B := fun _ => 0) (hA0.mono fun x hx => hx η), mdel_const]
  rw [curv, mdbar_congr he, mdbar_mul (hA1.inv hAu') ((hc.mul hA1).add hd), mdbar_inv hA1 hAu',
    mdbar_add (hc.mul hA1) hd, mdbar_mul hc hA1, mdbar_transpose (fun x => mdel A x ξ), mdbar_mdel hA, h0,
    mdbar_transpose A, hA0.self_of_nhds, curv]
  simp [Matrix.mul_assoc]

end General

variable {n : ℕ} {r : Type} [Fintype r] {T : V n → Matrix r r ℂ} {v : V n}


omit [Fintype r] in
theorem two_of_holo (h : ∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => T u a b) x) : MContDiffAt 2 T v :=
  fun a b => ((SCV.analyticAt_iff_eventually_differentiableAt.2 (h a b)).contDiffAt).restrict_scalars ℝ

theorem mdbar_zero_of_holo (h : ∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => T u a b) x) :
    ∀ᶠ x in 𝓝 v, ∀ η, mdbar T x η = 0 :=
  (eventually_all.2 fun a => eventually_all.2 fun b => h a b).mono fun x hx η => by
    ext a b
    rw [mdbar_apply, dbar_eq_zero (hx a b)]
    rfl

theorem conn_curv_frame : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G₂ T K : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => T u a b) x) → IsUnit (T v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => K u a b) x) → IsUnit (K v).det → (∀ᶠ x in 𝓝 v, G₂ x = T x * G x * (K x)ᴴ) → (∀ ξ, conn G₂ v ξ = (T v)ᵀ⁻¹ * (conn G v ξ * (T v)ᵀ + (mdel T v ξ)ᵀ)) ∧ ∀ ξ η, curv G₂ v ξ η = (T v)ᵀ⁻¹ * curv G v ξ η * (T v)ᵀ := by
  intro n r _ _ G G₂ T K v hG hGu hT hTu hK hKu he
  have hG2 : MContDiffAt 2 G v := hG.of_le (by norm_cast)
  refine ⟨fun ξ => ?_, fun ξ η => ?_⟩
  · rw [conn_congr he]
    exact conn_mul_mul (hG2.of_le one_le_two) hGu ((two_of_holo hT).of_le one_le_two) hTu
      ((two_of_holo hK).of_le one_le_two) hKu (mdbar_zero_of_holo hK).self_of_nhds ξ
  · rw [curv_congr he]
    exact curv_mul_mul hG2 hGu (two_of_holo hT) hTu (mdbar_zero_of_holo hT) (two_of_holo hK) hKu
      (mdbar_zero_of_holo hK) ξ η

end GlobalTheory.ChernCalc.FrameChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchRestrictedEqZeroOfNoComplexPoints
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem archInt_eq_zero_of_isEmpty {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}
    (hq : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) (L M : HermLB q) (e : ℕ)
    {r : M.B.ι → Z.functionFieldˣ} (hr : IsRatSec M.B r) : L.archInt M e hr = 0 := by
  unfold HermLB.archInt
  refine finsum_eq_zero_of_forall_eq_zero fun σ => ?_
  haveI := hq σ
  simp [Weight.chernInt, MeasureTheory.integral_of_isEmpty]

theorem mixArch_eq_zero_of_isEmpty {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}
    (hq : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) {e : ℕ} (L : Fin e → HermLB q) (M : HermLB q)
    {r : M.B.ι → Z.functionFieldˣ} (hr : IsRatSec M.B r) : mixArch L M hr = 0 := by
  unfold mixArch
  simp [archInt_eq_zero_of_isEmpty hq, FibreProj.pol]

theorem mixArch_resArch_eq_zero_of_noCxPts : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), (∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) → ∀ (e : ℕ) (L : Fin e → HermLB q) (M : HermLB q), (∀ (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), mixArch L M hr = 0) ∧ ∀ (t : M.B.Sec) (z : Y), resArch L M t z = 0 := by
  intro k _ Y _ q hq e L M
  refine ⟨fun r hr => mixArch_eq_zero_of_isEmpty hq L M hr, fun t z => ?_⟩
  unfold resArch
  split_ifs with h
  · refine mixArch_eq_zero_of_isEmpty (fun σ => ?_) _ _ _
    exact (Points.PtsOver.map (cloι z) rfl _ : CxPts (cloι z ≫ q) σ → CxPts q σ).isEmpty
  · rfl

end GlobalTheory.MixHt
end

