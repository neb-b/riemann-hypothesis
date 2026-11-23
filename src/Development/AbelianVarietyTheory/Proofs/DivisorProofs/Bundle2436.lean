module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPtCompClosedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1988
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0541
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0635
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonvanishingDetLineSectionOfHorizontal
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open Formalism.L2.Pj GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.DetLine.FromGeneric GlobalTheory.ShFam.Hor.Sec

namespace GlobalTheory.DetLine.FromHorizontal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_renumber {S : Scheme.{0}} {t : SAB H S} {R : Type} [CommRing R] {m n : ℕ} (h : m = n)
    {x x' : Sp R ⟶ S} (hx : x = x') {v v' : Fin n → (Sp (DualNumber R) ⟶ t.G.left)}
    {u u' : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hu : ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → v i = u k)
    (hu' : ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → v' i = u' k) {M : Matrix (Fin n) (Fin n) R}
    (hM : ∀ i, IsCombAtG t x v (M i) (v' i)) :
    ∃ M' : Matrix (Fin m) (Fin m) R, M'.det = M.det ∧ ∀ i, IsCombAtG t x' u (M' i) (u' i) := by
  subst h hx
  obtain rfl : v = u := funext fun i => hu i i rfl
  obtain rfl : v' = u' := funext fun i => hu' i i rfl
  exact ⟨M, rfl, hM⟩

theorem comb_left {S : Scheme.{0}} {t : SAB H S} {R : Type} [CommRing R] {x : Sp R ⟶ S} {n : ℕ} {a : Fin n → R}
    {u : Fin n → (Sp (DualNumber R) ⟶ t.G.left)} {z : epsAt x ⟶ t.G} (h : FramedFlatCoordinates.IsCombination x a u z) :
    IsCombAtG t x u a z.left :=
  have ⟨u', h₁, h₂⟩ := h
  ⟨u', h₁, congrArg CommaMorphism.left h₂.symm⟩

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {V : Set (gen Y)} {τ : E →+* ℂ} {e : c.F →+* ℂ}


variable (Y V τ) in
abbrev Fr (R : Type) [CommRing R] : Type := Framed c Y.t (genι Y) (genStr Y) V τ D.p D.q R

def Agree {R : Type} [CommRing R] (f : Fr Y V τ R)
    (u : ∀ ρ : E →+* ℂ, Fin (D.mult ρ) → (Sp (DualNumber R) ⟶ Y.t.G.left)) : Prop :=
  (∀ (i : Fin D.p) (k : Fin (D.mult τ)), (i : ℕ) = k → (f.2.1 i).left = u τ k) ∧
    ∀ (i : Fin D.q) (k : Fin (D.mult (conjEmb τ))), (i : ℕ) = k → (f.2.2.1 i).left = u (conjEmb τ) k

theorem exists_pullFr {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (b : Fr Y V τ R)
    {x' : Sp R' ⟶ gen Y} (hx : x' = spMap g ≫ b.1) :
    ∃ v w hf, factor g b (⟨x', v, w, hf⟩ : Fr Y V τ R') = 1 ∧
      ∀ u u', Agree b u → (∀ ρ i, u' ρ i = spMap (Chart.dualMapR g) ≫ u ρ i) →
        Agree (⟨x', v, w, hf⟩ : Fr Y V τ R') u' := by
  obtain ⟨j, h⟩ := b.2.2.2
  obtain ⟨v, w, h', a, a'⟩ := exists_pull g h hx
  refine ⟨v, w, ⟨_, h'⟩, ?_, fun u u' hu hu' => ⟨fun i k e => ?_, fun i k e => ?_⟩⟩
  · have h1 : IsChg Y.t (genι Y) g b.1 b.2.1 b.2.2.1 x' v w 1 1 := by
      refine ⟨hx, fun i => ?_, fun i => ?_⟩
      · simp only [← a]; exact DetExtendZero.comb_one (fun k => (h'.2.2.1.1 k).1) i
      · simp only [← a']; exact DetExtendZero.comb_one (fun k => (h'.2.2.2.1 k).1) i
    have := (factor_spec g b ⟨x', v, w, _, h'⟩ hx).2 1 1 h1
    rw [Matrix.det_one, Matrix.det_one, _root_.mul_one] at this
    exact this.symm
  · rw [hu', ← hu.1 i k e]; exact a i
  · rw [hu', ← hu.2 i k e]; exact a' i

theorem hor_factor (hτ : τ (H.rt : E) = H.rt0) {h : CxFr Y e → ℂ} (hh : HorFn τ h) {a a' : CxFr Y e} (hi : Inner a.1)
    (ha : a.1 = a'.1) {f f' : Fr Y V τ ℂ} (hf : f.1 = a.1.1) (hf' : f'.1 = a'.1.1) (hm : Agree f a.2.v)
    (hm' : Agree f' a'.2.v) : h a' = factor (RingHom.id ℂ) f f' * h a := by
  have hx : f'.1 = spMap (RingHom.id ℂ) ≫ f.1 := by rw [DetExtendZero.spMap_id, Category.id_comp, hf, hf', ha]
  obtain ⟨j, k⟩ := f.2.2.2
  obtain ⟨j', k'⟩ := f'.2.2.2
  obtain ⟨-, M, N, hc⟩ := exists_chg _ k k' hx
  have h1 := (factor_spec _ f f' hx).2 M N hc
  have h2 := (chg_isUnit k k' hc).1
  obtain ⟨-, hM, hN⟩ := hc
  simp only [DetExtendZero.dual_id, Category.id_comp] at hM hN
  obtain ⟨M', eM, hM'⟩ := exists_renumber (GlobalTheory.Harm.mult_of_mem D hτ) (congrArg (· ≫ genι Y) hf') hm.1 hm'.1
    fun i => comb_left (hM i)
  obtain ⟨N', eN, hN'⟩ := exists_renumber (GlobalTheory.Harm.mult_conjEmb_of_mem D hτ) (congrArg (· ≫ genι Y) hf') hm.2 hm'.2
    fun i => comb_left (hN i)
  have := hh.2.1 a a' M' N' hi ⟨ha, hM'⟩ ⟨ha, hN'⟩
  rw [eM, eN, h1] at this
  exact h2.mul_right_cancel (by rw [this]; ring)

theorem exists_section_of_horFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ) (e : c.F →+* ℂ) (h : CxFr Y e → ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y) (V : Set (gen Y)), IsOpenImmersion io → Set.range io = V → io ≫ genStr Y = B.str → τ (H.rt : E) = H.rt0 → HorFn τ h → ∃ σb : RuleY Y, SecY Y V τ σb ∧ NzY Y V τ σb := by
  intro E _ _ _ H D l Xo c O _ β Y τ e h B io V hio hV hs hτ hh
  obtain ⟨W, hW, φ, fr, a, hy, hφ, ha, hv, hf⟩ :=
    GlobalTheory.ShFam.HolFrames.exists_affine_holFrames E H D l Xo c O β Y e B io hio hs
  let sp (y : B.X) : Sp Γ(B.X, W y) ⟶ B.X := (hW y).fromSpec
  have hr {T : Scheme.{0}} (x : T ⟶ B.X) : Set.range (x ≫ io) ⊆ V := by
    rintro _ ⟨z, rfl⟩
    rw [← hV, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  choose bv bw hb hm using fun y =>
    (EigParts.eigFrame_match E H D l Xo c O β Y τ hτ V _ (φ y) (sp y ≫ io) (hφ y) (hr _) (fr y)).1
  let b (y : B.X) : Fr Y V τ Γ(B.X, W y) := ⟨sp y ≫ io, bv y, bw y, _, hb y⟩
  let gm {U : B.X.Opens} {z : B.X} (hz : z ∈ U) : Γ(B.X, U) →+* B.X.presheaf.stalk z := (B.X.presheaf.germ U z hz).hom
  have hloc {y z : B.X} (hz : z ∈ W y) : locPt B.X z ≫ io = spMap (gm hz) ≫ (b y).1 := by
    rw [← Category.assoc]
    exact congrArg (· ≫ io) ((hW y).fromSpecStalk_eq_fromSpecStalk hz).symm
  choose ev ew he _ using fun z => exists_pullFr (gm (hy z)) (b z) (hloc (hy z))
  let fz (z : B.X) : Fr Y V τ (B.X.presheaf.stalk z) := ⟨locPt B.X z ≫ io, ev z, ew z, he z⟩
  have hgen (z : B.X) : genPt B.X ≫ io = spMap (algebraMap _ B.X.functionField) ≫ (fz z).1 := by
    rw [genPt_eq z, Category.assoc]
  obtain ⟨v₀, w₀, ⟨j₀, h₀⟩, -⟩ := exists_pullFr _ (fz (genericPoint B.X)) (hgen _)
  let a₀ : Fr Y V τ B.X.functionField := ⟨genPt B.X ≫ io, v₀, w₀, j₀, h₀⟩
  choose ε hε using fun z => (factor_spec _ (fz z) a₀ (hgen z)).1
  have hu {y z : B.X} (hz : z ∈ W y) : IsUnit (factor (gm hz) (b y) (fz z)) := (factor_spec _ _ _ (hloc hz)).1
  have hk (y : B.X) : a₀.1 = spMap (fnOf (W y) (gen_mem (hy y))) ≫ (b y).1 := hloc (gen_mem (hy y))
  choose δ hδ using fun y => (factor_spec _ (b y) a₀ (hk y)).1
  have hδε {y z : B.X} (hz : z ∈ W y) : (δ y : B.X.functionField) =
      ε z * algebraMap _ B.X.functionField (factor (gm hz) (b y) (fz z)) := by
    rw [hδ, hε, ← factor_comp _ _ _ _ _ (hloc hz) (hgen z)]
    congr 1
    exact (RingHom.ext fun r => algebraMap_germ hz r).symm
  have hg {y z : B.X} (hz : z ∈ W y) : germOf z (ε z)⁻¹ = germOf z (δ y)⁻¹ := by
    rw [germOf_eq_iff, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, inv_div_inv, ← inv_div, hδε hz,
      mul_div_cancel_left₀ _ (ε z).ne_zero]
    exact UnitAt.inv ⟨_, hu hz, rfl⟩
  let Dv : B.Dv := show cartierGroup B.X from ⟨fun z => germOf z (ε z)⁻¹, fun y => ⟨W y, hy y, (δ y)⁻¹, fun z hz => hg hz⟩⟩
  have hD (y : B.X) (z : B.X) (hz : z ∈ W y) : Dv.IsEqn z (δ y)⁻¹ := hg hz
  obtain ⟨hne, hd⟩ := _root_.GlobalTheory.CxPtsDense.nonempty_and_dense c.F B e
  have hA := hd (io ⁻¹ᵁ (genBd Y).compl) (by
    obtain ⟨_, ⟨z, rfl⟩, hz⟩ := Y.jQ_dense.inter_open_nonempty _ io.isOpenEmbedding.isOpen_range
      ⟨_, genericPoint B.X, rfl⟩
    exact ⟨z, fun hb => hb hz⟩)
  let R := AnRead.all B.str e B.dim
  choose u hu₁ he₁ using fun y => exists_extension R io hA (isOpen_ptsIn (W y)) (fun z _ => ha y z) (hf y) hh.2.2.1 hh.2.2.2
  choose u' hu' he' using fun y => exists_extension R io hA (isOpen_ptsIn (W y)) (fun z _ => ha y z) (hf y)
    (h := fun a => (h a)⁻¹) (fun V _ _ _ B a hB ha hi => (hh.2.2.1 V B a hB ha hi).inv fun b hb => hh.1 _ (hi b hb))
    (logGrowth_inv hh.2.2.2)
  have h0 (y) (z) (hz : z ∈ ptsIn _ _ (io ⁻¹ᵁ (genBd Y).compl)) : h (a y z) ≠ 0 :=
    hh.1 _ ((inner_iff (ha y z)).2 hz)
  have htr (y y') (U : B.X.Opens) (r : Γ(B.X, U))
      (hr : ∀ hU, fnOf U hU r = (δ y' : B.X.functionField) / (δ y : B.X.functionField)) (p : CxPts B.str e)
      (h₁ : p ∈ ptsIn _ _ (W y)) (h₂ : p ∈ ptsIn _ _ (W y')) (h₃ : p ∈ ptsIn _ _ U)
      (hz : p ∈ ptsIn _ _ (io ⁻¹ᵁ (genBd Y).compl)) : h (a y p) = CxPts.ev _ _ U r p * h (a y' p) := by
    let z : B.X := p.1 (IsLocalRing.closedPoint ℂ)
    let χ : B.X.presheaf.stalk z →+* ℂ := (Scheme.stalkClosedPointTo (R := .of ℂ) p.1).hom
    have hχ {U : B.X.Opens} (h : p ∈ ptsIn _ _ U) : χ.comp (gm (mem_ptsIn.1 h)) = evHom h :=
      (congrArg CommRingCat.Hom.hom (HolFrames.valR_eq_germ p.1 U h)).symm
    have hp : p.1 ≫ io = spMap χ ≫ (fz z).1 := by
      rw [← Category.assoc]
      exact congrArg (· ≫ io) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of ℂ) p.1).symm
    have hq {y : B.X} (h : p ∈ ptsIn _ _ (W y)) : p.1 ≫ io = spMap (evHom h) ≫ (b y).1 := by
      rw [← hχ, DetExtendZero.spMap_comp, Category.assoc, ← hloc, hp]
    obtain ⟨v, w, k, e₁, m⟩ := exists_pullFr _ (b y) (hq h₁)
    obtain ⟨v', w', k', e₂, m'⟩ := exists_pullFr _ (b y') (hq h₂)
    rw [hor_factor hτ hh ((inner_iff (ha y' p)).2 hz) (Subtype.ext ((ha y' p).trans (ha y p).symm))
      (f := ⟨_, v', w', k'⟩) (f' := ⟨_, v, w, k⟩) (ha y' p).symm (ha y p).symm
      (m' _ _ (hm y') (hv y' p h₂)) (m _ _ (hm y) (hv y p h₁))]
    congr 1
    have e₃ := factor_comp (evHom h₂) (RingHom.id ℂ) (b y') ⟨_, v', w', k'⟩ ⟨_, v, w, k⟩ (hq h₂)
      (by rw [DetExtendZero.spMap_id, Category.id_comp])
    rw [e₂, map_one, _root_.mul_one, RingHom.id_comp, ← hχ,
      factor_comp _ χ _ (fz z) ⟨_, v, w, k⟩ (hloc (mem_ptsIn.1 h₂)) hp] at e₃
    rw [← hχ, factor_comp _ χ _ (fz z) ⟨_, v, w, k⟩ (hloc (mem_ptsIn.1 h₁)) hp] at e₁
    have e₄ : factor (gm (mem_ptsIn.1 h₂)) (b y') (fz z) =
        factor (gm (mem_ptsIn.1 h₁)) (b y) (fz z) * gm (mem_ptsIn.1 h₃) r := by
      refine IsFractionRing.injective (B.X.presheaf.stalk z) B.X.functionField (mul_left_cancel₀ (ε z).ne_zero ?_)
      rw [map_mul, ← _root_.mul_assoc, ← hδε, ← hδε]
      erw [algebraMap_germ]
      rw [hr, mul_div_cancel₀ _ (δ y).ne_zero]
    rw [← e₃, e₄, map_mul, ← _root_.mul_assoc, e₁, _root_.one_mul, ev_eq h₃, ← hχ]
    rfl
  obtain ⟨s, hs⟩ := exists_generates B Dv
    (_root_.GlobalTheory.ShFam.Hor.riemannRoch_ne_bot_of_holomorphicSection_ne_bot c.F B _ R _ (holSec_ne_bot hA _ W (fun y => (δ y)⁻¹) hy hD u hu₁
      (fun y z hz => by rw [he₁ y hz]; exact h0 y z hz.2) fun y y' r hr' z hz => by
        have hz' := mem_ptsIn_inf.1 hz.1
        rw [he₁ y ⟨hz'.1, hz.2⟩, he₁ y' ⟨hz'.2, hz.2⟩]
        exact htr y y' _ r (fun hU => by
          rw [hr', Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, inv_div_inv]) z hz'.1 hz'.2 hz.1 hz.2))
    (_root_.GlobalTheory.ShFam.Hor.riemannRoch_ne_bot_of_holomorphicSection_ne_bot c.F B _ R _ (holSec_ne_bot hA _ W δ hy (fun y y' hy => inv_inv (δ y) ▸ (hD y y' hy).neg) u' hu'
      (fun y z hz => by rw [he' y hz]; exact inv_ne_zero (h0 y z hz.2)) fun y y' r hr' z hz => by
        have hz' := mem_ptsIn_inf.1 hz.1
        rw [he' y ⟨hz'.1, hz.2⟩, he' y' ⟨hz'.2, hz.2⟩]
        rw [eq_mul_inv_iff_mul_eq₀ (h0 y' z hz.2), htr y' y _ r hr' z hz'.2 hz'.1 hz.1 hz.2, _root_.mul_comm,
          mul_inv_cancel_right₀ (h0 y z hz.2)]))
  obtain ⟨σ, h1, h2, -⟩ := exists_section E H l c _ _ Y.t (genι Y) (genStr Y) τ D.p D.q B.X io V hio hV
    (hV ▸ frameCover_gen E H D l Xo c O β Y io.opensRange τ hτ) j₀ v₀ w₀ s h₀ fun z => by
      obtain ⟨j, hj⟩ := he z
      obtain ⟨-, M, N, hc⟩ := exists_chg _ hj h₀ (hgen z)
      obtain ⟨_, ⟨t, rfl⟩, ht⟩ := (show Dv.IsEqn z (ε z)⁻¹ from rfl).generatesAt_iff.1 (hs z)
      refine ⟨j, ev z, ew z, M, N, t, hj, hc, ?_⟩
      rw [(factor_spec _ (fz z) a₀ (hgen z)).2 M N hc, ← hε, ht, Units.val_inv_eq_inv_val]
      have := (ε z).ne_zero
      field_simp
  exact ⟨σ, h1, h2⟩

end GlobalTheory.DetLine.FromHorizontal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOActNDescend
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.GaloisActDesc

theorem exists_oActN_descend : ∀ (O : Type) [Ring O] (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (ν : Ga → (A.left ⟶ A.left)) (act : OActN O A), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → GlobalTheory.ZM.IsGaloisCover Ga ν φ → (∀ a, IsGrpPullback A A (ρ a) (ν a)) → (∀ a c, (act.act c).left ≫ ν a = ν a ≫ (act.act c).left) → ∃ act₀ : OActN O A₀, ∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left := by
  intro O _ X Y π Ga _ ρ A _ _ A₀ _ _ φ ν act hπ _ _ hp hφ _ hcomm
  have : Flat π := by have := hπ.etale; infer_instance
  have : Surjective π := hπ.onto
  have eφ : Epi φ := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hφ
  have hi : ∀ c, ∃ f : A₀ ⟶ A₀, (act.act c).left ≫ φ = φ ≫ f.left := by
    intro c
    obtain ⟨g, hg, -⟩ := hφ.existsUnique_desc ((act.act c).left ≫ φ) (fun a ↦ by
      rw [← Category.assoc, ← hcomm, Category.assoc, hφ.inv])
    have hw : g ≫ A₀.hom = A₀.hom := by
      rw [← cancel_epi φ, reassoc_of% hg, hp.1.w, Over.w_assoc]
    exact ⟨Over.homMk g hw, hg.symm⟩
  choose f hf using hi
  refine ⟨⟨f, fun x ↦ ?_, ?_, fun x y ↦ ?_, fun x y ↦ ?_⟩, hf⟩
  · have := act.hom x
    exact GlobalTheory.ActDescent.isMonHom_descend hp hp (act.act x) (f x) (hf x)
  · refine GlobalTheory.ActDescent.over_hom_ext hp.1 ?_
    rw [← hf, act.one, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  · refine GlobalTheory.ActDescent.over_hom_ext hp.1 ?_
    rw [← hf, act.mul, Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, hf, Category.assoc]
  · refine GlobalTheory.ActDescent.over_hom_ext hp.1 ?_
    let φ₀ : Over.mk (A.hom ≫ π) ⟶ A₀ := Over.homMk φ hp.1.w
    have h := hp.2 A (act.act x) (act.act y) (φ₀ ≫ f x) (φ₀ ≫ f y) (hf x).symm (hf y).symm
    rw [← MonObj.comp_mul] at h
    rw [← hf, act.add, ← h]
    rfl

end GlobalTheory.GaloisActDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenThetaNonvanishingDescendedGroup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_open_theta_descent : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), Surjective π → ∀ (G' : Over S) [GrpObj G'] (E : Emb π G') (N : Near π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → ∀ (L : LB G'.left), E.Theta L → ∀ (G : Over (Sp R)) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), β ≫ G.hom = G'.hom ≫ π → IsOpenImmersion i.left → N.u ≫ β = pullback.fst _ _ ≫ i.left → ∃ (θ : L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) ∧ ∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ k, g ∈ G'.left.basicOpen (θ.f k) := by
  intro R _ _ S π hπ G' _ E N fU l hl hlf L hT G β i hβ hi hu
  obtain ⟨θ, OY, ⟨y₀, hy₀⟩, hθ⟩ := hT
  haveI := E.imm
  obtain ⟨W, hW, hWY⟩ := (E.j.isEmbedding.isInducing.isOpen_iff).1 OY.isOpen
  have hrng := _root_.GlobalTheory.Mum.Emb.range_closed R S π G' E
  have e1 : ∀ z, E.H.ι (l z) = N.u z := fun z => by rw [← Scheme.Hom.comp_apply, hl]
  have e2 : ∀ z, E.f (l z) = fU (pullback.fst N.U.hom π z) := fun z => by
    rw [← Scheme.Hom.comp_apply, hlf, Scheme.Hom.comp_apply]
  have e3 : ∀ z, β (N.u z) = i.left (pullback.fst N.U.hom π z) := fun z => by
    rw [← Scheme.Hom.comp_apply, hu, Scheme.Hom.comp_apply]
  have e4 : ∀ x, G.hom (β x) = π (G'.hom x) := fun x => by
    rw [← Scheme.Hom.comp_apply, hβ, Scheme.Hom.comp_apply]
  have hWj : ∀ y, y ∈ OY ↔ E.j y ∈ W := fun y => by
    show y ∈ (OY : Set E.Y.left) ↔ _
    rw [← hWY]; rfl
  refine ⟨θ, ⟨i.left '' (fU ⁻¹' W), i.left.isOpenEmbedding.isOpenMap _ (hW.preimage fU.continuous)⟩, ?_, ?_⟩
  · obtain ⟨g₀, hg₀c, hg₀f⟩ := hrng.2 hπ y₀
    obtain ⟨z, hz⟩ := N.all (E.H.ι g₀) hg₀c
    have hlz : l z = g₀ := E.H.ι.isOpenEmbedding.injective (by rw [e1, hz])
    refine ⟨i.left (pullback.fst N.U.hom π z), ⟨pullback.fst N.U.hom π z, ?_, rfl⟩, ?_⟩
    · show fU (pullback.fst N.U.hom π z) ∈ W
      rw [← e2 z, hlz, hg₀f]
      exact (hWj y₀).1 hy₀
    · rw [← e3, e4, hz]
      exact hg₀c
  · rintro g ⟨w, hw, hwg⟩ hc
    have hc' : π (G'.hom g) = closedPoint R := by rw [← e4]; exact hc
    obtain ⟨z, rfl⟩ := N.all g hc'
    have hzw : pullback.fst N.U.hom π z = w := i.left.isOpenEmbedding.injective (by rw [hwg, ← e3])
    have hc'' : π (G'.hom (E.H.ι (l z))) = closedPoint R := by rw [e1]; exact hc'
    obtain ⟨y, hy⟩ := hrng.1 (l z) hc''
    have hyO : y ∈ OY := (hWj y).2 (by rw [← hy, e2, hzw]; exact hw)
    obtain ⟨k, hk⟩ := hθ (l z) y hyO hc'' hy
    exact ⟨k, by rwa [e1] at hk⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodGeneratorOnOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TauOnOpen

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Sp R).Opens}

theorem tauW_isGen (ψW : PsiOn D W) (a b : D.X) : (ψW.tau a b).IsGen :=
  DVR.mulGen_isGen _ _ _ _ _ _ _
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (ψW.psi_gen _) (DVR.invGen_isGen _ _ _ _ (ψW.psi_gen _)))
      (DVR.invGen_isGen _ _ _ _ (ψW.psi_gen _)))
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D.rig_gen _))

theorem val_tauW_generic (ψW : PsiOn D W) (a b : D.X) (lam : (TK R).left ⟶ W.toScheme) (h : lam ≫ W.ι = jK R)
    (z : (TK R).left) (J) (hJ : Good D.P.L z J) : val (ψW.tau a b) lam z J = val (D.tau a b) (𝟙 _) z J := by
  have hW : lam ≫ W.ι = 𝟙 _ ≫ jK R := h.trans (Category.id_comp _).symm
  obtain ⟨mu, l₁, l₂⟩ : ∃ mu : (TK R).left ⟶ (jK R ⁻¹ᵁ W).toScheme, mu ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ ∧
      mu ≫ (jK R ∣_ W) = lam :=
    ⟨(isPullback_morphismRestrict (jK R) W).lift _ _ hW,
      (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩
  have vψ : ∀ χ, val (ψW.psi χ) lam z J = val (D.psi χ) (𝟙 _) z J := fun χ => by
    have e := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq χ) mu).trans (val_pull hJ _ _ _))
    rw [l₁, l₂] at e
    exact e
  have vρ : val (D.rigW W) lam z J = val D.rigK (𝟙 _) z J := by
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    exact congrArg (fun q => val D.rig q z J) hW
  refine (TauPull.val_tauW ψW lam hJ a b).trans (Eq.trans ?_ (TauPull.val_tau (𝟙 _) hJ a b).symm)
  rw [← vψ, ← vψ, ← vψ, ← vρ]

end GlobalTheory.TauOnOpen

namespace GlobalTheory

theorem exists_tau_onOpen : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens) (ψW : PsiOn D W) (a b : D.X), ∃ t : LB.Gen (LB.LinComb D.P.L (lamPts (toUnit (TW W) ≫ D.c a) (toUnit (TW W) ≫ D.c b)) negε), t.IsGen ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ W.toScheme) (z : Z) J, Good D.P.L z J → val t r z J = val (ψW.tau a b) r z J) ∧ ∀ (lam : (TK R).left ⟶ W.toScheme), lam ≫ W.ι = jK R → ∀ z J, Good D.P.L z J → val t lam z J = val (D.tau a b) (𝟙 _) z J := by
  intro R _ _ D W ψW a b
  obtain ⟨t, ht, hv⟩ : ∃ t : LB.Gen (LB.LinComb D.P.L (lamPts (toUnit (TW W) ≫ D.c a) (toUnit (TW W) ≫ D.c b)) negε),
      t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (TW W).left) (z : Z) (J), Good D.P.L z J →
        val t r z J = val (ψW.tau a b) r z J := by
    refine exists_gen D.P.isLB (fun U _ h => ?_) (ψW.tau a b) (TauOnOpen.tauW_isGen ψW a b)
    have e₁ : (toUnit (TW W) ≫ D.c (a + b)).left = ((toUnit (TW W) ≫ D.c a) * (toUnit (TW W) ≫ D.c b)).left := by
      rw [D.c_add]; exact congrArg (fun q : TW W ⟶ D.P.A => q.left) (MonObj.comp_mul (toUnit (TW W)) (D.c a) (D.c b))
    have e₂ : (toUnit (TW W)).left ≫ eSec D.P.A = (1 : TW W ⟶ D.P.A).left := rfl
    simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, e₁, e₂]
    simp [lamPts, negε]
  exact ⟨t, ht, hv, fun lam h z J hJ => (hv _ lam z J hJ).trans (TauOnOpen.val_tauW_generic ψW a b lam h z J hJ)⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodsPulledDegenerationData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TauPullOn

open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull GlobalTheory.FactorPull
open GlobalTheory.PsiEvenPull (proj)

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {θ : R →+* V} {D₀ : DegPre R}
  {D₁ : DegPre V} (hD : IsPullDeg θ D₀ D₁) {z : (TK V).left} {J : ((TK V).left ⟶ D₀.P.A.left) → D₀.P.L.ι}
  {J₁ : ((TK V).left ⟶ D₁.P.A.left) → D₁.P.L.ι} (hJ : Good D₀.P.L z J) (hJ₁ : Good D₁.P.L z J₁)
include hJ hJ₁

theorem psiW_val (x : D₁.X) : val (hD.psiW.psi (hD.xe x)) hD.g z J =
    (om hD.w z J J₁ (D₁.xK x))⁻¹ * val (D₁.psi x) (𝟙 _) z J₁ := by
  have e := PsiEvenPull.psi_pull hD x (𝟙 _) z hJ hJ₁
  simp only [Category.id_comp] at e
  exact e

theorem rigW_val : val (D₀.rigW hD.W) hD.g z J =
    om hD.w z J J₁ (1 : TK V ⟶ D₁.P.A).left * val D₁.rigK (𝟙 _) z J₁ := by
  have pm := (maps_iff hD.w _ (fun _ => eSec D₀.P.A) _ D₁.rig D₀.rig (specOf θ) _
    (rigPull_le (proj hD) (specOf θ) hD.he D₀.P.L) (fun _ => rfl)).1 hD.w_rig
  have e := pmaps_om (fun _ => hD.he) pm (jK V) z hJ hJ₁
  rw [Fintype.prod_unique, zpow_one] at e
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ₁ _ _ _).symm))
  rw [Category.id_comp]
  exact (congrArg (fun q => val D₀.rig q z J) hD.g_comm).trans e


omit hJ hJ₁ in
theorem tau_pull : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (D₀ : DegPre R) (D₁ : DegPre V) (hD : IsPullDeg θ D₀ D₁), ∃ (β₂ : (G2 D₁.P.A).left ⟶ (G2 D₀.P.A).left) (w₀ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ D₀.P.A D₀.P.L).pull β₂)), IsSquare (GlobalTheory.PsiEvenPull.proj hD) β₂ ∧ w₀.IsGen ∧ ∀ a b z J J₁, Good D₀.P.L z J → Good D₁.P.L z J₁ → val (D₁.tau a b) (𝟙 _) z J₁ = lamVal w₀ (lift (toUnit (TK V) ≫ D₁.c a) (toUnit (TK V) ≫ D₁.c b)).left z J J₁ * val (hD.psiW.tau (hD.xe a) (hD.xe b)) hD.g z J := by
  intro R V _ _ _ _ θ D₀ D₁ hD
  refine ⟨sqOf (pull_grp hD), lamIso (pull_grp hD) hD.w, isSquare_sqOf _, isGen_lamIso _ _ hD.w_gen,
    fun a b z J J₁ hJ hJ₁ => ?_⟩
  have g := gw_lam (pull_grp hD) hD.w (lift (toUnit (TK V) ≫ D₁.c a) (toUnit (TK V) ≫ D₁.c b)).left z hJ hJ₁
  have p := prod_lam (DVR.cP D₁ (TK V) a) (DVR.cP D₁ (TK V) b) (om hD.w z J J₁)
  rw [← DVR.cPoint_add] at p
  have l : lamVal (lamIso (pull_grp hD) hD.w) (lift (toUnit (TK V) ≫ D₁.c a) (toUnit (TK V) ≫ D₁.c b)).left z J J₁ =
      om hD.w z J J₁ (D₁.xK (a + b)) * (om hD.w z J J₁ (D₁.xK a))⁻¹ * (om hD.w z J J₁ (D₁.xK b))⁻¹ *
        om hD.w z J J₁ (1 : TK V ⟶ D₁.P.A).left := by
    refine Eq.trans ?_ (g.trans p)
    simp only [Category.assoc]
    rfl
  rw [l, TauPull.val_tauW _ _ hJ, TauPull.val_tau _ hJ₁, ← map_add (f := _), psiW_val hD hJ hJ₁, psiW_val hD hJ hJ₁,
    psiW_val hD hJ hJ₁, rigW_val hD hJ hJ₁]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TauPullOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVCommonPullback
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem exists_polAV_common_pullback : ∀ (Ω : Type) [Field Ω] (T T' : Scheme.{0}) (Q : PolAV T) (P' : PolAV T') (f : Sp Ω ⟶ T) (f' : Sp Ω ⟶ T') (G' : Over (Sp Ω)) [GrpObj G'] (a₁ : G'.left ⟶ Q.A.left) (a₂ : G'.left ⟶ P'.A.left), IsGrpPullback G' Q.A f a₁ → IsGrpPullback G' P'.A f' a₂ → LBIso (Q.L.pull a₁) (P'.L.pull a₂) → ∃ (P₀ : PolAV (Sp Ω)) (a : P₀.A.left ⟶ Q.A.left) (a' : P₀.A.left ⟶ P'.A.left) (e : G'.left ⟶ P₀.A.left), IsIso e ∧ e ≫ a = a₁ ∧ e ≫ a' = a₂ ∧ IsGrpPullback P₀.A Q.A f a ∧ IsGrpPullback P₀.A P'.A f' a' ∧ LBIso P₀.L (Q.L.pull a) ∧ LBIso P₀.L (P'.L.pull a') := by
  intro Ω _ T T' Q P' f f' G' _ a₁ a₂ h₁ h₂ hL
  obtain ⟨P₀, φ, hφ, hL₀⟩ := exists_pol_baseChange Q f
  obtain ⟨e, he, hea⟩ := grpPullback_iso h₁ hφ
  haveI := he
  have hinv : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have hφ' : φ = e.inv.left ≫ a₁ := by
    rw [← hea, ← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.id_comp]
  have hiso : IsIso e.hom.left := ⟨⟨e.inv.left, by rw [← Over.comp_left, e.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]⟩⟩
  refine ⟨P₀, φ, e.inv.left ≫ a₂, e.hom.left, hiso, hea, ?_, hφ, ?_, hL₀, ?_⟩
  · rw [← Category.assoc, ← Over.comp_left, e.hom_inv_id, Over.id_left, Category.id_comp]
  · exact ((isGrpPullback_of_iso e.symm).comp h₂).congr (Category.id_comp _) rfl
  · exact LBIso.trans P₀.isLB (pull_isLB Q.isLB _) (pull_isLB P'.isLB _) hL₀
      (GenSpread.lbIso_pull_comp e.inv.left hφ' rfl hL)

end GlobalTheory.UPoinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusKernelHopfLePowCotangentStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_frobenius_kernel_hopf_le_pow_cotangent : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H] [HopfAlgebra K H] [Module.Finite K H], Module.finrank K (H ⧸ frobKerIdeal p K H) ≤ p ^ Module.finrank K (Cot K H) := by
  first | exact @GlobalTheory.PDiv.FrobKerOrder.finrank_le_pow_finrank_cot | exact GlobalTheory.PDiv.FrobKerOrder.finrank_le_pow_finrank_cot | (intros; apply GlobalTheory.PDiv.FrobKerOrder.finrank_le_pow_finrank_cot <;> assumption)
end

