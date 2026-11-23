module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2268
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2379
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortCentralMove
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1857
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1745
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

namespace GlobalTheory.CechKS

theorem chartPt_sub : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) (V : X.Opens) (U : X.affineOpens) {n : ℕ} (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)) (hv : ∀ a, IsTanAtG t (LogKS.chart U) (v a)) (J₀ : Type) (W₀ : J₀ → t.G.left.Opens) (j : J₀ → t.PP.L.ι) (d : J₀ → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)) (hcov : ⨆ i, W₀ i = t.G.hom ⁻¹ᵁ (U.1 ⊓ V)) (hWj : ∀ i, W₀ i ≤ t.PP.L.U (j i)) (hfield : ∀ i, LogKS.IsField (W₀ i) (d i)) (hlift : ∀ i (h : W₀ i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), d i (W₀ i) ((t.G.hom.appLE U.1 (W₀ i) h).hom r) = (t.G.hom.appLE U.1 (W₀ i) h).hom (D r)) (hdiff : ∀ (i i' : J₀) (O : t.G.left.Opens), O ≤ W₀ i ⊓ W₀ i' → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), g₀ ≫ t.G.hom = spMap φ ≫ LogKS.chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → (∀ a, LogKS.IsTranslate t φ g₀ (v a) (w a)) → valR g₀ O (d i O f - d i' O f) = ∑ a, ∑ b, φ (Θ a b) * ((valR (w b) _ (t.PP.L.g (j i) (j i')).val).snd * valR g₀ _ (t.PP.L.g (j i) (j i'))⁻¹.val) * (valR (w a) O f).snd) {K : Type} [Field K] (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1) (y1 : Sp (DualNumber K) ⟶ X) (hU' : ⊤ ≤ y1 ⁻¹ᵁ U.1) (hy1 : ∀ r, ev y1 U.1 hU' r = TrivSqZeroExt.inl (ev x0 U.1 hU r) + TrivSqZeroExt.inr (ev x0 U.1 hU (D r))) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (m : A.left ⟶ t.G.left) (m' : A'.left ⟶ t.G.left) (i : A.left ⟶ A'.left) (u : Fin n → (epsR K ⟶ A)) (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (hm : IsGrpPullback A t.G x0 m) (hm' : IsGrpPullback A' t.G y1 m') (him : i ≫ m' = m) (hu : ∀ a, (u a).left ≫ m = spMap (dualMap (ev x0 U.1 hU)) ≫ v a) (M : LB A.left) (wg : LB.Iso (t.PP.L.pull m) M) (hwg : wg.IsGen) (i₁ i₂ : J₀) (Ω₁ Ω₂ : t.G.left.affineOpens) (hΩ₁ : Ω₁.1 ≤ W₀ i₁) (hΩ₂ : Ω₂.1 ≤ W₀ i₂) (p₁ p₂ : M.ι) (B : Type) [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left) (O : A'.left.Opens) (f : Γ(A'.left, O)) (w : Fin n → (Sp (DualNumber B) ⟶ A.left)) (hx : x ≫ A.hom = spMap (baseMap K B)) (hxW : ⊤ ≤ x ⁻¹ᵁ ((m ⁻¹ᵁ Ω₁.1 ⊓ M.U p₁) ⊓ (m ⁻¹ᵁ Ω₂.1 ⊓ M.U p₂))) (hxO : ⊤ ≤ x ⁻¹ᵁ (i ⁻¹ᵁ O)) (hw : ∀ a, IsTransl (baseMap K B) x (u a) (w a)) (l₁ l₂ : Sp B ⟶ A'.left) (h₁ : IsChartPt A' m m' Ω₁.1 (d i₁ Ω₁.1) u (Matrix.of fun a b => ev x0 U.1 hU (Θ a b)) (M.U p₁ ⊓ (t.PP.L.pull m).U (fun _ => j i₁)) (wg.s (p₁, fun _ => j i₁)) x l₁) (h₂ : IsChartPt A' m m' Ω₂.1 (d i₂ Ω₂.1) u (Matrix.of fun a b => ev x0 U.1 hU (Θ a b)) (M.U p₂ ⊓ (t.PP.L.pull m).U (fun _ => j i₂)) (wg.s (p₂, fun _ => j i₂)) x l₂), valR l₁ O f - valR l₂ O f = algebraMap (DualNumber K) B DualNumber.eps * ∑ a, ∑ b, baseMap K B ((Matrix.of fun a b => ev x0 U.1 hU (Θ a b)) a b) * ((valR (w b) _ (M.g p₁ p₂).val).snd * valR x _ (M.g p₁ p₂)⁻¹.val) * (valR (w a) (i ⁻¹ᵁ O) ((i.app O).hom f)).snd := by
  intro E _ _ _ H X t V U n v D Θ hv J₀ W₀ j d hcov hWj hfield hlift hdiff K _ x0 hU y1 hU' hy1 A _ A' _ m m' i u
    hi hm hm' him hu M wg hwg i₁ i₂ Ω₁ Ω₂ hΩ₁ hΩ₂ p₁ p₂ B _ _ x O f w hx hxW hxO hw l₁ l₂ h₁ h₂
  have hW₀ : ∀ k, W₀ k ≤ t.G.hom ⁻¹ᵁ U.1 := fun k p hp => by
    have : p ∈ t.G.hom ⁻¹ᵁ (U.1 ⊓ V) := hcov ▸ (le_iSup W₀ k) hp
    exact this.1
  have := t.semi.separated
  have hut : ∀ a, IsTangent (u a) := GlobalTheory.T.isTangent_of_fibre_pullback_tangent_at_chart t U v hv x0 hU A m u hm hu
  let Ω : t.G.left.affineOpens :=
    ⟨Ω₁.1 ⊓ Ω₂.1, GlobalTheory.T.isAffineOpen_inf_of_separated_over_affineOpen t.G.hom U Ω₁ Ω₂ (hΩ₁.trans (hW₀ _)) (hΩ₂.trans (hW₀ _))⟩
  have e₁ : Ω.1 ≤ Ω₁.1 := inf_le_left
  have e₂ : Ω.1 ≤ Ω₂.1 := inf_le_right
  have hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω.1) := fun p hp => ⟨(hxW hp).1.1, (hxW hp).2.1⟩
  obtain ⟨l₁', k₁⟩ := GlobalTheory.CechKS.exists_isChartPt t U v D hv (W₀ i₁) (hW₀ i₁) (d i₁) (hfield i₁) (hlift i₁ (hW₀ i₁)) x0 hU y1 hU' hy1
    A A' m m' u hm hm' hu Ω (e₁.trans hΩ₁) (Matrix.of fun a b => ev x0 U.1 hU (Θ a b))
    (M.U p₁ ⊓ (t.PP.L.pull m).U (fun _ => j i₁)) (wg.s (p₁, fun _ => j i₁)) B x hx hxΩ
  obtain ⟨l₂', k₂⟩ := GlobalTheory.CechKS.exists_isChartPt t U v D hv (W₀ i₂) (hW₀ i₂) (d i₂) (hfield i₂) (hlift i₂ (hW₀ i₂)) x0 hU y1 hU' hy1
    A A' m m' u hm hm' hu Ω (e₂.trans hΩ₂) (Matrix.of fun a b => ev x0 U.1 hU (Θ a b))
    (M.U p₂ ⊓ (t.PP.L.pull m).U (fun _ => j i₂)) (wg.s (p₂, fun _ => j i₂)) B x hx hxΩ
  obtain rfl : l₁' = l₁ := (k₁.of_le (hfield i₁) e₁ hΩ₁ hx hxΩ hut).unique hm'.1 h₁
  obtain rfl : l₂' = l₂ := (k₂.of_le (hfield i₂) e₂ hΩ₂ hx hxΩ hut).unique hm'.1 h₂
  have hwt : ∀ a, transl (baseMap K B) x (u a) = w a := fun a => (isTransl_transl _ x hx (u a)).unique (hw a)
  have hwx := fun a => (hw a).red (hut a)
  have := isAffineHom_of_field x0
  have : IsAffineHom m := MorphismProperty.of_isPullback (P := @IsAffineHom) hm.1.flip inferInstance
  obtain ⟨S, hS, hSx, hSv⟩ := _root_.GlobalTheory.CechKS.LinTan.exists_linComb A.hom ⟨m ⁻¹ᵁ Ω.1, Ω.2.preimage m⟩ (baseMap K B) x hx hxΩ w
    (fun a => (hw a).w) hwx (fun a => ∑ b, baseMap K B ((Matrix.of fun a b => ev x0 U.1 hU (Θ a b)) a b) *
      ((valR (w b) _ (M.g p₁ p₂).val).snd * valR x _ (M.g p₁ p₂)⁻¹.val))
  have hx₁ : ⊤ ≤ x ⁻¹ᵁ (M.U p₁ ⊓ (t.PP.L.pull m).U (fun _ => j i₁)) :=
    fun p hp => ⟨(hxW hp).1.2, Set.mem_iInter.2 fun _ => hWj i₁ (hΩ₁ (hxW hp).1.1)⟩
  have hx₂ : ⊤ ≤ x ⁻¹ᵁ (M.U p₂ ⊓ (t.PP.L.pull m).U (fun _ => j i₂)) :=
    fun p hp => ⟨(hxW hp).2.2, Set.mem_iInter.2 fun _ => hWj i₂ (hΩ₂ (hxW hp).2.1)⟩
  have hlog : ∀ b, (valR (w b) _ (M.g p₁ p₂).val).snd * valR x _ (M.g p₁ p₂)⁻¹.val =
      (valR (w b ≫ m) _ (t.PP.L.g (j i₁) (j i₂)).val).snd * valR (x ≫ m) _ (t.PP.L.g (j i₁) (j i₂))⁻¹.val +
      (dlogAt (baseMap K B) x (u b) (M.U p₁ ⊓ (t.PP.L.pull m).U (fun _ => j i₁)) (wg.s (p₁, fun _ => j i₁)) -
        dlogAt (baseMap K B) x (u b) (M.U p₂ ⊓ (t.PP.L.pull m).U (fun _ => j i₂)) (wg.s (p₂, fun _ => j i₂))) := by
    intro b
    unfold dlogAt
    rw [hwt]
    exact _root_.GlobalTheory.CechKS.dlog_transition_iso m t.PP.L M wg hwg (j i₁) (j i₂) p₁ p₂ x (w b) (hwx b) hx₁ hx₂
  have hxm : ⊤ ≤ (x ≫ m) ⁻¹ᵁ Ω.1 := hxΩ
  have hbase : (x ≫ m) ≫ t.G.hom = spMap ((baseMap K B).comp (ev x0 U.1 hU)) ≫ LogKS.chart U := by
    rw [Category.assoc, hm.1.w, ← Category.assoc, hx, GlobalTheory.Cris.spMap_comp (ev x0 U.1 hU), Category.assoc]
    exact congrArg _ (GlobalTheory.FlagMod.spMap_ev x0 U.2 hU).symm
  rw [_root_.GlobalTheory.CechKS.valR_sub_eq_eps_mul_of_affine hi.1.w hm'.1 him U hU' Ω ((e₁.trans hΩ₁).trans (hW₀ _)) x hxΩ S hS hSx l₁' l₂' k₁.1 k₂.1 k₁.2.1 k₂.2.1
    (fun f => ⟨_, k₂.2.2 f⟩) ?_ O hxO f, hSv _ hxO]
  · simp only [Finset.sum_mul]
  · intro f
    have hd := hdiff i₁ i₂ Ω.1 (le_inf (e₁.trans hΩ₁) (e₂.trans hΩ₂)) f B _ (x ≫ m) (fun a => w a ≫ m) hbase hxm
      (fun a => _root_.GlobalTheory.CechKS.IsTransl.isTranslate_comp t x0 A m hm _ (v a) (u a) (hu a) _ x hx (w a) (hw a))
    rw [valR_eq_ev _ _ hxm, map_sub, ← valR_eq_ev, ← valR_eq_ev] at hd
    rw [k₁.2.2, k₂.2.2, valR_comp_app S, hSv _ hxΩ]
    unfold chartVal
    simp only [← valR_comp_app, hwt, hlog]
    rw [add_sub_add_left_eq_sub, ← mul_sub, add_sub_add_comm, hd, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
    rw [← Finset.sum_mul, ← sub_mul, ← add_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine congrArg (· * _) (Finset.sum_congr rfl fun b _ => ?_)
    simp only [Matrix.of_apply, RingHom.comp_apply]
    ring

theorem isCechKS_of_isKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)), (∀ a, IsTanAtG t (LogKS.chart U) (v a)) → LogKS.IsKS t V U v D Θ → ∀ (K : Type) [Field K] (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1), ⊤ ≤ x0 ⁻¹ᵁ V → ∀ (y1 : Sp (DualNumber K) ⟶ X) (hU' : ⊤ ≤ y1 ⁻¹ᵁ U.1), (∀ r, ev y1 U.1 hU' r = TrivSqZeroExt.inl (ev x0 U.1 hU r) + TrivSqZeroExt.inr (ev x0 U.1 hU (D r))) → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (ι : A.left ⟶ t.G.left) (ι' : A'.left ⟶ t.G.left) (i : A.left ⟶ A'.left) (u : Fin n → (epsR K ⟶ A)), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A t.G x0 ι → IsGrpPullback A' t.G y1 ι' → i ≫ ι' = ι → (∀ a, (u a).left ≫ ι = spMap (dualMap (ev x0 U.1 hU)) ≫ v a) → ∀ (M : LB A.left), ⨆ k, M.U k = ⊤ → LBIso (t.PP.L.pull ι) M → GlobalTheory.CechKS.IsCechKS A A' i M u (Matrix.of fun a b => ev x0 U.1 hU (Θ a b)) := by
  intro E _ _ _ H X t V U n v D Θ hv hKS K _ x0 hU hV y1 hU' hy1 A _ A' _ ι ι' i u hi hι hι' hιι' hu M hM hiso
  obtain ⟨J₀, W₀, j, d, hcov, hWj, hfield, hlift, hdiff⟩ := hKS
  obtain ⟨wg, hwg⟩ := hiso
  have hW₀ : ∀ k, W₀ k ≤ t.G.hom ⁻¹ᵁ U.1 := fun k p hp => by
    have : p ∈ t.G.hom ⁻¹ᵁ (U.1 ⊓ V) := hcov ▸ (le_iSup W₀ k) hp
    exact this.1
  let θ : Matrix (Fin n) (Fin n) K := Matrix.of fun a b => ev x0 U.1 hU (Θ a b)
  let lam : ∀ (_ : Σ k : J₀, {Ω : t.G.left.affineOpens // Ω.1 ≤ W₀ k} × M.ι) (B : Type) [CommRing B]
      [Algebra (DualNumber K) B], (Sp B ⟶ A.left) → (Sp B ⟶ A'.left) :=
    fun k B _ _ x => chartPt A' i ι ι' k.2.1.1.1 (d k.1 k.2.1.1.1) u θ
      (M.U k.2.2 ⊓ (t.PP.L.pull ι).U (fun _ => j k.1)) (wg.s (k.2.2, fun _ => j k.1)) x
  have hex : ∀ (k : Σ k : J₀, {Ω : t.G.left.affineOpens // Ω.1 ≤ W₀ k} × M.ι) (B : Type) [CommRing B]
      [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left), x ≫ A.hom = spMap (baseMap K B) →
      ⊤ ≤ x ⁻¹ᵁ (ι ⁻¹ᵁ k.2.1.1.1) →
      IsChartPt A' ι ι' k.2.1.1.1 (d k.1 k.2.1.1.1) u θ (M.U k.2.2 ⊓ (t.PP.L.pull ι).U (fun _ => j k.1))
        (wg.s (k.2.2, fun _ => j k.1)) x (lam k B x) := by
    intro k B _ _ x hx hxΩ
    exact isChartPt_chartPt _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.CechKS.exists_isChartPt t U v D hv (W₀ k.1) (hW₀ k.1) (d k.1)
      (hfield k.1) (hlift k.1 (hW₀ k.1)) x0 hU y1 hU' hy1 A A' ι ι' u hι hι' hu k.2.1.1 k.2.1.2 θ _ _ B x hx hxΩ)
  refine ⟨Σ k : J₀, {Ω : t.G.left.affineOpens // Ω.1 ≤ W₀ k} × M.ι, fun k => ι ⁻¹ᵁ k.2.1.1.1 ⊓ M.U k.2.2,
    fun k => k.2.2, lam, ?_, fun k => inf_le_right, ?_, ?_⟩
  · refine eq_top_iff.2 fun a _ => ?_
    have h1 : (ι ≫ t.G.hom).base a ∈ U.1 ⊓ V := by
      rw [hι.1.w]
      exact ⟨hU (Set.mem_univ (A.hom.base a)), hV (Set.mem_univ (A.hom.base a))⟩
    have h2 : ι.base a ∈ ⨆ k, W₀ k := by
      rw [hcov]
      exact h1
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h2
    obtain ⟨Ω, hΩB, haΩ, hΩk⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 t.G.left.isBasis_affineOpens hk
    have h3 : a ∈ ⨆ p, M.U p := by
      rw [hM]
      trivial
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 h3
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨k, ⟨⟨Ω, hΩB⟩, hΩk⟩, p⟩, haΩ, hp⟩
  · intro k B _ _ x hx hxW
    have hxΩ : ⊤ ≤ x ⁻¹ᵁ (ι ⁻¹ᵁ k.2.1.1.1) := fun p hp => (hxW hp).1
    have hP := hex k B x hx hxΩ
    refine ⟨hP.1, _root_.GlobalTheory.CechKS.chartPt_red hi hι'.1 hιι' hx hxΩ hP, fun B' _ _ ρ => ?_⟩
    have hx' : (spMap (ρ : B →+* B') ≫ x) ≫ A.hom = spMap (baseMap K B') := by
      rw [Category.assoc, hx]
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, AlgHom.comp_algebraMap]
    have hxΩ' : ⊤ ≤ (spMap (ρ : B →+* B') ≫ x) ⁻¹ᵁ (ι ⁻¹ᵁ k.2.1.1.1) :=
      fun p _ => hxΩ (Set.mem_univ ((spMap (ρ : B →+* B')).base p))
    have hxWo : ⊤ ≤ x ⁻¹ᵁ (M.U k.2.2 ⊓ (t.PP.L.pull ι).U (fun _ => j k.1)) :=
      fun p hp => ⟨(hxW hp).2, Set.mem_iInter.2 fun _ => hWj k.1 (k.2.1.2 (hxW hp).1)⟩
    exact (_root_.GlobalTheory.CechKS.isChartPt_spMap hx hxΩ hxWo (GlobalTheory.T.isTangent_of_fibre_pullback_tangent_at_chart t U v hv x0 hU A ι u hι hu) hP B' ρ).unique hι'.1 (hex k B' _ hx' hxΩ')
  · intro k k' B _ _ x O f w hx hxW hxO hw
    have h₁ : ⊤ ≤ x ⁻¹ᵁ (ι ⁻¹ᵁ k.2.1.1.1) := fun p hp => (hxW hp).1.1
    have h₂ : ⊤ ≤ x ⁻¹ᵁ (ι ⁻¹ᵁ k'.2.1.1.1) := fun p hp => (hxW hp).2.1
    exact chartPt_sub t V U v D Θ hv J₀ W₀ j d hcov hWj hfield hlift hdiff x0 hU y1 hU' hy1 A A' ι ι' i u hi hι
      hι' hιι' hu M wg hwg k.1 k'.1 k.2.1.1 k'.2.1.1 k.2.1.2 k'.2.1.2 k.2.2 k'.2.2 B x O f w hx hxW hxO hw _ _
      (hex k B x hx h₁) (hex k' B x hx h₂)

end GlobalTheory.CechKS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLineBundlePullTrivialOfPointwiseGenerator
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PtExt

theorem triv_pull_of_isPtGen : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (L : LB X.left), L.IsLB →
    ∀ (q : Y ⟶ X) (t : ∀ (E : Type) [CommRing E] [Algebra R E], Pt Y E → L.ι → E), IsPtGen L q t →
    GlobalTheory.AbLaw.Triv (L.pull q.left) := by
  intro R _ X Y L _ q t ht
  unfold IsPtGen at ht
  obtain ⟨hu, hn, hg⟩ := ht
  have hmul : ∀ {D : Type} [CommRing D] (x : Sp D ⟶ Y.left) (U : Y.left.Opens), ⊤ ≤ x ⁻¹ᵁ U →
      ∀ a b : Γ(Y.left, U), evU x U (a * b) = evU x U a * evU x U b := by
    intro D _ x U h a b; unfold evU; rw [dite_eq_left h, dite_eq_left h, dite_eq_left h, map_mul]
  have hone : ∀ {D : Type} [CommRing D] (x : Sp D ⟶ Y.left) (U : Y.left.Opens), ⊤ ≤ x ⁻¹ᵁ U →
      evU x U (1 : Γ(Y.left, U)) = 1 := by
    intro D _ x U h; unfold evU; rw [dite_eq_left h, map_one]
  have hch : ∀ (j : PUnit → L.ι) {E : Type} [CommRing E] [Algebra R E] (z : Pt Y E),
      ⊤ ≤ z.left ⁻¹ᵁ (L.pull q.left).U j → ⊤ ≤ (z ≫ q).left ⁻¹ᵁ L.U (j PUnit.unit) :=
    fun j E _ _ z h p hp ↦ LB.wchart_le L (K := PUnit) (fun _ ↦ q.left) j PUnit.unit (h hp)
  have huniq : ∀ (U : Y.left.Opens) (f : Fn0 Y), (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E']
      [Algebra R E'] (ψ : E →ₐ[R] E') (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U → f E' (spOver ψ ≫ z) = ψ (f E z)) →
      ∀ c c' : Γ(Y.left, U), (∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U →
        evU z.left U c = f E z) → (∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U →
        evU z.left U c' = f E z) → c = c' :=
    fun U f hf c c' hc hc' ↦ (GlobalTheory.T.exists_unique_section_of_natural_pointwise_function R Y U f hf).unique hc hc'
  have hnat : ∀ j : PUnit → L.ι, ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : E →ₐ[R] E') (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ (L.pull q.left).U j →
      t E' (spOver ψ ≫ z) (j PUnit.unit) = ψ (t E z (j PUnit.unit)) :=
    fun j E _ _ E' _ _ ψ z h ↦ hn E E' ψ z _ (hch j z h)
  have hnatI : ∀ j : PUnit → L.ι, ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : E →ₐ[R] E') (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ (L.pull q.left).U j →
      Ring.inverse (t E' (spOver ψ ≫ z) (j PUnit.unit)) = ψ (Ring.inverse (t E z (j PUnit.unit))) := by
    intro j E _ _ E' _ _ ψ z h
    rw [hnat j E E' ψ z h]
    obtain ⟨u, hu'⟩ := hu E z _ (hch j z h)
    rw [← hu', Ring.inverse_unit]
    have e : ψ (u : E) = ((Units.map (ψ : E →* E') u : E'ˣ) : E') := rfl
    rw [e, Ring.inverse_unit]
    rfl
  have ex := fun j : PUnit → L.ι ↦
    (GlobalTheory.T.exists_unique_section_of_natural_pointwise_function R Y ((L.pull q.left).U j) (fun E _ _ z ↦ t E z (j PUnit.unit)) (hnat j)).exists
  have exI := fun j : PUnit → L.ι ↦
    (GlobalTheory.T.exists_unique_section_of_natural_pointwise_function R Y ((L.pull q.left).U j) (fun E _ _ z ↦ Ring.inverse (t E z (j PUnit.unit))) (hnatI j)).exists
  choose a ha using ex
  choose b hb using exI
  have hab : ∀ j, a j * b j = 1 := by
    intro j
    refine huniq _ (fun _ _ _ _ ↦ 1) (fun E _ _ E' _ _ ψ z _ ↦ (map_one ψ).symm) _ _ ?_ ?_
    · intro E _ _ z h
      rw [hmul _ _ h, ha j E z h, hb j E z h]
      exact Ring.mul_inverse_cancel _ (hu E z _ (hch j z h))
    · intro E _ _ z h
      exact hone _ _ h
  refine ⟨⟨fun j ↦ ⟨a j, b j, hab j, by rw [mul_comm]; exact hab j⟩⟩, ?_⟩
  intro i j
  apply Units.ext
  have hVi : (L.pull q.left).U i ⊓ (L.pull q.left).U j ≤ (L.pull q.left).U i := inf_le_left
  have hVj : (L.pull q.left).U i ⊓ (L.pull q.left).U j ≤ (L.pull q.left).U j := inf_le_right
  refine huniq ((L.pull q.left).U i ⊓ (L.pull q.left).U j) (fun E _ _ z ↦ t E z (i PUnit.unit))
    (fun E _ _ E' _ _ ψ z h ↦ hnat i E E' ψ z (fun p hp ↦ hVi (h hp))) _ _ ?_ ?_
  · intro E _ _ z h
    have e1 := evalSectionAtPointOrZero_restriction Y.left E z.left _ _ hVi (a i) h
    refine Eq.trans ?_ ((e1.trans (ha i E z (fun p hp ↦ hVi (h hp)))))
    rfl
  · intro E _ _ z h
    have hzi : ⊤ ≤ z.left ⁻¹ᵁ (L.pull q.left).U i := fun p hp ↦ hVi (h hp)
    have hzj : ⊤ ≤ z.left ⁻¹ᵁ (L.pull q.left).U j := fun p hp ↦ hVj (h hp)
    have hij : ⊤ ≤ (z.left ≫ q.left) ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
      fun p hp ↦ ⟨hch i z hzi hp, hch j z hzj hp⟩
    rw [Units.val_mul, hmul _ _ h]
    have e2 := evalSectionAtPointOrZero_restriction Y.left E z.left _ _ hVj (a j) h
    have e2' : evU z.left _ (ReciprocityTheory.ChartRestriction.G.Semi.res hVj (⟨a j, b j, hab j, by rw [mul_comm]; exact hab j⟩ :
        Γ(Y.left, (L.pull q.left).U j)ˣ)).val = t E z (j PUnit.unit) :=
      e2.trans (ha j E z hzj)
    have e3 : evU z.left _ ((L.pull q.left).g i j).val =
        evU (z ≫ q).left (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) (L.g (i PUnit.unit) (j PUnit.unit)).val := by
      unfold evU
      rw [dite_eq_left h]
      have hij' : ⊤ ≤ (z ≫ q).left ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) := hij
      rw [dite_eq_left hij']
      exact (evalAt_pull_g L q.left z.left i j hij h).symm
    rw [e3, e2']
    exact (hg E z (i PUnit.unit) (j PUnit.unit) (hch i z hzi) (hch j z hzj)).symm

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShortSeriesTranslateFrameConstantMultiple
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section
namespace GlobalTheory.HeartFrame

theorem splitOffBad_of_mul {D : D7} (V : HSp D) (a b : ℕ) (h : GA D V) (hs : SplitOffBad V (a * b) h) : SplitOffBad V a h := by
  obtain ⟨h1, e, P, h2, h3, h4⟩ := hs
  refine ⟨h1, e, P, h2, fun PP hPP ha => h3 PP hPP ?_, h4⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ ha


set_option maxHeartbeats 2000000 in
theorem central_short_series_frame : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∀ (cc : (T.J.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ka : ℂ) (δ : ℤˣ) (c0 : ℂ), GlobalTheory.AdTh.CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.J.U ((i : ℕ) + 1) (O i).s0) (O i).dict (O i).mu (T.J.x₀ ((i : ℕ) + 1) (O i).s0) (R.ωP i A.μ0) (R.vacP i) cc → GlobalTheory.PtId.IoAt (O i) (v₀ i (sg0 D A)) ka → GlobalTheory.PtId.ClsAt R i (iotaW T.J i) δ → GlobalTheory.PtId.CovAt (O i) c0 → ‖ka‖ = 1 → ‖c0‖ = 1 → ∀ z ∈ Subgroup.center G, ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ((w ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → ∀ F₀ : (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i), IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x₀ P ((F₀).1 : T.R ((i : ℕ) + 1)) → ∀ g : GA D (Wc D i), (lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * (O i).phi ((ka * (-((δ : ℤ) : ℂ)) ^ GlobalTheory.PtId.degW (T.J.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) * c0⁻¹) • cc) (actLev T.J.toCore.Q.c (O i).lev2 z⁻¹ ((F₀).1 : T.R ((i : ℕ) + 1))) g = D.what₂.embLL c * singleSeries R i ω φ' h ((O i).c0' y) w g := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hOP hβ hU hIo hRow hPh hSp v hv hmu hQ hF0 hV hdel hMb hRun ℓ hLP hAP χ ξR ω φ hK Λ h hSB hLa N x₀ P y hUm hTb hTd hLev hAdm hPh' hio cc ka δ c0 hcc hka hδ hcov hka1 hc01 z hz
  obtain ⟨x', ε, hx', hε, hmv⟩ := GlobalTheory.CentralLevelMove.short_central_move D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP hU hIo hRow hPh hSp v hv hmu hQ hF0 hV hdel hMb hRun ℓ hLP hAP χ ξR ω φ hK Λ h (splitOffBad_of_mul _ _ _ _ hSB) hLa N x₀ P y hUm hTb hTd hLev hAdm hPh' hio cc ka δ c0 hcc hka hδ hcov hka1 hc01 z hz
  obtain ⟨h0L, m0, hm0, h0⟩ := GlobalTheory.AdTh.CoverRoot.covAt_base_root D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP c0 hcov
  obtain ⟨c0', h1L, ⟨m1, hm1, h1⟩, hcT⟩ := GlobalTheory.OnCmp.CoverRoot.cover_value_root D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP v hF0 hdel hRun χ hK.chr
  have hrat : c0' * c0⁻¹ ∈ D.what₂.embLL.range := by
    obtain ⟨a, ha⟩ := h1L
    obtain ⟨b, hb⟩ := h0L
    exact ⟨a * b⁻¹, by rw [map_mul, map_inv₀, ha, hb]⟩
  have hroot : (c0' * c0⁻¹) ^ (m1 * m0) = 1 := by
    rw [mul_pow, inv_pow, pow_mul, h1, one_pow, mul_comm m1, pow_mul, h0]
    simp
  obtain ⟨y₀, c, hrk, hint, hmain⟩ := GlobalTheory.FrameShort.short_at_frame D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP hβ hU hIo hRow hPh hSp v hv hmu hQ hF0 hV hdel hMb hRun ℓ hLP hAP χ ξR ω φ hK Λ h hSB hLa N x' P y hUm hTb hTd hLev hx' hPh' hio cc ka δ c0 hcc hka hδ hcov hka1 hc01 c0' hrat ⟨m1 * m0, Nat.mul_pos hm1 hm0, hroot⟩ hcT
  refine ⟨y₀, ε * c, hrk, fun lam hlam => ?_, fun φ' hφ' w hw F₀ hF₀ g => ?_⟩
  · obtain ⟨s, hs, hsi⟩ := hint lam hlam
    refine ⟨s, hs, ?_⟩
    rw [mul_left_comm]
    exact hε.mul hsi
  obtain ⟨F₁, hF₁, he⟩ := hmv F₀ hF₀
  have e3 := hmain φ' hφ' w hw F₁ hF₁ g
  rw [he, map_mul]
  linear_combination (D.what₂.embLL ε) * e3

end GlobalTheory.HeartFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueIsIntegralOfIntegralAtPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem intElem_pow_mul_of_away {R S Rt St : Type} [CommRing R] [CommRing S] [CommRing Rt] [CommRing St]
    (f : R →+* S) (t : R) [Algebra R Rt] [Algebra S St] [IsLocalization.Away t Rt]
    [IsLocalization.Away (f t) St] (ft : Rt →+* St)
    (hc : ft.comp (algebraMap R Rt) = (algebraMap S St).comp f) (x : S)
    (hx : ft.IsIntegralElem (algebraMap S St x)) : ∃ n : ℕ, f.IsIntegralElem (f t ^ n * x) := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra Rt St := ft.toAlgebra
  letI : Algebra R St := ((algebraMap S St).comp f).toAlgebra
  haveI : IsScalarTower R Rt St := IsScalarTower.of_algebraMap_eq' hc.symm
  haveI : IsScalarTower R S St := IsScalarTower.of_algebraMap_eq' rfl
  have hx' : IsIntegral Rt (algebraMap S St x) := hx
  obtain ⟨⟨_, a, rfl⟩, ha⟩ := hx'.exists_multiple_integral_of_isLocalization (Submonoid.powers t)
  have e : (⟨t ^ a, a, rfl⟩ : Submonoid.powers t) • algebraMap S St x =
      algebraMap S St (f t ^ a * x) := by
    rw [Submonoid.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply R S St, ← map_mul]
    simp [RingHom.algebraMap_toAlgebra]
  rw [e] at ha
  have hr : IsIntegral R (f t) := f.isIntegralElem_map
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_algebraMap (R := R) (Sₘ := St) hr ha
  exact ⟨n + a, by rw [pow_add, _root_.mul_assoc]; exact hn⟩

theorem isIntegralElem_of_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) {y : C} (h : (g.comp f).IsIntegralElem y) : g.IsIntegralElem y := by
  obtain ⟨p, hp, h⟩ := h
  exact ⟨p.map f, hp.map f, by rw [Polynomial.eval₂_map]; exact h⟩

theorem res_res_sections {Y : Scheme.{0}} {U V V' : Y.Opens} (h1 : V ≤ U) (h2 : V' ≤ V) (z : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom z) =
      (Y.presheaf.map (homOfLE (h2.trans h1)).op).hom z := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem chartVal_isIntegral_of_intAt : ∀ {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k)
    (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → IsAffineOpen (α ⁻¹ᵁ W) →
    (∀ x ∈ W, IntAt L α s x) → (α.app W).hom.IsIntegralElem (chartVal L α s j W hW) := by
  intro X Y L α k s j W hW hWa hYa hint
  letI : Algebra Γ(X, W) Γ(Y, α ⁻¹ᵁ W) := (α.app W).hom.toAlgebra
  set F := chartVal L α s j W hW with hF
  have loc : ∀ x ∈ W, ∃ d : Γ(X, W), x ∈ X.basicOpen d ∧
      ∃ n : ℕ, (α.app W).hom.IsIntegralElem ((α.app W).hom d ^ n * F) := by
    intro x hx
    obtain ⟨j', W', hW', hxW', hW'a, hint'⟩ := hint x hx
    obtain ⟨d, hdle, hxd⟩ := hWa.exists_basicOpen_le (V := W ⊓ W') ⟨x, ⟨hx, hxW'⟩⟩ hx
    refine ⟨d, hxd, ?_⟩
    set r : Γ(Y, α ⁻¹ᵁ W) := (α.app W).hom d with hr
    have hED : Y.basicOpen r ≤ α ⁻¹ᵁ X.basicOpen d := (Scheme.preimage_basicOpen α d).ge
    haveI := hWa.isLocalization_basicOpen d
    haveI := hYa.isLocalization_basicOpen r
    have hDW : X.basicOpen d ≤ W := X.basicOpen_le d
    have hDW' : X.basicOpen d ≤ W' := hdle.trans inf_le_right
    have hEW : Y.basicOpen r ≤ α ⁻¹ᵁ W := Y.basicOpen_le r
    have hEW' : Y.basicOpen r ≤ α ⁻¹ᵁ W' := hED.trans (fun y hy => hDW' hy)
    have hDjj : X.basicOpen d ≤ L.U j ⊓ L.U j' := le_inf (hDW.trans hW) (hDW'.trans hW')
    let LC := LB.LinComb L (K := Fin 1) (fun _ => α) (fun _ => (k : ℤ))
    have hEJ : Y.basicOpen r ≤ LC.U (fun _ => j) ⊓ LC.U (fun _ => j') :=
      le_inf (hEW.trans (locInt_le_chart L α j W hW)) (hEW'.trans (locInt_le_chart L α j' W' hW'))
    refine intElem_pow_mul_of_away (α.app W).hom d (Rt := Γ(X, X.basicOpen d))
      (St := Γ(Y, Y.basicOpen r)) (α.appLE _ _ hED).hom ?_ F ?_
    · show (α.appLE _ _ hED).hom.comp (X.presheaf.map (homOfLE hDW).op).hom =
        (Y.presheaf.map (homOfLE hEW).op).hom.comp (α.app W).hom
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]; rfl
    · have hc0 := congrArg (Y.presheaf.map (homOfLE hEJ).op).hom (s.compat (fun _ => j) (fun _ => j'))
      rw [map_mul] at hc0
      show (α.appLE _ _ hED).hom.IsIntegralElem ((Y.presheaf.map (homOfLE hEW).op).hom F)
      have eF : (Y.presheaf.map (homOfLE hEW).op).hom F = (Y.presheaf.map (homOfLE hEJ).op).hom
          ((Y.presheaf.map (homOfLE (inf_le_left : LC.U (fun _ => j) ⊓ LC.U (fun _ => j') ≤ LC.U (fun _ => j))).op).hom
            (s.f (fun _ => j))) :=
        (res_res_sections _ _ _).trans (res_res_sections _ _ _).symm
      rw [eF, hc0]
      refine RingHom.IsIntegralElem.mul _ ?_ ?_
      · have h'' : LC.U (fun _ => j) ⊓ LC.U (fun _ => j') ≤ α ⁻¹ᵁ (L.U j ⊓ L.U j') :=
          le_inf (inf_le_left.trans (LB.wchart_le L _ _ 0)) (inf_le_right.trans (LB.wchart_le L _ _ 0))
        have hg : ((LC.g (fun _ => j) (fun _ => j') : Γ(Y, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))ˣ) :
            Γ(Y, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))) = ((Y.presheaf.map (homOfLE h'').op).hom
              ((α.app (L.U j ⊓ L.U j')).hom (L.g j j' : Γ(X, L.U j ⊓ L.U j')))) ^ k := by
          change ((∏ _i : Fin 1, (ReciprocityTheory.ChartRestriction.G.Semi.res h''
            (ReciprocityTheory.ChartRestriction.G.Semi.pullU α (L.U j ⊓ L.U j') (L.g j j'))) ^ (k : ℤ) :
              Γ(Y, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))ˣ) : Γ(Y, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))) = _
          rw [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
          rfl
        have hz : (Y.presheaf.map (homOfLE hEJ).op).hom ((Y.presheaf.map (homOfLE h'').op).hom
              ((α.app (L.U j ⊓ L.U j')).hom (L.g j j' : Γ(X, L.U j ⊓ L.U j')))) =
            (α.appLE _ _ hED).hom ((X.presheaf.map (homOfLE hDjj).op).hom (L.g j j' : Γ(X, L.U j ⊓ L.U j'))) := by
          refine (res_res_sections _ _ _).trans ?_
          have := congrArg (fun φ => (CommRingCat.Hom.hom φ) (L.g j j' : Γ(X, L.U j ⊓ L.U j')))
            (Scheme.Hom.map_appLE (f := α) hED (homOfLE hDjj).op)
          exact this.symm
        rw [hg, map_pow, hz, ← map_pow]
        exact RingHom.isIntegralElem_map _
      · have h1 := hint'.map (Y.presheaf.map (homOfLE hEW').op).hom
        have e1 : (Y.presheaf.map (homOfLE hEW').op).hom.comp (α.app W').hom =
            (α.appLE _ _ hED).hom.comp (X.presheaf.map (homOfLE hDW').op).hom := by
          rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]; rfl
        rw [e1] at h1
        have h2 := isIntegralElem_of_comp _ _ h1
        convert h2 using 1
        exact (res_res_sections _ _ _).trans (res_res_sections _ _ _).symm
  change F ∈ (integralClosure Γ(X, W) Γ(Y, α ⁻¹ᵁ W)).toSubmodule
  let S0 : Set Γ(X, W) := {d | ∃ n : ℕ, (α.app W).hom.IsIntegralElem ((α.app W).hom d ^ n * F)}
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ S0 ?_ F ?_
  · rw [← hWa.iSup_basicOpen_eq_self_iff]
    apply le_antisymm
    · exact iSup_le fun d => X.basicOpen_le _
    · intro x hx
      obtain ⟨d, hxd, hd⟩ := loc x hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨d, hd⟩, hxd⟩
  · rintro ⟨d, n, hn⟩
    refine ⟨n, ?_⟩
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_pow]
    exact hn

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartCombinationPower
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open GlobalTheory.Points GlobalTheory.HermFrame
open scoped Classical

namespace GlobalTheory.ChernTop

variable {n : ℕ}

def rowForm (a : Fin n) : (Fin n → ℂ) →ₗ[ℂ] Ev n := Fintype.linearCombination ℂ fun b => sym (a, b)

def matForm (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Ev n where
  toFun H := kappa • ∑ a, rowForm a (H a)
  map_add' H H' := by
    rw [← smul_add, ← Finset.sum_add_distrib]
    exact congrArg _ (Finset.sum_congr rfl fun a _ => map_add _ _ _)
  map_smul' c H := by
    rw [RingHom.id_apply, smul_comm, Finset.smul_sum (r := c)]
    exact congrArg _ (Finset.sum_congr rfl fun a _ => map_smul (rowForm a) c (H a))

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} {σ : k →+* ℂ}

variable {c : AlgChart p σ D} {y : CxPts p σ}

end GlobalTheory.ChernTop
end
end

