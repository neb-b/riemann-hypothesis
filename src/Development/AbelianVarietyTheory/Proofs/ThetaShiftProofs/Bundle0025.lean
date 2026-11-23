module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SectionsEquivAnArcTheta
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermMemConvLaurent
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcSectionValue

section General

variable {A B K : Type} [CommRing A] [CommRing B] [CommRing K] {Z : Scheme.{0}}

theorem spMap_cancel {ρ : A →+* B} (hρ : Function.Injective ρ) {f g : Sp A ⟶ Sp K}
    (h : spMap ρ ≫ f = spMap ρ ≫ g) : f = g := by
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [spMap, ← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  congr 1
  ext a
  exact hρ (congrArg (fun q => q.hom a) h')

theorem valR_const (p : Z ⟶ Sp K) (f : K →+* A) (q : Sp A ⟶ Z) (hq : q ≫ p = spMap f) (U : Z.Opens)
    (h : ⊤ ≤ q ⁻¹ᵁ U) (a : K) : valR q U (constFn p U a) = f a := by
  refine (HolHom.valR_appLE q p ⊤ U le_top _ h).trans ?_
  rw [hq]
  exact Conv.valR_spMap_top f a

theorem exists_chart_local [IsLocalRing A] (x : Sp A ⟶ Z) {L : LB Z} (hL : L.IsLB) : ∃ j, ⊤ ≤ x ⁻¹ᵁ L.U j := by
  have : x (IsLocalRing.closedPoint A) ∈ ⨆ j, L.U j := hL.cover ▸ trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  exact ⟨j, ((IsLocalRing.closedPoint_mem_iff (x ⁻¹ᵁ L.U j)).1 hj).ge⟩

theorem le_div_iff {Z' : Scheme.{0}} (x : Sp A ⟶ Z') (φ : Z' ⟶ Z) (L : LB Z) (M : LB Z') (j : L.ι) (k : M.ι) :
    ⊤ ≤ x ⁻¹ᵁ (LB.div (L.pull φ) M).U (fun _ => j, k) ↔ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U j ∧ ⊤ ≤ x ⁻¹ᵁ M.U k :=
  ⟨fun h => ⟨fun _ hz => Set.mem_iInter.1 (h hz).1 PUnit.unit, fun _ hz => (h hz).2⟩,
    fun h _ hz => ⟨Set.mem_iInter.2 fun _ => h.1 hz, h.2 hz⟩⟩

theorem exists_rigIso_of_eq {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) {L₁ L₂ : RigLB G'} (h : L₁ = L₂) (L : RigLB G)
    (w : LB.Iso L₁.L (L.L.pull m.F)) (hw : IsRigIso m L₁ L w) (k₁ : L₁.L.ι) :
    ∃ (w' : LB.Iso L₂.L (L.L.pull m.F)) (k₂ : L₂.L.ι), IsRigIso m L₂ L w' ∧ HEq k₁ k₂ ∧ L₁.L.U k₁ = L₂.L.U k₂ ∧
      ∀ (x : Sp A ⟶ G'.left) (j : L.L.ι),
        valR x _ (w.s (fun _ => j, k₁)).val = valR x _ (w'.s (fun _ => j, k₂)).val := by
  subst h
  exact ⟨w, k₁, hw, HEq.rfl, rfl, fun _ _ => rfl⟩

end General

section Germ

variable (Γ : Germs) (w : ℂ)

theorem isLocalRing_germ : IsLocalRing (Γ.R w) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    by_cases h : Γ.ev w a = 0
    · exact Or.inr (Γ.unit w _ (by simp [h]))
    · exact Or.inl (Γ.unit w _ h)

theorem germ_mem_convLaurent (f : Γ.R w) : (f : ℂ⸨X⸩) ∈ Conv.convLaurent := by
  obtain ⟨T, hw, a, s, hs, h⟩ := Γ.frac w f
  have hs' : (s : ℂ⸨X⸩) ≠ 0 := fun e => hs (by rw [show s = 0 from Subtype.ext e, map_zero])
  have : (f : ℂ⸨X⸩) = a / s := by rw [← h]; field_simp
  rw [this]
  exact div_mem (Conv.halfRing_le_convLaurent T a.2) (Conv.halfRing_le_convLaurent T s.2)

theorem le_of_ev {Z : Scheme.{0}} (x : Sp (Γ.R w) ⟶ Z) {U : Z.Opens}
    (h : ⊤ ≤ (spMap (Γ.ev w).toRingHom ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  haveI := isLocalRing_germ Γ w
  haveI : IsLocalHom (Γ.ev w).toRingHom := ⟨fun a ha => Γ.unit w a ha.ne_zero⟩
  refine ((IsLocalRing.closedPoint_mem_iff (x ⁻¹ᵁ U)).1 ?_).ge
  have := h (x := IsLocalRing.closedPoint ℂ) trivial
  rw [← IsLocalRing.comap_closedPoint (Γ.ev w).toRingHom]
  exact this

end Germ

theorem exists_le_halfPlane {Z : Scheme.{0}} {T : ℝ} (yT : Sp (Conv.halfRing T) ⟶ Z) {U : Z.Opens}
    (hU : ⊤ ≤ (spMap (Conv.halfRing T).val.toRingHom ≫ yT) ⁻¹ᵁ U) :
    ∃ (T' : ℝ) (h : T ≤ T'), ⊤ ≤ (spMap (Subalgebra.inclusion (Conv.halfRing_mono h) :
      Conv.halfRing T →+* Conv.halfRing T') ≫ yT) ⁻¹ᵁ U := by
  have hfac : spMap (Conv.halfRing T).val.toRingHom ≫ yT =
      spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) ≫
        (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT) := by
    rw [← Category.assoc, ← spMap_comp]
    rfl
  refine Conv.exists_le_preimage_inclusion yT fun p _ => ?_
  rw [hfac] at hU
  obtain rfl : p = spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) (default : PrimeSpectrum ℂ⸨X⸩) :=
    Subsingleton.elim (α := PrimeSpectrum Conv.convLaurent) _ _
  exact hU (x := (default : PrimeSpectrum ℂ⸨X⸩)) trivial

theorem exists_fsum_ne_zero {O : Type} [CommRing O] [StarRing O] (A : AnArc O) {θ : (Fin A.gB → ℂ) → ℂ} (h : θ ≠ 0) :
    ∃ v, A.FSum 1 0 θ v ≠ 0 := by
  obtain ⟨z, hz⟩ := Function.ne_iff.1 h
  refine ⟨(0, z), fun e => hz ?_⟩
  have hl : A.level 1 0 0 = {0} := by
    ext m
    rw [AnArc.mem_level, Finset.mem_singleton]
    have h2 := A.two_mul_exponent 1 0 m
    refine ⟨fun h0 => by_contra fun hm => ?_, fun h0 => by simp [h0, AnArc.exponent]⟩
    have := A.be_pos m hm
    simp [h0] at h2
    omega
  have := A.coeff_FSum 1 0 θ (0, z) 0
  rw [e, hl] at this
  simpa [AnArc.term] using this.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_germ_lift (Y : Model Xo c β) (bF : c.F →+* ℂ) {A : AnArc (𝓞 E)} {yF : Sp ℂ⸨X⸩ ⟶ Xo.XF c}
    (hover : yF ≫ pullback.snd _ _ = spMap ((algebraMap ℂ ℂ⸨X⸩).comp bF))
    (ΦF : GenPts A Y.oF.t yF) {Φ : GenPts A Xo.univ.t (yF ≫ pullback.fst _ _)}
    (hx : ∀ v, (ΦF.x v).left ≫ Y.m0.toSABMap.φ = (Φ.x v).left) {Γ : Germs} (Ψ : SpecPts Φ Γ)
    (U : (Xo.XF c).Opens) (hU : ⊤ ≤ yF ⁻¹ᵁ U) :
    ∃ T₁ : ℝ, ∀ w : ℂ, T₁ < w.im → ∃ hw : Ψ.T < w.im, ∀ v, ∃ xg : Sp (Γ.R w) ⟶ Y.oF.t.G.left,
      xg ≫ Y.m0.toSABMap.φ = (Ψ.xt w hw v).left ∧ spMap (Γ.R w).val.toRingHom ≫ xg = (ΦF.x v).left ∧
      ⊤ ≤ (xg ≫ Y.oF.t.G.hom) ⁻¹ᵁ U ∧
      ∀ x : Sp ℂ ⟶ Y.oF.t.G.left, x ≫ Y.m0.toSABMap.φ = (Ψ.pi w v).left →
        x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF → x = spMap (Γ.ev w).toRingHom ≫ xg := by
  have hb : spMap (Conv.halfRing Ψ.T).val.toRingHom ≫ spMap ((algebraMap ℂ (Conv.halfRing Ψ.T)).comp bF) =
      yF ≫ pullback.snd _ _ := by
    rw [hover, ← spMap_comp]; rfl
  have hs : Ψ.yT ≫ Xo.s = spMap ((algebraMap ℂ (Conv.halfRing Ψ.T)).comp bF) ≫
      spMap (IntermediateField.inclusion c.le).toRingHom := by
    refine spMap_cancel (ρ := (Conv.halfRing Ψ.T).val.toRingHom) Subtype.val_injective ?_
    rw [← Category.assoc, Ψ.yT_gen, ← Category.assoc, hb, Category.assoc, Category.assoc, pullback.condition]
  let yT : Sp (Conv.halfRing Ψ.T) ⟶ Xo.XF c := pullback.lift _ _ hs
  have h1 : yT ≫ pullback.fst _ _ = Ψ.yT := pullback.lift_fst _ _ _
  have h2 : yT ≫ pullback.snd _ _ = spMap ((algebraMap ℂ (Conv.halfRing Ψ.T)).comp bF) := pullback.lift_snd _ _ _
  have hg : spMap (Conv.halfRing Ψ.T).val.toRingHom ≫ yT = yF := by
    apply pullback.hom_ext
    · rw [Category.assoc, h1, Ψ.yT_gen]
    · rw [Category.assoc, h2, hb]
  obtain ⟨T₁, hT, hU₁⟩ := exists_le_halfPlane yT (hg ▸ hU)
  refine ⟨T₁, fun w hw₁ => ⟨hT.trans_lt hw₁, fun v => ?_⟩⟩
  set hw := hT.trans_lt hw₁
  have hP := Y.m0.cart.1
  have hc : (Ψ.xt w hw v).left ≫ Xo.univ.t.G.hom =
      (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ yT) ≫ pullback.fst _ _ := by
    rw [Category.assoc, h1]
    exact Over.w (Ψ.xt w hw v)
  have e1 := hP.lift_fst _ _ hc
  have e2 := hP.lift_snd _ _ hc
  refine ⟨hP.lift _ _ hc, e1, ?_, ?_, fun x hx1 hx2 => ?_⟩
  · apply hP.hom_ext
    · rw [Category.assoc, e1, Ψ.xt_gen]
      exact (hx v).symm
    · rw [Category.assoc, e2, ← Category.assoc, ← spMap_comp]
      exact hg.trans (Over.w (ΦF.x v)).symm
  · rw [e2]
    have : spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom =
        spMap (Subalgebra.inclusion (Γ.le T₁ w hw₁)).toRingHom ≫ spMap (Subalgebra.inclusion (Conv.halfRing_mono hT) :
          Conv.halfRing Ψ.T →+* Conv.halfRing T₁) := by
      rw [← spMap_comp]; rfl
    rw [this, Category.assoc]
    exact FormalValue.top_le_comp hU₁ _
  · have e3 : x ≫ Y.m0.toSABMap.φ = (spMap (Γ.ev w).toRingHom ≫ hP.lift _ _ hc) ≫ Y.m0.toSABMap.φ := by
      rw [hx1, Ψ.pi_eq w hw v, Category.assoc]
      exact congrArg _ e1.symm
    refine hP.hom_ext e3 (pullback.hom_ext ?_ ?_)
    · rw [Category.assoc, ← hP.w, ← Category.assoc, Category.assoc _ _ (pullback.fst _ _), ← hP.w, ← Category.assoc]
      exact congrArg (· ≫ Xo.univ.t.G.hom) e3
    · rw [Category.assoc, hx2, Category.assoc, Category.assoc, reassoc_of% e2, h2, ← spMap_comp, ← spMap_comp]
      congr 1
      ext a
      exact ((Γ.ev w).commutes (bF a)).symm

end GlobalTheory.ArcSectionValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermsSpec
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section
namespace GlobalTheory.GermRing
open GlobalTheory.Conv

def Rep (w : ℂ) (f : ℂ⸨X⸩) (x : ℂ) : Prop :=
  ∃ (T : ℝ) (hw : T < w.im) (a s : halfRing T),
    ev T w hw s ≠ 0 ∧ (s : ℂ⸨X⸩) * f = a ∧ ev T w hw a = x * ev T w hw s

theorem Rep.common {w : ℂ} {f g : ℂ⸨X⸩} {x y : ℂ} (hf : Rep w f x) (hg : Rep w g y) :
    ∃ (T : ℝ) (hw : T < w.im) (a s b t : halfRing T),
      (ev T w hw s ≠ 0 ∧ (s : ℂ⸨X⸩) * f = a ∧ ev T w hw a = x * ev T w hw s) ∧
      (ev T w hw t ≠ 0 ∧ (t : ℂ⸨X⸩) * g = b ∧ ev T w hw b = y * ev T w hw t) := by
  obtain ⟨T, hw, a, s, h⟩ := hf
  obtain ⟨T', hw', b, t, h'⟩ := hg
  exact ⟨max T T', max_lt hw hw', ⟨a, halfRing_mono (le_max_left _ _) a.2⟩,
    ⟨s, halfRing_mono (le_max_left _ _) s.2⟩, ⟨b, halfRing_mono (le_max_right _ _) b.2⟩,
    ⟨t, halfRing_mono (le_max_right _ _) t.2⟩, h, h'⟩

theorem Rep.unique {w : ℂ} {f : ℂ⸨X⸩} {x y : ℂ} (hx : Rep w f x) (hy : Rep w f y) : x = y := by
  obtain ⟨T, hw, a, s, b, t, ⟨h1, h2, h3⟩, k1, k2, k3⟩ := hx.common hy
  have e : a * t = b * s := Subtype.ext (by
    push_cast
    rw [← h2, ← k2]; ring)
  have e' := congrArg (ev T w hw) e
  rw [map_mul, map_mul, h3, k3] at e'
  apply mul_right_cancel₀ (mul_ne_zero h1 k1)
  linear_combination e'

theorem Rep.add {w : ℂ} {f g : ℂ⸨X⸩} {x y : ℂ} (hx : Rep w f x) (hy : Rep w g y) :
    Rep w (f + g) (x + y) := by
  obtain ⟨T, hw, a, s, b, t, ⟨h1, h2, h3⟩, k1, k2, k3⟩ := hx.common hy
  refine ⟨T, hw, a * t + b * s, s * t, by rw [map_mul]; exact mul_ne_zero h1 k1, ?_, ?_⟩
  · push_cast
    rw [← h2, ← k2]; ring
  · rw [map_add (f := _), map_mul, map_mul, map_mul, h3, k3]; ring

theorem Rep.mul {w : ℂ} {f g : ℂ⸨X⸩} {x y : ℂ} (hx : Rep w f x) (hy : Rep w g y) :
    Rep w (f * g) (x * y) := by
  obtain ⟨T, hw, a, s, b, t, ⟨h1, h2, h3⟩, k1, k2, k3⟩ := hx.common hy
  refine ⟨T, hw, a * b, s * t, by rw [map_mul]; exact mul_ne_zero h1 k1, ?_, ?_⟩
  · push_cast
    rw [← h2, ← k2]; ring
  · rw [map_mul, map_mul, h3, k3]; ring

theorem rep_of_mem {T : ℝ} {w : ℂ} (hw : T < w.im) (s : halfRing T) :
    Rep w (s : ℂ⸨X⸩) (ev T w hw s) :=
  ⟨T, hw, s, 1, by rw [map_one]; exact one_ne_zero, by simp, by rw [map_one, _root_.mul_one]⟩

theorem rep_algebraMap (w c : ℂ) : Rep w (algebraMap ℂ ℂ⸨X⸩ c) c := by
  have hw : w.im - 1 < w.im := sub_one_lt _
  have h := rep_of_mem hw (algebraMap ℂ (halfRing (w.im - 1)) c)
  rw [AlgHom.commutes] at h
  exact h

theorem Rep.inv {w : ℂ} {f : ℂ⸨X⸩} {x : ℂ} (hx : Rep w f x) (h0 : x ≠ 0) :
    ∃ g, Rep w g x⁻¹ ∧ f * g = 1 := by
  obtain ⟨T, hw, a, s, h1, h2, h3⟩ := hx
  have ha : ev T w hw a ≠ 0 := by rw [h3]; exact mul_ne_zero h0 h1
  have ha' : (a : ℂ⸨X⸩) ≠ 0 := fun h => ha (by rw [show a = 0 from Subtype.ext h, map_zero])
  have hf : f ≠ 0 := fun h => ha' (by rw [← h2, h, mul_zero])
  refine ⟨f⁻¹, ⟨T, hw, s, a, ha, ?_, ?_⟩, mul_inv_cancel₀ hf⟩
  · rw [← h2, _root_.mul_assoc, mul_inv_cancel₀ hf, _root_.mul_one]
  · rw [h3, ← _root_.mul_assoc, inv_mul_cancel₀ h0, _root_.one_mul]

def ring (w : ℂ) : Subalgebra ℂ ℂ⸨X⸩ where
  carrier := {f | ∃ x, Rep w f x}
  mul_mem' := fun ⟨_, hx⟩ ⟨_, hy⟩ => ⟨_, hx.mul hy⟩
  add_mem' := fun ⟨_, hx⟩ ⟨_, hy⟩ => ⟨_, hx.add hy⟩
  algebraMap_mem' c := ⟨c, rep_algebraMap w c⟩

def val (w : ℂ) (f : ring w) : ℂ := Classical.choose (show ∃ x, Rep w f x from f.2)

theorem rep_val (w : ℂ) (f : ring w) : Rep w f (val w f) := Classical.choose_spec (show ∃ x, Rep w f x from f.2)

def evRing (w : ℂ) : ring w →ₐ[ℂ] ℂ where
  toFun := val w
  map_one' := (rep_val w 1).unique (by simpa using rep_algebraMap w 1)
  map_mul' f g := (rep_val w (f * g)).unique ((rep_val w f).mul (rep_val w g))
  map_zero' := (rep_val w 0).unique (by simpa using rep_algebraMap w 0)
  map_add' f g := (rep_val w (f + g)).unique ((rep_val w f).add (rep_val w g))
  commutes' c := (rep_val w _).unique (rep_algebraMap w c)

def germs : Germs where
  R := ring
  ev := evRing
  unit w s hs := by
    obtain ⟨g, hg, h⟩ := (rep_val w s).inv hs
    exact IsUnit.of_mul_eq_one (⟨g, _, hg⟩ : ring w) (Subtype.ext h)
  le T w hw f hf := ⟨_, rep_of_mem hw ⟨f, hf⟩⟩
  ev_eq T w hw s := (rep_val w _).unique (rep_of_mem hw s)
  frac w f := by
    obtain ⟨T, hw, a, s, h1, h2, -⟩ := rep_val w f
    exact ⟨T, hw, a, s, h1, h2⟩

theorem germs_spec : Nonempty Germs ∧ ∀ (Γ : Germs) (w : ℂ), IsLocalRing (Γ.R w) ∧ (∀ f : Γ.R w, (f : ℂ⸨X⸩) ∈ Conv.convLaurent) ∧ ∀ (f : Γ.R w) (g : ℂ⸨X⸩), Γ.ev w f ≠ 0 → (f : ℂ⸨X⸩) * g ∈ Γ.R w → g ∈ Γ.R w := by
  refine ⟨⟨germs⟩, fun Γ w => ⟨?_, fun f => ?_, fun f g hf h => ?_⟩⟩
  · refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f => ?_
    by_cases h : Γ.ev w f = 0
    · exact Or.inr (Γ.unit w _ (by rw [map_sub, map_one, h, sub_zero]; exact one_ne_zero))
    · exact Or.inl (Γ.unit w _ h)
  · obtain ⟨T, hw, a, s, h1, h2⟩ := Γ.frac w f
    have hs : (s : ℂ⸨X⸩) ≠ 0 := fun h => h1 (by rw [show s = 0 from Subtype.ext h, map_zero])
    have e : (f : ℂ⸨X⸩) = (s : ℂ⸨X⸩)⁻¹ * a := by
      rw [← h2, ← _root_.mul_assoc, inv_mul_cancel₀ hs, _root_.one_mul]
    rw [e]
    exact mul_mem (convLaurent.inv_mem (halfRing_le_convLaurent T s.2)) (halfRing_le_convLaurent T a.2)
  · obtain ⟨k, hk⟩ := (Γ.unit w f hf).exists_left_inv
    have hk' : (k : ℂ⸨X⸩) * f = 1 := congrArg Subtype.val hk
    have e : g = k * (f * g) := by rw [← _root_.mul_assoc, hk', _root_.one_mul]
    rw [e]
    exact mul_mem k.2 h

end GlobalTheory.GermRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicCurve
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.HalfPoint

theorem holomorphic_curve : ∀ (Z : Scheme.{0}) (T : ℝ) (yT : Sp (Conv.halfRing T) ⟶ Z) (yw : ℂ → (Sp ℂ ⟶ Z)), (∀ w (hw : T < w.im), yw w = spMap (Conv.ev T w hw).toRingHom ≫ yT) → IsHolTo {w : ℂ | T < w.im} yw ∧ ∀ (U : Z.Opens), ⊤ ≤ (spMap (Conv.halfRing T).val.toRingHom ≫ yT) ⁻¹ᵁ U → (∃ T' ≥ T, ∀ (T'' : ℝ) (i : Conv.halfRing T →+* Conv.halfRing T''), T' ≤ T'' → (∀ r, (i r : ℂ⸨X⸩) = r) → ⊤ ≤ (spMap i ≫ yT) ⁻¹ᵁ U) ∧ ∀ f : Γ(Z, U), ∃ T' ≥ T, ∃ h : valR (spMap (Conv.halfRing T).val.toRingHom ≫ yT) U f ∈ Conv.halfRing T', ∀ w (hw : T' < w.im), ⊤ ≤ yw w ⁻¹ᵁ U ∧ valAt' (yw w) U f = Conv.ev T' w hw ⟨_, h⟩ := by
  intro Z T yT yw hyw
  have hc : ∀ w, T < w.im → yw w = Conv.halfCurve yT w := fun w hw =>
    (hyw w hw).trans (Conv.halfCurve_eq yT hw).symm
  refine ⟨fun U f => ?_, fun U hU => ?_⟩
  · have e : {b ∈ {w : ℂ | T < w.im} | ⊤ ≤ yw b ⁻¹ᵁ U} =
        {b ∈ {w : ℂ | T < w.im} | ⊤ ≤ Conv.halfCurve yT b ⁻¹ᵁ U} := by
      ext b
      exact and_congr_right fun hb => by rw [hc b hb]
    rw [e]
    obtain ⟨h1, h2⟩ := Conv.isHolTo_halfCurve yT U f
    exact ⟨h1, h2.congr fun b hb => by rw [hc b hb.1]⟩
  · have hfac : spMap (Conv.halfRing T).val.toRingHom ≫ yT =
        spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) ≫
          (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT) := by
      rw [← Category.assoc, ← spMap_comp]
      rfl
    have hU' : ⊤ ≤ (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT) ⁻¹ᵁ U := by
      intro p _
      rw [hfac] at hU
      obtain rfl : p = spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) (default : PrimeSpectrum ℂ⸨X⸩) :=
        Subsingleton.elim (α := PrimeSpectrum Conv.convLaurent) _ _
      exact hU (x := (default : PrimeSpectrum ℂ⸨X⸩)) trivial
    refine ⟨?_, fun f => ?_⟩
    · obtain ⟨T', h, hT'⟩ := Conv.exists_le_preimage_inclusion yT hU'
      refine ⟨T', h, fun T'' i hle hi => ?_⟩
      have hi' : i = (Subalgebra.inclusion (Conv.halfRing_mono hle) :
          Conv.halfRing T' →+* Conv.halfRing T'').comp
          (Subalgebra.inclusion (Conv.halfRing_mono h) : Conv.halfRing T →+* Conv.halfRing T') :=
        RingHom.ext fun r => Subtype.ext (hi r)
      rw [hi', spMap_comp, Category.assoc]
      exact fun p _ => hT' (x := spMap _ p) trivial
    · obtain ⟨T', h, h1, h2⟩ := Conv.exists_valAt'_halfCurve rfl hU'
      obtain ⟨hf, hv⟩ := h2 f
      have e : valR (spMap (Conv.halfRing T).val.toRingHom ≫ yT) U f =
          ((valR (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT) U f :
            Conv.convLaurent) : ℂ⸨X⸩) := by
        rw [hfac, HolHom.valR_spMap _ _ U hU']
        rfl
      refine ⟨T', h, e ▸ hf, fun w hw => ?_⟩
      rw [hc w (h.trans_lt hw)]
      exact ⟨h1 w hw, (hv w hw).trans (Conv.ev_congr hw hw e.symm)⟩

end GlobalTheory.HalfPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemThetaShiftZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory.ArcThetaSpaces

open TwistedTheta

section

variable {P : Out.PolAV (Sp ℂ)} {g : ℕ} {u : HolUnif P.A P.L g} {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}

theorem eq_zero_of_val (u : HolUnif P.A P.L g) (U : P.A.left.Opens) (f : Γ(P.A.left, U))
    (h : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → valAt' (u.ex z).left U f = 0) : f = 0 := by
  have := P.isAb.smooth
  have := isReduced_of_smooth_complex _ P.A.hom inferInstance
  refine ComplexPoints.eq_of_valAt'_eq P.A.hom _ _ _ fun x hx hi => ?_
  obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk x hx)
  obtain rfl : (u.ex z).left = x := by rw [hz]; rfl
  rw [h z hi, valAt'_zero]

theorem finite_thetaShift (hT : Out.GlobalSectionsRankAlgClosed) {j : ℕ} (hj : 1 ≤ j)
    (h₁ : ∀ s, ∃ θ, u.IsFnPow j s θ) (h₂ : ∀ θ, u.IsThetaFn Hm χ j θ → ∃ s, u.IsFnPow j s θ) (c : Fin g → ℂ) :
    Module.Finite ℂ (thetaShift u Hm χ j c) := by
  obtain ⟨b, rfl⟩ : ∃ b : Fin g → ℂ, c = j • b := ⟨(j : ℂ)⁻¹ • c, by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (Nat.cast_ne_zero.2 (by omega))]⟩
  obtain ⟨β, hβ⟩ := PowSec.exists_basis_sections hT ℂ P j hj
  choose φ hφ using h₁
  have hle : thetaShift u Hm χ j (j • b) ≤ Submodule.span ℂ (Set.range fun i z => φ (β i) (z + b)) := by
    intro θ hθ
    obtain ⟨s, hs⟩ := h₂ _ (isThetaFn_sub hθ)
    obtain ⟨a, ha, -⟩ := hβ s
    refine (Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨a, funext fun z => ?_⟩
    have hi := FrameValue.le_chartAt P.isLB (u.ex (z + b)).left
    set i := FrameValue.chartAt P.isLB (u.ex (z + b)).left
    have hi' : ⊤ ≤ (u.ex (z + b)).left ⁻¹ᵁ (lbPow P.L j).U (fun _ => i) := fun p hp => mem_powChart.2 (hi hp)
    have e := (valAt'_sum _ _ _ _).symm.trans
      ((congrArg (valAt' _ _) (ha fun _ => i)).symm.trans (hs (fun _ => i) (z + b) hi'))
    simp only [add_sub_cancel_right] at e
    refine mul_right_cancel₀ (pow_ne_zero j (u.fr_ne i _ hi)) (Eq.trans ?_ e)
    rw [Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Eq.trans ?_ ((valAt'_mul _ _ _ _).trans (congrArg₂ (· * ·)
      (valAt'_constFn _ _ (Over.w (u.ex (z + b))) _ _ hi') (hφ _ _ _ hi'))).symm
    simp [_root_.mul_assoc]
  have := Module.Finite.span_of_finite ℂ (Set.finite_range fun i z => φ (β i) (z + b))
  exact Submodule.finiteDimensional_of_le hle

theorem mem_thetaShift_zero {j : ℕ} {θ : (Fin g → ℂ) → ℂ} (h : u.IsThetaFn Hm χ j θ) : θ ∈ thetaShift u Hm χ j 0 :=
  ⟨h.1, fun l z => by rw [h.2 l z, FrameValue.hermForm_zero_left]; simp⟩

theorem exists_ne_zero (hT : Out.GlobalSectionsRankAlgClosed) (h₁ : ∀ s, ∃ θ, u.IsThetaFn Hm χ 1 θ ∧ u.IsFnPow 1 s θ) :
    ∃ θ, u.IsThetaFn Hm χ 1 θ ∧ θ ≠ 0 := by
  obtain ⟨β, hβ⟩ := PowSec.exists_indep_sections hT P 1 le_rfl
  have i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  by_contra hne
  push_neg at hne
  have h0 : ∀ i j, (β i).f j = 0 := fun i j => eq_zero_of_val u _ _ fun z hz => by
    obtain ⟨θ, h, h'⟩ := h₁ (β i)
    rw [h' j z hz, hne θ h, Pi.zero_apply, zero_mul]
  exact one_ne_zero (congrFun (hβ 1 fun j => by simp [h0]) i₀)

theorem exists_isFn (h₁ : ∀ s, ∃ θ, u.IsThetaFn Hm χ 1 θ ∧ u.IsFnPow 1 s θ) (th : P.L.Sec) (h : ∃ j, th.f j ≠ 0) :
    ∃ θ, u.IsThetaFn Hm χ 1 θ ∧ θ ≠ 0 ∧ u.IsFn th θ := by
  obtain ⟨θ, h₂, h₃⟩ := h₁ (secToPow th 1)
  have hf : u.IsFn th θ := fun i z hi => by
    have hi' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P.L 1).U (fun _ => i) := fun p hp => mem_powChart.2 (hi hp)
    have e := h₃ (fun _ => i) z hi'
    rw [pow_one] at e
    refine Eq.trans ?_ e
    exact ((valAt'_res _ _ (th.f i ^ 1) hi').trans (by rw [pow_one])).symm
  refine ⟨θ, h₂, ?_, hf⟩
  rintro rfl
  obtain ⟨j, hj⟩ := h
  exact hj (eq_zero_of_val u _ _ fun z hz => by rw [hf j z hz, Pi.zero_apply, zero_mul])

end

theorem sections_theta : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a), (∀ (j : ℕ) (α : Λ.A.X), 1 ≤ j → (∀ s, Λ.fn j α s ∈ Λ.A.Theta j α) ∧ ∀ th ∈ Λ.A.Theta j α, ∃! s, Λ.fn j α s = th) ∧ AnFin Λ.A ∧ ∀ th : a.D₀.P.L.Sec, (∃ j, th.f j ≠ 0) → ∃ θ ∈ Λ.A.Theta 1 0, θ ≠ 0 ∧ Λ.u.IsFn th θ := by
  intro hL _ E _ _ _ H _ D l c O _ β _ _ b a Λ
  have hT := theta_eq_thetaShift Λ.A Λ.u (fun m => Λ.A.chi ⟨m.1, Λ.lam ▸ m.2⟩) Λ.lam
    (fun l l' e => congrArg Λ.A.chi (Subtype.ext e))
  have h0 : Λ.A.ct 0 = 0 := map_zero _
  have hθ : ∀ n θ, Λ.u.IsThetaFn Λ.A.Hm (fun m => Λ.A.chi ⟨m.1, Λ.lam ▸ m.2⟩) n θ → ∃ s, Λ.u.IsFnPow n s θ :=
    fun n θ h => ((Λ.pow n).2 θ h).exists
  refine ⟨fun j α hj => ?_, ⟨fun j α hj => ?_, ?_⟩, fun th h => ?_⟩
  · rw [hT]
    refine ⟨fun s => secFn_mem Λ.ah (Λ.ct α) s, fun th hth => ?_⟩
    obtain ⟨s, hs⟩ := exists_secFn_eq Λ.ah (by omega) (hθ j) (Λ.ct α) hth
    exact ⟨s, hs, fun t ht => secFn_injective (Λ.ct α) (ht.trans hs.symm)⟩
  · rw [hT]
    exact finite_thetaShift hL.globalSectionsRank hj (fun s => ((Λ.pow j).1 s).exists.imp fun _ h => h.2) (hθ j) _
  · rw [hT, h0]
    obtain ⟨θ, h₁, h₂⟩ := exists_ne_zero hL.globalSectionsRank fun s => ((Λ.pow 1).1 s).exists
    exact ⟨θ, mem_thetaShift_zero h₁, h₂⟩
  · rw [hT, h0]
    obtain ⟨θ, h₁, h₂⟩ := exists_isFn (fun s => ((Λ.pow 1).1 s).exists) th h
    exact ⟨θ, mem_thetaShift_zero h₁, h₂⟩

end GlobalTheory.ArcThetaSpaces
end
end

