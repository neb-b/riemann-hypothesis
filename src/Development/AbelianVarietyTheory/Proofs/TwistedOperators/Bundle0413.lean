module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0368

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedLatticePrescribedLocalComponents
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom

namespace GlobalTheory.GluedCmp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Algebra

variable {A : Type} [CommRing A] {n k : ℕ} (m : Matrix (Fin n) (Fin k) A) (z : Fin n → A) {e t T : A}

theorem unit_fwd (he : e * e = e) (ht : t * T = 1) (x f : Fin k → A) (a : A) :
    e • (m *ᵥ (x + a • f) + (a * t) • z) = m *ᵥ (e • x + (a * (e * t)) • T • f) + (a * (e * t) * e) • z ∧
      e • (e • x + (a * (e * t)) • T • f) = e • x + (a * (e * t)) • T • f := by
  have h1 : a * (e * t) * e = e * (a * t) := by linear_combination (a * t) * he
  have h2 : a * (e * t) * T = e * a := by linear_combination (a * e) * ht
  rw [h1, smul_smul (a * (e * t)) T f, h2]
  refine ⟨?_, ?_⟩
  · simp only [Matrix.mulVec_add, Matrix.mulVec_smul, smul_add, smul_smul]
  · simp only [smul_add, smul_smul, ← mul_assoc, he]

theorem unit_bwd (he : e * e = e) (ht : t * T = 1) (x f : Fin k → A) (hx : e • x = x) (a : A) :
    m *ᵥ x + (a * e) • z = m *ᵥ ((x - (a * e) • T • f) + (a * e * T) • f) + (a * e * T * t) • z ∧
      e • (m *ᵥ x + (a * e) • z) = m *ᵥ x + (a * e) • z := by
  have h1 : a * e * T * t = a * e := by linear_combination (a * e) * ht
  have h2 : e * (a * e) = a * e := by linear_combination a * he
  refine ⟨?_, ?_⟩
  · rw [h1, smul_smul (a * e) T f, sub_add_cancel]
  · rw [smul_add, ← Matrix.mulVec_smul, hx, smul_smul, h2]

theorem glue_fwd (he : e * e = e) (x f g : Fin k → A) (hg : e • g = g) (a : A) :
    e • (m *ᵥ (x + a • f) + (a * t) • z) = m *ᵥ (e • x - a • (g - e • f)) + a • ((t * e) • z + m *ᵥ g) ∧
      e • (e • x - a • (g - e • f)) = e • x - a • (g - e • f) := by
  have hs : e • (g - e • f) = g - e • f := by rw [smul_sub, hg, smul_smul, he]
  refine ⟨?_, ?_⟩
  · simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_add, smul_sub, smul_smul]
    module
  · rw [smul_sub e (e • x) (a • (g - e • f)), smul_smul e e x, he, smul_comm e a (g - e • f), hs]

theorem glue_bwd (he : e * e = e) (x f g : Fin k → A) (hx : e • x = x) (hg : e • g = g) (a : A) :
    m *ᵥ x + a • ((t * e) • z + m *ᵥ g) = m *ᵥ ((x + a • (g - e • f)) + (a * e) • f) + (a * e * t) • z ∧
      e • (m *ᵥ x + a • ((t * e) • z + m *ᵥ g)) = m *ᵥ x + a • ((t * e) • z + m *ᵥ g) := by
  have h2 : e * (t * e) = t * e := by linear_combination t * he
  refine ⟨?_, ?_⟩
  · simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_add, smul_sub, smul_smul]
    module
  · rw [smul_add e (m *ᵥ x), ← Matrix.mulVec_smul m e x, hx, smul_comm e a, smul_add e ((t * e) • z),
      smul_smul e (t * e) z, h2, ← Matrix.mulVec_smul m e g, hg]

theorem idem_smul_smul (he : e * e = e) (y : Fin n → A) : e • e • y = e • y := by
  rw [smul_smul, he]

end Algebra

variable {D : D7} {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {z : Y.V} {u : D.what₂.Word} {L₀ : Lat X} {x₀ : X.V}

theorem fg_glueLat (h : L₀.FG) : (glueLat Y X ι z u L₀ x₀).FG := by
  unfold glueLat
  refine Submodule.FG.sup ?_ (Submodule.fg_span_singleton _)
  refine Submodule.FG.map _ ?_
  rw [show (Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E) =
      (((Formalism.L2.Herm.crd X).restrictScalars (𝓞 D.host.E) : X.V ≃ₗ[𝓞 D.host.E] _) : X.V →ₗ[𝓞 D.host.E] _) from rfl,
    Submodule.comap_equiv_eq_map_symm]
  exact h.map _

theorem cmp_unit (hg : IsGlueVec X u L₀ (vA X x₀)) {w : Pl D.host.E}
    (hw : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) (y : Fin Y.rank → EAf D) :
    InCmp (idem w) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y ↔
      ∃ x, InCmp (idem w) L₀ x ∧ ∃ a ∈ OA D, y = mA Y X ι *ᵥ x + (a * idem w) • vA Y z := by
  have he := idem_mul_self w
  have ht := inc_inv_mul u
  have het : idem w * inc D (Tu D u)⁻¹ ∈ OA D := (idem_mul_inv_mem_iff u w).2 hw
  have hew := idem_mem w
  unfold InCmp
  constructor
  · rintro ⟨hy, hey⟩
    obtain ⟨x, hx, a, ha, rfl⟩ := (mem_hat_glueLat y).1 hy
    obtain ⟨h1, h2⟩ := unit_fwd (mA Y X ι) (vA Y z) he ht x (vA X x₀) a
    refine ⟨idem w • x + (a * (idem w * inc D (Tu D u)⁻¹)) • inc D (Tu D u) • vA X x₀,
      ⟨add_mem_hat (smul_mem_hat hew hx) (smul_mem_hat (mul_mem ha het) hg.mul_mem), h2⟩,
      a * (idem w * inc D (Tu D u)⁻¹), mul_mem ha het, ?_⟩
    rw [← hey, h1]
  · rintro ⟨x, ⟨hx, hex⟩, a, ha, rfl⟩
    obtain ⟨h1, h2⟩ := unit_bwd (mA Y X ι) (vA Y z) he ht x (vA X x₀) hex a
    refine ⟨?_, h2⟩
    rw [h1]
    exact (mem_hat_glueLat _).2 ⟨_, sub_mem_hat hx (smul_mem_hat (mul_mem ha hew) hg.mul_mem), _,
      mul_mem (mul_mem ha hew) (inc_Tu_mem u), rfl⟩

theorem cmp_glue {w : Pl D.host.E} {g : Fin X.rank → EAf D} (h1 : idem w • g = g)
    (h2 : g - idem w • vA X x₀ ∈ hat L₀) (y : Fin Y.rank → EAf D) :
    InCmp (idem w) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y ↔
      ∃ x, InCmp (idem w) L₀ x ∧ ∃ a ∈ OA D,
        y = mA Y X ι *ᵥ x + a • ((inc D (Tu D u)⁻¹ * idem w) • vA Y z + mA Y X ι *ᵥ g) := by
  have he := idem_mul_self w
  have hew := idem_mem w
  unfold InCmp
  constructor
  · rintro ⟨hy, hey⟩
    obtain ⟨x, hx, a, ha, rfl⟩ := (mem_hat_glueLat y).1 hy
    obtain ⟨k1, k2⟩ := glue_fwd (mA Y X ι) (vA Y z) (t := inc D (Tu D u)⁻¹) he x (vA X x₀) g h1 a
    refine ⟨idem w • x - a • (g - idem w • vA X x₀),
      ⟨sub_mem_hat (smul_mem_hat hew hx) (smul_mem_hat ha h2), k2⟩, a, ha, ?_⟩
    rw [← hey, k1]
  · rintro ⟨x, ⟨hx, hex⟩, a, ha, rfl⟩
    obtain ⟨k1, k2⟩ := glue_bwd (mA Y X ι) (vA Y z) (t := inc D (Tu D u)⁻¹) he x (vA X x₀) g hex h1 a
    refine ⟨?_, k2⟩
    rw [k1]
    exact (mem_hat_glueLat _).2 ⟨_, add_mem_hat hx (smul_mem_hat ha h2), _, mul_mem ha hew, rfl⟩

theorem cmp_conj (h : IsLine Y X ι z u) (hg : IsGlueVec X u L₀ (vA X x₀)) (w : Pl D.host.E) (y : Fin Y.rank → EAf D) :
    InCmp (cjA D (idem w)) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y ↔
      cjA D (idem w) • y = y ∧ (∃ (x : Fin X.rank → EAf D) (a : EAf D), y = mA Y X ι *ᵥ x + a • vA Y z) ∧
        ∀ y', InCmp (idem w) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y' → hA Y y' y ∈ OA D := by
  have hew := idem_mem w
  unfold InCmp
  constructor
  · rintro ⟨hy, hcy⟩
    obtain ⟨x, hx, a, ha, rfl⟩ := (mem_hat_glueLat y).1 hy
    refine ⟨hcy, ⟨x + a • vA X x₀, a * inc D (Tu D u)⁻¹, rfl⟩, ?_⟩
    rintro y' ⟨hy', -⟩
    exact (mem_hat_glueLat_iff_dual h hg _ _).1 hy y' hy'
  · rintro ⟨hcy, ⟨x, a, rfl⟩, hdual⟩
    refine ⟨(mem_hat_glueLat_iff_dual h hg x a).2 ?_, hcy⟩
    intro y'' hy''
    have key : hA Y y'' (mA Y X ι *ᵥ x + a • vA Y z) =
        hA Y (idem w • y'') (mA Y X ι *ᵥ x + a • vA Y z) := by
      conv_lhs => rw [← hcy]
      rw [hA_smul_right, hA_smul_left, cjA_cjA]
    rw [key]
    exact hdual _ ⟨smul_mem_hat hew hy'', idem_smul_smul (idem_mul_self w) y''⟩

theorem isGlued_glueLat : ∀ (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V)
    (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V) (f₀ : Pl D.host.E → Fin X.rank → EAf D),
    Submodule.IsLattice D.host.E L₀ → IsGlueVec X u L₀ (vA X x₀) →
    (∀ w : Pl D.host.E, π ∈ w.asIdeal → idem w • f₀ w = f₀ w ∧ f₀ w - idem w • vA X x₀ ∈ hat L₀) →
    IsGlued Y X ι z u π L₀ f₀ (glueLat Y X ι z u L₀ x₀) := by
  intro D u π Y X ι z h L₀ x₀ f₀ hL hg hf
  unfold IsGlued
  refine ⟨fg_glueLat hL.fg, ?_, ?_⟩
  · intro w e he hw y
    obtain rfl := eq_idem he
    exact cmp_unit hg hw y
  · intro w e he hπ
    obtain rfl := eq_idem he
    exact ⟨fun y => cmp_glue (hf w hπ).1 (hf w hπ).2 y, cmp_conj h hg w⟩

end GlobalTheory.GluedCmp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedLatticeSelfDualPrimitiveMeet
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom

namespace GlobalTheory.GlueVecLattice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {z : Y.V} {u : D.what₂.Word}

theorem vA_flat (x : X.V) (t : D.host.E) :
    vA Y (ι x + t • z) = mA Y X ι *ᵥ vA X x + inc D t • vA Y z := by
  rw [vA_add, vA_smul, mA_mulVec_vA]

theorem mem_of_coords {L₀ : Lat X} {x₀ x : X.V} {t : D.host.E}
    (h1 : t * Tu D u ∈ (algebraMap (𝓞 D.host.E) D.host.E).range)
    (h2 : Formalism.L2.Herm.crd X (x - (t * Tu D u) • x₀) ∈ L₀) : ι x + t • z ∈ glueLat Y X ι z u L₀ x₀ := by
  obtain ⟨a, ha⟩ := h1
  refine (mem_glueLat _).2 ⟨_, h2, a, ?_⟩
  change _ = _ + algebraMap (𝓞 D.host.E) D.host.E a • _
  rw [ha, map_sub, map_smul, smul_add, smul_smul, mul_assoc, mul_inv_cancel₀ (Tu_ne_zero u), mul_one]
  abel

theorem coords_of_mem_hat (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) {x₀ x : X.V}
    {t : D.host.E} (hy : vA Y (ι x + t • z) ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀))) :
    t * Tu D u ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ∧
      Formalism.L2.Herm.crd X (x - (t * Tu D u) • x₀) ∈ L₀ := by
  obtain ⟨x₁, hx₁, a, ha, e⟩ := (mem_hat_glueLat _).1 hy
  rw [vA_flat] at e
  obtain ⟨e1, e2⟩ := flat_inj h e
  have e3 : a = inc D (t * Tu D u) := by
    rw [RingHom.map_mul, e2, mul_assoc, inc_inv_mul, mul_one]
  refine ⟨(inc_mem_iff _).1 (e3 ▸ ha), GlobalTheory.GlueUnique.mem_of_inc_mem_hat hL.fg ?_⟩
  change vA X (x - (t * Tu D u) • x₀) ∈ _
  have e4 : vA X (x - (t * Tu D u) • x₀) = x₁ := by
    rw [sub_eq_add_neg, ← neg_smul, vA_add, vA_smul, RingHom.map_neg, ← e3, e1, neg_smul, add_neg_cancel_right]
  rwa [e4]

theorem mem_iff_coords (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) {x₀ : X.V} (x : X.V)
    (t : D.host.E) : ι x + t • z ∈ glueLat Y X ι z u L₀ x₀ ↔
      t * Tu D u ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ∧
        Formalism.L2.Herm.crd X (x - (t * Tu D u) • x₀) ∈ L₀ :=
  ⟨fun hy => coords_of_mem_hat h hL (vA_mem_hat Y hy), fun hy => mem_of_coords hy.1 hy.2⟩

theorem mem_flatSp (y : Y.V) : y ∈ flatSp Y X ι z ↔ ∃ (x : X.V) (t : D.host.E), y = ι x + t • z := by
  rw [flatSp, Submodule.mem_sup]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, b, hb, rfl⟩
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hb
    exact ⟨x, t, rfl⟩
  · rintro ⟨x, t, rfl⟩
    exact ⟨_, ⟨x, rfl⟩, _, Submodule.mem_span_singleton.2 ⟨t, rfl⟩, rfl⟩

theorem glueLat_fg {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) (x₀ : X.V) : (glueLat Y X ι z u L₀ x₀).FG := by
  refine Submodule.FG.sup (Submodule.FG.map _ ?_) (Submodule.fg_span_singleton _)
  have e : L₀.comap ((Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E)) =
      L₀.map ((Formalism.L2.Herm.crd X).symm.toLinearMap.restrictScalars (𝓞 D.host.E)) := by
    ext x
    constructor
    · intro hx
      exact ⟨_, hx, (Formalism.L2.Herm.crd X).symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      change Formalism.L2.Herm.crd X ((Formalism.L2.Herm.crd X).symm y) ∈ L₀
      rwa [LinearEquiv.apply_symm_apply]
  rw [e]
  exact hL.fg.map _

theorem span_glueLat {L₀ : Lat X} (hL : Submodule.IsFullLattice D.host.E L₀) (x₀ : X.V) :
    Submodule.span D.host.E (glueLat Y X ι z u L₀ x₀ : Set Y.V) = flatSp Y X ι z := by
  have h1 : ∀ x : X.V, ι x ∈ Submodule.span D.host.E (glueLat Y X ι z u L₀ x₀ : Set Y.V) := by
    intro x
    obtain ⟨y, rfl⟩ := (Formalism.L2.Herm.crd X).symm.surjective x
    have hy : y ∈ Submodule.span D.host.E (L₀ : Set (Fin X.rank → D.host.E)) := (Submodule.IsFullLattice.span_eq_top (self := hL)) ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy =>
      exact Submodule.subset_span ((mem_glueLat _).2 ⟨_, by rwa [LinearEquiv.apply_symm_apply], 0, by simp⟩)
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul, map_smul]; exact Submodule.smul_mem _ c ha
  refine le_antisymm (Submodule.span_le.2 fun y hy => ?_) fun y hy => ?_
  · obtain ⟨x, -, a, rfl⟩ := (mem_glueLat y).1 hy
    refine (mem_flatSp _).2 ⟨x + (a : D.host.E) • x₀, a * (Tu D u)⁻¹, ?_⟩
    rw [map_add (f := _), map_smul, smul_add, smul_smul]
    abel
  · obtain ⟨x, t, rfl⟩ := (mem_flatSp y).1 hy
    refine add_mem (h1 x) (Submodule.smul_mem _ t ?_)
    have h2 : (Tu D u)⁻¹ • z + ι x₀ ∈ Submodule.span D.host.E (glueLat Y X ι z u L₀ x₀ : Set Y.V) :=
      Submodule.subset_span ((mem_glueLat _).2 ⟨0, by simp, 1, by simp⟩)
    have h3 := Submodule.smul_mem _ (Tu D u) (sub_mem h2 (h1 x₀))
    rwa [add_sub_cancel_right, smul_smul, mul_inv_cancel₀ (Tu_ne_zero u), one_smul] at h3

theorem isSDIn_glueLat (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsFullLattice D.host.E L₀) {x₀ : X.V}
    (hg : IsGlueVec X u L₀ (vA X x₀)) : IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) := by
  refine ⟨glueLat_fg hL.toIsLattice x₀, span_glueLat hL x₀, fun y hy => ?_⟩
  obtain ⟨x, t, rfl⟩ := (mem_flatSp y).1 hy
  have key := mem_hat_glueLat_iff_dual h hg (vA X x) (inc D t)
  rw [← vA_flat] at key
  constructor
  · intro hm x' hx'
    rw [← inc_mem_iff, ← hA_vA]
    exact key.1 (vA_mem_hat Y hm) _ (vA_mem_hat Y hx')
  · intro H
    have h1 := coords_of_mem_hat h hL.toIsLattice (key.2 (hA_mem_of_forall ?_))
    · exact mem_of_coords h1.1 h1.2
    · rintro _ ⟨x', hx', rfl⟩
      change hA Y (vA Y x') _ ∈ _
      rw [hA_vA, inc_mem_iff]
      exact H x' hx'

theorem capX_glueLat (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) (x₀ : X.V) :
    capX Y X ι (glueLat Y X ι z u L₀ x₀) = L₀ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 : ι x + (0 : D.host.E) • z ∈ glueLat Y X ι z u L₀ x₀ := by
      rw [zero_smul, add_zero]; exact hx
    have h2 := ((mem_iff_coords h hL x 0).1 h1).2
    rwa [zero_mul, zero_smul, sub_zero] at h2
  · intro hy
    obtain ⟨x, rfl⟩ := (Formalism.L2.Herm.crd X).surjective y
    exact ⟨x, (mem_glueLat (ι x)).2 ⟨x, hy, 0, by simp⟩, rfl⟩

theorem isPrim_glueLat (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) {x₀ : X.V}
    (hg : IsGlueVec X u L₀ (vA X x₀)) : IsPrim Y z (glueLat Y X ι z u L₀ x₀) := by
  intro a
  have e : a • z = ι 0 + a • z := by rw [map_zero, zero_add]
  have hmem (x : Fin X.rank → D.host.E) : (fun i => inc D (x i)) ∈ hat L₀ ↔ x ∈ L₀ :=
    ⟨GlobalTheory.GlueUnique.mem_of_inc_mem_hat hL.fg, inc_mem_hat⟩
  rw [e, mem_iff_coords h hL, ← hmem, ← inc_mem_iff, ← inc_mem_iff]
  change _ ∧ vA X (0 - (a * Tu D u) • x₀) ∈ _ ↔ _
  rw [zero_sub, ← neg_smul, vA_smul, RingHom.map_neg, RingHom.map_mul]
  generalize inc D a = b
  constructor
  · rintro ⟨h1, h2⟩
    have h3 := hg.pair _ h2
    rw [hA_smul_right, RingHom.map_neg, RingHom.map_mul, cjA_inc_Tu] at h3
    have h4 := mul_mem (cjA_mem h1) hg.norm
    rw [RingHom.map_mul, cjA_inc_Tu] at h4
    rw [← cjA_mem_iff]
    convert neg_mem (add_mem h3 h4) using 1
    linear_combination (-(cjA D b)) * inc_inv_mul u
  · intro hb
    refine ⟨mul_mem hb (inc_Tu_mem u), ?_⟩
    rw [← neg_mul, ← smul_smul]
    exact smul_mem_hat (neg_mem hb) hg.mul_mem

theorem glueLat_selfDual_prim_cap : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V),
    IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V), Submodule.IsFullLattice D.host.E L₀ → IsGlueVec X u L₀ (vA X x₀) →
      IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) ∧ IsPrim Y z (glueLat Y X ι z u L₀ x₀) ∧
        capX Y X ι (glueLat Y X ι z u L₀ x₀) = L₀ :=
  fun _ _ _ _ _ _ h _ x₀ hL hg => ⟨isSDIn_glueLat h hL hg, isPrim_glueLat h hL.toIsLattice hg, capX_glueLat h hL.toIsLattice x₀⟩

end GlobalTheory.GlueVecLattice

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyGeneratorRatioPointwiseBound
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

noncomputable section

namespace GlobalTheory.HeckeGenBound

theorem norm_le_of_valueId {g n : ℕ} (Hm Hm' : Matrix (Fin g) (Fin g) ℂ) (hH' : Hm'.IsHermitian)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (p : ℕ)
    (hHH : ∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w)
    (θ θ' f : (Fin g → ℂ) → ℂ) (T : ℂ) (wm : Fin n → (Fin g → ℂ)) (w : Fin g → ℂ)
    (hf : f (h w) ≠ 0)
    (hfa : ∀ m, ‖f (h w)‖ = Real.exp (Real.pi * (hermForm Hm' (h w) (h (wm m))).re +
      Real.pi / 2 * (hermForm Hm' (h (wm m)) (h (wm m))).re) * ‖f (h w + h (wm m))‖)
    (hid : T * θ' (h w) * f (h w) = ∑ m, θ ((p : ℂ) • (w + wm m)) * f (h w + h (wm m))) :
    ‖T‖ * (‖θ' (h w)‖ * Real.exp (-(Real.pi / 2) * (hermForm Hm' (h w) (h w)).re)) ≤
      ∑ m, ‖θ ((p : ℂ) • w + (p : ℂ) • wm m)‖ * Real.exp (-(Real.pi / 2) *
        (hermForm Hm ((p : ℂ) • w + (p : ℂ) • wm m) ((p : ℂ) • w + (p : ℂ) • wm m)).re) := by
  have hF : 0 < ‖f (h w)‖ := norm_pos_iff.2 hf
  have hs : star (p : ℂ) = p := by simp
  have key : ∀ m, ‖f (h w + h (wm m))‖ * Real.exp (-(Real.pi / 2) * (hermForm Hm' (h w) (h w)).re) =
      ‖f (h w)‖ * Real.exp (-(Real.pi / 2) *
        (hermForm Hm ((p : ℂ) • w + (p : ℂ) • wm m) ((p : ℂ) • w + (p : ℂ) • wm m)).re) := by
    intro m
    have e1 : hermForm Hm ((p : ℂ) • w + (p : ℂ) • wm m) ((p : ℂ) • w + (p : ℂ) • wm m) =
        hermForm Hm' (h w + h (wm m)) (h w + h (wm m)) := by
      rw [← map_add (f := _), hHH, ← smul_add, GlobalTheory.UnitFrameGen.hermForm_smul_left,
        GlobalTheory.UnitFrameGen.hermForm_smul_right, hs]
      ring
    rw [e1, hfa m, GlobalTheory.UnitFrameGen.hermForm_add_left, GlobalTheory.UnitFrameGen.hermForm_add_right,
      GlobalTheory.UnitFrameGen.hermForm_add_right]
    simp only [Complex.add_re, GlobalTheory.UnitFrameGen.hermForm_swap_re hH' (h (wm m)) (h w)]
    rw [mul_comm (Real.exp _) ‖_‖, _root_.mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have h1 : ‖T‖ * ‖θ' (h w)‖ * ‖f (h w)‖ ≤
      ∑ m, ‖θ ((p : ℂ) • (w + wm m))‖ * ‖f (h w + h (wm m))‖ := by
    rw [← norm_mul, ← norm_mul, hid]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp only [norm_mul]
  refine le_of_mul_le_mul_right ?_ hF
  calc ‖T‖ * (‖θ' (h w)‖ * Real.exp (-(Real.pi / 2) * (hermForm Hm' (h w) (h w)).re)) * ‖f (h w)‖
      = (‖T‖ * ‖θ' (h w)‖ * ‖f (h w)‖) * Real.exp (-(Real.pi / 2) * (hermForm Hm' (h w) (h w)).re) := by ring
    _ ≤ (∑ m, ‖θ ((p : ℂ) • (w + wm m))‖ * ‖f (h w + h (wm m))‖) *
        Real.exp (-(Real.pi / 2) * (hermForm Hm' (h w) (h w)).re) :=
      mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = ∑ m, ‖θ ((p : ℂ) • w + (p : ℂ) • wm m)‖ * (‖f (h w + h (wm m))‖ *
        Real.exp (-(Real.pi / 2) * (hermForm Hm' (h w) (h w)).re)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [smul_add]; ring
    _ = _ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [key m]; ring

theorem exists_pointwise_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (P : Ideal (𝓞 E)) (p i : ℕ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), admitted l P p → Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C → HkPtC p (U.un k x) C z → FrBor t (U.un k' x') z → IsUnitFr (U.X k) x.1 → IsUnitFr (U.X k') x'.1 → ∃ (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (Fd Fd' : Set (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (u u' : (Fin g → ℂ) → ℝ) (v : Fin (Ideal.absNorm P ^ i) → (Fin g → ℂ)), Countable Λ ∧ Countable Λ' ∧ MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume ∧ MeasureTheory.IsAddFundamentalDomain Λ' Fd' MeasureTheory.volume ∧ (∀ a ∈ Λ, h a ∈ Λ') ∧ (∀ z, 0 ≤ u z) ∧ (∀ z, 0 ≤ u' z) ∧ (∀ a ∈ Λ, ∀ z, u (z + a) = u z) ∧ (∀ a ∈ Λ', ∀ z, u' (z + a) = u' z) ∧ (∫ z in Fd, u z ^ 2) / (MeasureTheory.volume Fd).toReal = 1 ∧ (∫ z in Fd', u' z ^ 2) / (MeasureTheory.volume Fd').toReal = 1 ∧ ∀ w, cabs (t none : CAt σ) * u' (h w) ≤ ∑ m, u ((p : ℂ) • w + v m) := by
  intro E _ _ _ H Dw l Xo c σ r U hG hU P p i k k' x x' C z t hAd hK hHk hb hx hx'
  have hU0 := hU
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, -, hP⟩ := hU
  obtain ⟨Pm, -, hp, hu, -, hA⟩ := hP k x
  obtain ⟨Pm', -, hp', hu', -, hA'⟩ := hP k' x'
  obtain ⟨Hm, χ, fr, θ, Fd, hH, hpos, him, hd, hn, hc, h0, ha, hv, hF, hI⟩ := hA hx
  obtain ⟨Hm', χ', fr', θ', Fd', hH', hpos', him', hd', hn', hc', h0', ha', hv', hF', hI'⟩ := hA' hx'
  obtain ⟨h, wm, hlat, hHH, hwm, hid⟩ := _root_.GlobalTheory.HeckeValueId.hecke_theta_value_identity E H Dw l Xo c σ r U hG hU0 P p i k k' x x' C z t hAd hK hHk hb
    g e F ik Pm Pm' hp hp' hu hu' Hm χ fr θ hH hpos him hd hn hc h0 ha hv Hm' χ' fr' θ' hH' hpos' him' hd' hn' hc'
    h0' ha' hv'
  clear hP

  have per : ∀ (kk : U.Comp) (xx : (U.X kk).dom) (Q : (F.Di (ik kk)).La →+ (Fin g → ℂ))
      (Hq : Matrix (Fin g) (Fin g) ℂ) (χq : (Fin g → ℂ) → ℂ) (frq : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
      (θq : (Fin g → ℂ) → ℂ),
      IsPeriod (F.Di (ik kk)) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Q → (U.un kk xx).x = F.u (ik kk) Q →
      Hq.IsHermitian →
      (∀ j z, ⊤ ≤ (F.ex (ik kk) Q z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → frq j z ≠ 0) →
      (∀ a j z, ‖χq (Q a)‖ = 1 ∧ (⊤ ≤ (F.ex (ik kk) Q z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        frq j z = χq (Q a) * Complex.exp (Real.pi * hermForm Hq z (Q a) +
          Real.pi / 2 * hermForm Hq (Q a) (Q a)) * frq j (z + Q a))) →
      (∀ j z (pt : Sp ℂ ⟶ Gx (U.un kk xx).x),
        pt ≫ Formalism.L2.PjFree.gxFst (U.un kk xx).x = (F.ex (ik kk) Q z).left →
        pt ≫ Formalism.L2.PjFree.gxSnd (U.un kk xx).x = 𝟙 (Sp ℂ) →
        ⊤ ≤ (F.ex (ik kk) Q z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        valAt' pt ((PPx (U.un kk xx).x).U (fun _ => j)) ((U.un kk xx).s.f (fun _ => j)) = θq z * frq j z) →
      ∀ a ∈ Q.range, ∀ z, ‖θq (z + a)‖ * Real.exp (-(Real.pi / 2) * (hermForm Hq (z + a) (z + a)).re) =
        ‖θq z‖ * Real.exp (-(Real.pi / 2) * (hermForm Hq z z).re) := by
    intro kk xx Q Hq χq frq θq hQ hQu hHq hnq haq hvq
    have hexp : ∀ a ∈ Q.range, ∀ z, F.ex (ik kk) Q (z + a) = F.ex (ik kk) Q z := fun a ha z => by
      rw [F.ex_add (ik kk) Q hQ, (F.ex_ker (ik kk) Q hQ a).2 ha]
      exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
    have hw0 : ∀ z, (F.ex (ik kk) Q z).left ≫ Xo.univ.t.G.hom = ((U.un kk xx).x : Sp ℂ ⟶ Xo.X) := fun z =>
      (Over.w (F.ex (ik kk) Q z)).trans hQu.symm
    intro a ha z
    obtain ⟨j, hj⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (F.ex (ik kk) Q z).left
    have hj' : ⊤ ≤ (F.ex (ik kk) Q (z + a)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by rw [hexp a ha]; exact hj
    let q : Over.mk ((U.un kk xx).x : Sp ℂ ⟶ Xo.X) ⟶ Xo.univ.t.G := Over.homMk (F.ex (ik kk) Q z).left (hw0 z)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) q)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) q)
    have v1 := hvq j z _ e1 e2 hj
    have v2 := hvq j (z + a) _ (by rw [hexp a ha]; exact e1) e2 hj'
    have hm : ‖frq j z‖ = Real.exp (Real.pi * (hermForm Hq z a).re + Real.pi / 2 * (hermForm Hq a a).re) *
        ‖frq j (z + a)‖ := by
      obtain ⟨b, rfl⟩ := ha
      exact GlobalTheory.UnitFrameGen.norm_factor Hq _ _ _ _ _ (haq b j z).1 ((haq b j z).2 hj)
    have hsq := GlobalTheory.UnitFrameGen.normSq_periodic hHq _ _ _ _ z a (hnq j _ hj') (v2.symm.trans v1) hm
    have hsq' : ∀ w : Fin g → ℂ, (‖θq w‖ * Real.exp (-(Real.pi / 2) * (hermForm Hq w w).re)) ^ 2 =
        ‖θq w‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hq w w).re) := fun w => by
      rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    refine (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 ?_
    rw [hsq', hsq', hsq]
  have hsq' : ∀ (Hq : Matrix (Fin g) (Fin g) ℂ) (θq : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ),
      (‖θq w‖ * Real.exp (-(Real.pi / 2) * (hermForm Hq w w).re)) ^ 2 =
        ‖θq w‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hq w w).re) := fun Hq θq w => by
    rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  refine ⟨g, Pm.range, Pm'.range, Fd, Fd', h, fun z => ‖θ z‖ * Real.exp (-(Real.pi / 2) * (hermForm Hm z z).re),
    fun z => ‖θ' z‖ * Real.exp (-(Real.pi / 2) * (hermForm Hm' z z).re), fun m => (p : ℂ) • wm m,
    ?_, ?_, hF, hF', ?_, fun z => by positivity, fun z => by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · haveI := hp.2.2.1
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  · haveI := hp'.2.2.1
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  · rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb'⟩ := hlat a
    exact ⟨b, hb'.symm⟩
  · intro a ha0 z
    exact per k x Pm Hm χ fr θ hp hu hH hn ha hv a ha0 z
  · intro a ha0 z
    exact per k' x' Pm' Hm' χ' fr' θ' hp' hu' hH' hn' ha' hv' a ha0 z
  · simp only [hsq']
    exact hI
  · simp only [hsq']
    exact hI'
  · intro w
    obtain ⟨j, hj, hval⟩ := hid w
    have hfa : ∀ m, ‖fr' j (h w)‖ = Real.exp (Real.pi * (hermForm Hm' (h w) (h (wm m))).re +
        Real.pi / 2 * (hermForm Hm' (h (wm m)) (h (wm m))).re) * ‖fr' j (h w + h (wm m))‖ := fun m => by
      obtain ⟨b, hb'⟩ := hwm m
      rw [hb']
      exact GlobalTheory.UnitFrameGen.norm_factor Hm' _ _ _ _ _ (ha' b j (h w)).1 ((ha' b j (h w)).2 hj)
    have := norm_le_of_valueId Hm Hm' hH' h p hHH θ θ' (fr' j) (Formalism.L2.PjFree.toC (t none : CAt σ)) wm w
      (hn' j _ hj) hfa hval
    exact this

end GlobalTheory.HeckeGenBound
end
end

