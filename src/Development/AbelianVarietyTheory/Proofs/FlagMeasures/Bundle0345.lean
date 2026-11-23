module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0336
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfPerpPerp
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0338
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0117

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerDatumStableIffIdentificationsCompatible
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.GdatIota
open Formalism.L2.SG.Pf GlobalTheory.StabCnt

variable {D : D7} {T T' : D.host.E}

theorem mem_gmap' (φ : GV D) (M : LV D) (x : (VS D).V) : x ∈ Formalism.HermitianLatticesTheory.gmap φ M ↔ φ.symm x ∈ M := by
  rw [← gmap_apply_mem φ M, LinearEquiv.apply_symm_apply]

theorem xlam_adapt {A B : LFlag (D.sp.Y 0) D.R.rS T} {φ : GV D} (h : Adapt φ A B) (M : LV D) :
    XLam (Formalism.HermitianLatticesTheory.gmap φ M) B = Formalism.HermitianLatticesTheory.gmap φ (XLam M A) := by
  rw [XLam, XLam, gmap_inf', gmap_toO, adapt_xsp h]

theorem lrep_adapt {A B : LFlag (D.sp.Y 0) D.R.rS T} {φ : GV D} (h : Adapt φ A B) (M : LV D) :
    Lrep (Formalism.HermitianLatticesTheory.gmap φ M) B = Formalism.HermitianLatticesTheory.gmap φ (Lrep M A) := by
  rw [Lrep, Lrep, gmap_inf', gmap_toO, adapt_orth h]

theorem lsub_adapt {A B : LFlag (D.sp.Y 0) D.R.rS T} {φ : GV D} (h : Adapt φ A B) (M : LV D) :
    Lsub (Formalism.HermitianLatticesTheory.gmap φ M) B = Formalism.HermitianLatticesTheory.gmap φ (Lsub M A) := by
  rw [Lsub, Lsub, lrep_adapt h, gmap_inf', gmap_sup', gmap_toO, gmap_toO, adapt_xsp h, adapt_orth h]

theorem ngx_adapt {A B : LFlag (D.sp.Y 0) D.R.rS T} {A' B' : LFlag (D.sp.Y 0) D.R.rS T'} {φ : GV D} (h : Adapt φ A B)
    (h' : Adapt φ A' B') (M : LV D) (n : ℕ) :
    NgX (Formalism.HermitianLatticesTheory.gmap φ M) n B B' = Formalism.HermitianLatticesTheory.gmap φ (NgX M n A A') := by
  rw [NgX, NgX, gmap_sup', gmap_sup', gmap_ideal_smul, xlam_adapt h, xlam_adapt h']

theorem aut_lrep {F : LFlag (D.sp.Y 0) D.R.rS T} {M : LV D} {A : GV D} (hA : A ∈ Aut0 F M) (x : (VS D).V) :
    A x ∈ Lrep M F ↔ x ∈ Lrep M F := by
  have := lrep_adapt hA.1 M
  rw [hA.2] at this
  rw [← gmap_apply_mem A (Lrep M F) x, ← this]

theorem aut_lrep_symm {F : LFlag (D.sp.Y 0) D.R.rS T} {M : LV D} {A : GV D} (hA : A ∈ Aut0 F M) (x : (VS D).V) :
    A.symm x ∈ Lrep M F ↔ x ∈ Lrep M F := by
  rw [← aut_lrep hA (A.symm x), LinearEquiv.apply_symm_apply]

theorem lsub_eq {F : LFlag (D.sp.Y 0) D.R.rS T} {M : LV D} {A h : GV D} (hA : A ∈ Aut0 F M) (hh : Adapt h F F)
    (hc : ∀ x ∈ orth (VS D) (Xsp F), h x - A x ∈ Xsp F) : Lsub (Formalism.HermitianLatticesTheory.gmap h M) F = Lsub M F := by
  rw [lsub_adapt hh]
  ext y
  rw [mem_gmap']
  constructor
  · rintro ⟨hy, hy'⟩
    obtain ⟨l, hl, ξ, hξ, e⟩ := Submodule.mem_sup.1 hy
    have hy2 : y ∈ orth (VS D) (Xsp F) := by
      have := mem_of_map_eq (adapt_orth hh) hy'
      rwa [LinearEquiv.apply_symm_apply] at this
    refine ⟨?_, hy2⟩
    have e2 : y = A l + ((h l - A l) + h ξ) := by
      have : y = h (l + ξ) := by rw [e, LinearEquiv.apply_symm_apply]
      rw [this, map_add (f := _)]; abel
    rw [e2]
    exact Submodule.add_mem_sup ((aut_lrep hA l).2 hl)
      (show _ ∈ Xsp F from add_mem (hc l hl.2) (mem_of_map_eq (adapt_xsp hh) hξ))
  · rintro ⟨hy, hy'⟩
    obtain ⟨l, hl, ξ, hξ, e⟩ := Submodule.mem_sup.1 hy
    refine ⟨?_, symm_mem_of_map_eq (adapt_orth hh) hy'⟩
    have hm := (aut_lrep_symm hA l).2 hl
    have h1 := hc _ hm.2
    rw [LinearEquiv.apply_symm_apply] at h1
    have e2 : h.symm y = A.symm l + h.symm (ξ - (h (A.symm l) - l)) := by
      rw [← e]; simp only [map_add (f := _), map_sub, LinearEquiv.symm_apply_apply]; abel
    rw [e2]
    exact Submodule.add_mem_sup hm
      (show _ ∈ Xsp F from symm_mem_of_map_eq (adapt_xsp hh) (sub_mem (show ξ ∈ Xsp F from hξ) h1))

theorem ngx_shift {F : LFlag (D.sp.Y 0) D.R.rS T} {F' : LFlag (D.sp.Y 0) D.R.rS T'} {M : LV D} {n : ℕ}
    {l m l' m' : (VS D).V} (hl : l ∈ Lrep M F) (hm : m ∈ Lrep M F) (hl' : l' ∈ Lrep M F') (hm' : m' ∈ Lrep M F')
    (h1 : l - m ∈ Xsp F) (h2 : l' - m' ∈ Xsp F') (h : m - m' ∈ NgX M n F F') : l - l' ∈ NgX M n F F' := by
  have e : l - l' = (m - m') + (l - m) - (l' - m') := by abel
  rw [e]
  refine sub_mem (add_mem h ?_) ?_
  · exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨M.sub_mem hl.1 hm.1, h1⟩)
  · exact Submodule.mem_sup_right ⟨M.sub_mem hl'.1 hm'.1, h2⟩

theorem gdat_iff {F : LFlag (D.sp.Y 0) D.R.rS T} {F' : LFlag (D.sp.Y 0) D.R.rS T'} {M : LV D} {A A' h : GV D}
    (hA : A ∈ Aut0 F M) (hA' : A' ∈ Aut0 F' M) (hh : Adapt h F F) (hh' : Adapt h F' F')
    (hc : ∀ x ∈ orth (VS D) (Xsp F), h x - A x ∈ Xsp F)
    (hc' : ∀ x ∈ orth (VS D) (Xsp F'), h x - A' x ∈ Xsp F') :
    gdat F F' (Formalism.HermitianLatticesTheory.gmap h M) = gdat F F' M ↔
      ∀ x' ∈ Lrep M F', ∀ l ∈ Lrep M F,
        (l - x' ∈ NgX M (gS D) F F' ↔ A l - A' x' ∈ NgX M (gS D) F F') := by
  have hG : ∀ p : (VS D).V × (VS D).V, p ∈ (gdat F F' (Formalism.HermitianLatticesTheory.gmap h M)).2.2 ↔
      ∃ l' ∈ Lrep M F', ∃ l ∈ Lrep M F, p.1 - A' l' ∈ Xsp F' ∧ p.2 - A l ∈ Xsp F ∧
        l - l' ∈ NgX M (gS D) F F' := by
    intro p
    show (∃ l' ∈ Lrep (Formalism.HermitianLatticesTheory.gmap h M) F', ∃ l ∈ Lrep (Formalism.HermitianLatticesTheory.gmap h M) F, p.1 - l' ∈ Xsp F' ∧
      p.2 - l ∈ Xsp F ∧ l - l' ∈ NgX (Formalism.HermitianLatticesTheory.gmap h M) (gS D) F F') ↔ _
    rw [lrep_adapt hh, lrep_adapt hh', ngx_adapt hh hh']
    constructor
    · rintro ⟨l', hl', l, hl, h1, h2, h3⟩
      obtain ⟨m', rfl⟩ := h.surjective l'
      obtain ⟨m, rfl⟩ := h.surjective l
      rw [gmap_apply_mem] at hl hl'
      rw [← map_sub, gmap_apply_mem] at h3
      refine ⟨m', hl', m, hl, ?_, ?_, h3⟩
      · simpa using add_mem h1 (hc' m' hl'.2)
      · simpa using add_mem h2 (hc m hl.2)
    · rintro ⟨m', hl', m, hl, h1, h2, h3⟩
      refine ⟨h m', (gmap_apply_mem _ _ _).2 hl', h m, (gmap_apply_mem _ _ _).2 hl, ?_, ?_, ?_⟩
      · simpa using sub_mem h1 (hc' m' hl'.2)
      · simpa using sub_mem h2 (hc m hl.2)
      · rw [← map_sub, gmap_apply_mem]; exact h3
  have hG0 : ∀ p : (VS D).V × (VS D).V, p ∈ (gdat F F' M).2.2 ↔
      ∃ l' ∈ Lrep M F', ∃ l ∈ Lrep M F, p.1 - l' ∈ Xsp F' ∧ p.2 - l ∈ Xsp F ∧
        l - l' ∈ NgX M (gS D) F F' := fun p => Iff.rfl
  constructor
  · intro he x' hx' l hl
    have hx2 := (aut_lrep hA' x').2 hx'
    have hl2 := (aut_lrep hA l).2 hl
    constructor
    · intro hN
      have : (A' x', A l) ∈ (gdat F F' M).2.2 := by
        rw [← he, hG]
        exact ⟨x', hx', l, hl, by simp, by simp, hN⟩
      obtain ⟨m', hm', m, hm, h1, h2, h3⟩ := (hG0 _).1 this
      exact ngx_shift hl2 hm hx2 hm' h2 h1 h3
    · intro hN
      have : (A' x', A l) ∈ (gdat F F' (Formalism.HermitianLatticesTheory.gmap h M)).2.2 := by
        rw [he, hG0]
        exact ⟨A' x', hx2, A l, hl2, by simp, by simp, hN⟩
      obtain ⟨m', hm', m, hm, h1, h2, h3⟩ := (hG _).1 this
      have h1' := symm_mem_of_map_eq (adapt_xsp hA'.1) h1
      have h2' := symm_mem_of_map_eq (adapt_xsp hA.1) h2
      simp only [map_sub, LinearEquiv.symm_apply_apply] at h1' h2'
      exact ngx_shift hl hm hx' hm' h2' h1' h3
  · intro hR
    refine Prod.ext (lsub_eq hA hh hc) (Prod.ext (lsub_eq hA' hh' hc') ?_)
    ext p
    rw [hG, hG0]
    constructor
    · rintro ⟨l', hl', l, hl, h1, h2, h3⟩
      exact ⟨A' l', (aut_lrep hA' l').2 hl', A l, (aut_lrep hA l).2 hl, h1, h2, (hR l' hl' l hl).1 h3⟩
    · rintro ⟨l', hl', l, hl, h1, h2, h3⟩
      obtain ⟨m', rfl⟩ := A'.surjective l'
      obtain ⟨m, rfl⟩ := A.surjective l
      rw [aut_lrep hA'] at hl'
      rw [aut_lrep hA] at hl
      exact ⟨m', hl', m, hl, h1, h2, (hR m' hl' m hl).2 h3⟩

theorem aut_conj {A B : LFlag (D.sp.Y 0) D.R.rS T} {M : LV D} {g b : GV D} (hg : Adapt g A B) (hb : b ∈ Aut0 A M) :
    g * b * g⁻¹ ∈ Aut0 B (Formalism.HermitianLatticesTheory.gmap g M) := by
  refine ⟨?_, (conj_gmap g b M).2 hb.2⟩
  rw [mul_assoc]
  exact adapt_mul (adapt_mul (adapt_inv hg) hb.1) hg

theorem gdat_iff_iotaCompat : ∀ (D : D7) (T T' : D.host.E) (F0 F : LFlag (D.sp.Y 0) D.R.rS T) (F0' F' : LFlag (D.sp.Y 0) D.R.rS T') (lam lam' Λ : LV D) (γ g h b₁ b₂ : GV D), γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → Formalism.HermitianLatticesTheory.gmap γ lam' = lam → Adapt g F0 F → Adapt g (mapLF γ F0') F' → Λ = Formalism.HermitianLatticesTheory.gmap g lam → b₁ ∈ Aut0 F0 lam → b₂ ∈ Aut0 F0' lam' → h ∈ H0 F F' → (∀ x ∈ orth (VS D) (Xsp F), h x - (g * b₁ * g⁻¹) x ∈ Xsp F) → (∀ x ∈ orth (VS D) (Xsp F'), h x - (g * γ * b₂ * γ⁻¹ * g⁻¹) x ∈ Xsp F') → (gdat F F' (Formalism.HermitianLatticesTheory.gmap h Λ) = gdat F F' Λ ↔ IotaCompat lam F0 (mapLF γ F0') (mapLF (b₁ * γ * b₂⁻¹) F0') (b₁ * γ * b₂⁻¹ * γ⁻¹) (gS D)) := by
  intro D T T' F0 F F0' F' lam lam' Λ γ g h b₁ b₂ hγ hlam hg hg' hΛ hb₁ hb₂ hh hc hc'
  have hγa : Adapt γ F0' (mapLF γ F0') := adapt_mapLF hγ
  have hc₂ : γ * b₂ * γ⁻¹ ∈ Aut0 (mapLF γ F0') lam := by
    have := aut_conj hγa hb₂
    rwa [hlam] at this
  have hA := aut_conj hg hb₁
  have hA' := aut_conj hg' hc₂
  have e1 : g * γ * b₂ * γ⁻¹ * g⁻¹ = g * (γ * b₂ * γ⁻¹) * g⁻¹ := by group
  rw [e1] at hc'
  subst hΛ
  rw [gdat_iff hA hA' (frameAdaptedIsometry_of_fixing_both_frames hh).1 (frameAdaptedIsometry_of_fixing_both_frames hh).2 hc hc', lrep_adapt hg, lrep_adapt hg', ngx_adapt hg hg']
  have hi : b₁ * γ * b₂⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hb₁.1.1 hγ) (Subgroup.inv_mem _ hb₂.1.1)
  have hβ : Adapt (b₁ * γ * b₂⁻¹ * (b₂ * γ⁻¹)) (mapLF γ F0') (mapLF (b₁ * γ * b₂⁻¹) F0') :=
    adapt_mul (adapt_mul (adapt_inv hγa) hb₂.1) (adapt_mapLF hi)
  have e2 : b₁ * γ * b₂⁻¹ * (b₂ * γ⁻¹) = b₁ := by group
  rw [e2] at hβ
  have hN := ngx_adapt hb₁.1 hβ lam (gS D)
  rw [hb₁.2] at hN
  have e3 : b₁ * γ * b₂⁻¹ * γ⁻¹ = b₁ * (γ * b₂ * γ⁻¹)⁻¹ := by group
  unfold IotaCompat
  rw [hN, e3]
  generalize γ * b₂ * γ⁻¹ = c at hc₂ ⊢
  have e4 : ∀ x, (b₁ * c⁻¹) (c x) = b₁ x := fun x => by
    change b₁ (c.symm (c x)) = _
    rw [LinearEquiv.symm_apply_apply]
  constructor
  · intro H x' hx' l hl
    obtain ⟨y, rfl⟩ := c.surjective x'
    obtain ⟨m, rfl⟩ := b₁.surjective l
    rw [aut_lrep hc₂] at hx'
    rw [aut_lrep hb₁] at hl
    have := H (g y) ((gmap_apply_mem _ _ _).2 hx') (g m) ((gmap_apply_mem _ _ _).2 hl)
    simp only [conj_apply, LinearEquiv.symm_apply_apply, ← map_sub, gmap_apply_mem] at this
    rw [e4, ← map_sub, gmap_apply_mem]
    exact this.symm
  · intro H x' hx' l hl
    obtain ⟨y, rfl⟩ := g.surjective x'
    obtain ⟨m, rfl⟩ := g.surjective l
    rw [gmap_apply_mem] at hx' hl
    have := H (c y) ((aut_lrep hc₂ y).2 hx') (b₁ m) ((aut_lrep hb₁ m).2 hl)
    rw [e4, ← map_sub, gmap_apply_mem] at this
    simp only [conj_apply, LinearEquiv.symm_apply_apply, ← map_sub, gmap_apply_mem]
    exact this.symm

end GlobalTheory.GdatIota
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairIsometryUniqueOnOrthModIsotropic
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.BetaUniq

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem keeps_orth {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (P : Submodule E S.V)
    (hP : ∀ x ∈ P, γ x ∈ P) : ∀ x ∈ orth S P, γ x ∈ orth S P := by
  have hle : P.map (γ : S.V →ₗ[E] S.V) ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact hP x hx
  have heq : P.map (γ : S.V →ₗ[E] S.V) = P :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq γ P)
  have hiso : ∀ x y, S.hT (γ x) (γ y) = S.hT x y := hγ
  intro x hx
  rw [Formalism.MainNotions.mem_orth_iff] at hx ⊢
  intro y hy
  rw [← heq] at hy
  obtain ⟨y, hy, rfl⟩ := hy
  exact (hiso y x).trans (hx y hy)

theorem exists_of_mem_gsmul {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {a : S.V}
    (h : a ∈ Ideal.span {(g : 𝓞 E)} • Λ) : ∃ l ∈ Λ, a = (g : E) • l := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨b, hb, rfl⟩ := h
  refine ⟨b, hb, ?_⟩
  rw [← algebraMap_smul E (g : 𝓞 E) b, map_natCast]

theorem gsmul_mem {Λ : Submodule (𝓞 E) S.V} (g : ℕ) {l : S.V} (hl : l ∈ Λ) :
    (g : E) • l ∈ Ideal.span {(g : 𝓞 E)} • Λ := by
  rw [← map_natCast (algebraMap (𝓞 E) E) g, algebraMap_smul]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hl

theorem int_pair {Λ : Submodule (𝓞 E) S.V} (hu : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) :
    ∀ x ∈ Λ, ∀ y ∈ Λ, S.hT x y ∈ (1 : Submodule (𝓞 E) E) := fun x hx y hy => by
  rw [← hu, Formalism.HermitianLatticesTheory.dualBasic_mem_dual] at hy
  exact hy x hx

theorem exists_sub_smul_mem_orth {r : ℕ} {T' : E} (A : LFlag S r T') (hT : T' ≠ 0) :
    ∀ x ∈ orth S (Xsp A), ∃ a : E, x - a • A.fl.z ∈ orth S (Xplus A) := by
  intro x hx
  rw [Formalism.MainNotions.mem_orth_iff] at hx
  refine ⟨S.hT A.fl.z x / (-T'), ?_⟩
  rw [Formalism.MainNotions.mem_orth_iff]
  refine Formalism.MainNotions.hT_zero_of_mem_Xplus A.fl (fun a => ?_) ?_
  · rw [map_sub, map_smul, A.fl.z_orth, smul_zero, sub_zero]
    exact hx _ (Submodule.subset_span ⟨a, rfl⟩)
  · rw [map_sub, map_smul, A.fl.z_norm, smul_eq_mul, div_mul_cancel₀ _ (neg_ne_zero.2 hT), sub_self]

end GlobalTheory.LoopC.BetaUniq

namespace GlobalTheory.LoopC.BetaUniq

theorem main : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E)
    (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (A B : LFlag S r T')
    (β₁ β₂ : S.V ≃ₗ[E] S.V), Submodule.IsLattice E Λ → Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → 3 ≤ g → T' ≠ 0 →
    (∀ x ∈ orth S (Xplus A), x ∉ Xsp A → 0 < Algebra.trace ℚ E (S.hT x x)) →
    XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ A →
    XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ B →
    IsAutLam S Λ β₁ → (Xsp A).map (β₁ : S.V →ₗ[E] S.V) = Xsp B → β₁ A.fl.z - B.fl.z ∈ Xsp B →
    IotaCompat Λ F A B β₁ g →
    IsAutLam S Λ β₂ → (Xsp A).map (β₂ : S.V →ₗ[E] S.V) = Xsp B → β₂ A.fl.z - B.fl.z ∈ Xsp B →
    IotaCompat Λ F A B β₂ g → ∀ x ∈ orth S (Xsp A), β₁ x - β₂ x ∈ Xsp B := by
  intro E _ _ _ S r T T' Λ g F A B β₁ β₂ hΛ hu hg hT' hpos hFA hFB h1a h1X h1z h1ι h2a h2X h2z h2ι
  have hg0 : (g : E) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  have hΛ₁ : ∀ x, β₁ x ∈ Λ ↔ x ∈ Λ := FrEqv.aut_mem_iff h1a
  have hΛ₂ : ∀ x, β₂ x ∈ Λ ↔ x ∈ Λ := FrEqv.aut_mem_iff h2a
  have hΛ₁' : ∀ x, β₁.symm x ∈ Λ ↔ x ∈ Λ := fun x => by
    rw [← hΛ₁ (β₁.symm x), LinearEquiv.apply_symm_apply]
  have hX₁ : ∀ x ∈ Xsp A, β₁ x ∈ Xsp B := fun x hx => h1X ▸ Submodule.mem_map_of_mem hx
  have hX₂ : ∀ x ∈ Xsp A, β₂ x ∈ Xsp B := fun x hx => h2X ▸ Submodule.mem_map_of_mem hx
  have hX₁' : ∀ y ∈ Xsp B, β₁.symm y ∈ Xsp A := fun y hy => by
    rw [← h1X] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa using hx
  set δ : S.V ≃ₗ[E] S.V := β₁⁻¹ * β₂ with hδ_def
  have hδ_apply : ∀ x, δ x = β₁.symm (β₂ x) := fun x => by
    rw [hδ_def, LinearEquiv.mul_apply, LinearEquiv.coe_inv]
  have hδ : δ ∈ Formalism.HermitianLatticesTheory.isom S.hT := mul_mem (inv_mem h1a.1) h2a.1
  have hδX : ∀ x ∈ Xsp A, δ x ∈ Xsp A := fun x hx => by
    rw [hδ_apply]; exact hX₁' _ (hX₂ x hx)
  have hδz : δ A.fl.z - A.fl.z ∈ Xsp A := by
    have e : δ A.fl.z - A.fl.z = β₁.symm (β₂ A.fl.z - β₁ A.fl.z) := by
      rw [hδ_apply, map_sub, LinearEquiv.symm_apply_apply]
    rw [e]
    refine hX₁' _ ?_
    have := (Xsp B).sub_mem h2z h1z
    convert this using 1; abel
  have hδXp : ∀ x ∈ Xplus A, δ x ∈ Xplus A := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
    rw [map_add (f := _), map_smul]
    refine (Xplus A).add_mem (Submodule.mem_sup_left (hδX a ha)) ?_
    have e : c • δ A.fl.z = c • (δ A.fl.z - A.fl.z) + c • A.fl.z := by rw [← smul_add]; congr 1; abel
    rw [e]
    exact (Xplus A).add_mem (Submodule.mem_sup_left ((Xsp A).smul_mem c hδz))
      (Submodule.mem_sup_right (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)))
  set U : Submodule E S.V := orth S (Xplus A) with hU_def
  have hδU : ∀ x ∈ U, δ x ∈ U := keeps_orth hδ _ hδXp
  have hXU : Xsp A ≤ U := Formalism.MainNotions.X_le_orth_Xplus A.fl
  have hrad : ∀ x ∈ Xsp A, ∀ y ∈ U, S.hT x y = 0 := fun x hx y hy =>
    (Formalism.MainNotions.mem_orth_iff _ _).1 hy x (Submodule.mem_sup_left hx)
  have hrad' : ∀ y ∈ U, ∀ x ∈ Xsp A, S.hT y x = 0 := fun y hy x hx =>
    Formalism.MainNotions.hT_swap_zero (hrad x hx y hy)
  set M : Submodule (𝓞 E) S.V := Λ ⊓ toO S U with hM_def
  have hM : ∀ x, x ∈ M ↔ x ∈ Λ ∧ x ∈ U := fun x => Iff.rfl
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hΛ.fg
  have hMfg : M.FG := Submodule.FG.of_le_of_isNoetherian (T := Λ) inf_le_left
  have hint := int_pair hu
  have hUXA : U ≤ orth S (Xsp A) := fun y hy => by
    rw [Formalism.MainNotions.mem_orth_iff] at hy ⊢
    exact fun x hx => hy x (Submodule.mem_sup_left hx)

  have hcong : ∀ x ∈ M, ∃ y ∈ M, δ x - x - (g : E) • y ∈ Xsp A := by
    intro x hx
    obtain ⟨hxΛ, hxU⟩ := (hM x).1 hx

    obtain ⟨l', hl'Λ, hl'⟩ := GlobalTheory.Mass.RowPerp.exists_sub_mem S.herm S.nondeg hΛ hu (orth S (Xsp F))
      ((g : E)⁻¹ • x) (fun y hyΛ hy => by
        have hyX : y ∈ Xsp F := GlobalTheory.Mass.RowPerp.mem_of_perp_perp S.nondeg (Xsp F) y fun w hw =>
          Formalism.MainNotions.hT_swap_zero (hy w ((Formalism.MainNotions.mem_orth_iff _ _).2 hw))
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hFA (Submodule.mem_inf.2 ⟨hyΛ, hyX⟩))
        obtain ⟨l, hlΛ, rfl⟩ := exists_of_mem_gsmul ha
        obtain ⟨t, ht⟩ := Submodule.mem_one.1 (hint x hxΛ l hlΛ)
        refine Submodule.mem_one.2 ⟨t, ?_⟩
        rw [LinearMap.map_smulₛₗ S.hT, LinearMap.smul_apply, map_add (f := _), map_smul,
          hrad' x hxU b (Submodule.mem_inf.1 hb).2, add_zero, starRingEnd_apply, star_inv₀, star_natCast,
          smul_eq_mul, smul_eq_mul, ht, inv_mul_cancel_left₀ hg0])
    set l : S.V := x - (g : E) • l' with hl_def
    have hlΛ : l ∈ Λ := by
      rw [hl_def, ← map_natCast (algebraMap (𝓞 E) E) g, algebraMap_smul]
      exact Λ.sub_mem hxΛ (Λ.smul_mem _ hl'Λ)
    have hlF : l ∈ Lrep Λ F := by
      refine Submodule.mem_inf.2 ⟨hlΛ, ?_⟩
      have e : l = (g : E) • ((g : E)⁻¹ • x - l') := by
        rw [hl_def, smul_sub, smul_smul, mul_inv_cancel₀ hg0, one_smul]
      rw [e]
      exact (orth S (Xsp F)).smul_mem _ hl'
    have hlx : l - x ∈ NgX Λ g F A := by
      have e : l - x = (g : E) • (-l') := by rw [hl_def, smul_neg]; abel
      rw [e]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (gsmul_mem g (Λ.neg_mem hl'Λ)))
    have hxA : x ∈ Lrep Λ A := Submodule.mem_inf.2 ⟨hxΛ, hUXA hxU⟩
    have hb1 : l - β₁ x ∈ NgX Λ g F B := (h1ι x hxA l hlF).1 hlx
    have hb2 : l - β₂ x ∈ NgX Λ g F B := (h2ι x hxA l hlF).1 hlx
    have hdiff : β₂ x - β₁ x ∈ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ B := by
      have hle : NgX Λ g F B ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ B :=
        sup_le (sup_le le_sup_left hFB) le_sup_right
      have := (NgX Λ g F B).sub_mem hb1 hb2
      refine hle ?_
      convert this using 1; abel
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hdiff
    obtain ⟨lam, hlam, rfl⟩ := exists_of_mem_gsmul ha
    have hbA : β₁.symm b ∈ Xsp A := hX₁' b (Submodule.mem_inf.1 hb).2
    have key : δ x - x - (g : E) • β₁.symm lam = β₁.symm b := by
      have e : b = (β₂ x - β₁ x) - (g : E) • lam := by rw [← hab]; abel
      rw [e, map_sub, map_sub, map_smul, LinearEquiv.symm_apply_apply, hδ_apply]
    refine ⟨β₁.symm lam, (hM _).2 ⟨(hΛ₁' lam).2 hlam, ?_⟩, ?_⟩
    · have e : β₁.symm lam = (g : E)⁻¹ • (δ x - x - β₁.symm b) := by
        rw [← key, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hg0, one_smul]
      rw [e]
      exact U.smul_mem _ (U.sub_mem (U.sub_mem (hδU x hxU) hxU) (hXU hbA))
    · rw [key]; exact hbA
  have hmain : ∀ x ∈ M, δ x - x ∈ Xsp A :=
    GlobalTheory.isom_sub_mem_of_congr E S.V S.hT U (Xsp A) M δ g S.herm hXU hrad hpos hMfg
      (fun x hx => ((hM x).1 hx).2) hδ hδX hg hcong

  have hext : ∀ x ∈ orth S (Xsp A), δ x - x ∈ Xsp A := by
    intro x hx
    obtain ⟨a, hy⟩ := exists_sub_smul_mem_orth A hT' x hx
    set y := x - a • A.fl.z with hy_def
    have hfull : Submodule.IsFullLattice E Λ :=
      { toIsLattice := hΛ, span_eq_top := GlobalTheory.LoopC.FunIdx.span_eq_top_of_unimodular Λ hΛ hu }
    obtain ⟨d, hd0, hd⟩ := GlobalTheory.Mass.RowPerp.exists_smul_mem hfull y
    have hdM : d • y ∈ M := (hM _).2 ⟨hd, by
      rw [← algebraMap_smul E d y]; exact U.smul_mem _ hy⟩
    have h1 := hmain _ hdM
    rw [← algebraMap_smul E d y, map_smul, ← smul_sub] at h1
    have hyX : δ y - y ∈ Xsp A :=
      (Submodule.smul_mem_iff _ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)).1 h1
    have e : δ x - x = a • (δ A.fl.z - A.fl.z) + (δ y - y) := by
      rw [hy_def, map_sub, map_smul, smul_sub]; abel
    rw [e]
    exact (Xsp A).add_mem ((Xsp A).smul_mem a hδz) hyX
  intro x hx
  have e : β₁ x - β₂ x = -(β₁ (δ x - x)) := by
    rw [hδ_apply, map_sub, LinearEquiv.apply_symm_apply, neg_sub]
  rw [e]
  exact (Xsp B).neg_mem (hX₁ _ (hext x hx))

end GlobalTheory.LoopC.BetaUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PostOnMemGoodPart
section
noncomputable section

open Formalism.MainNotions.ArithmeticCylinders IsDedekindDomain MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped InnerProductSpace TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultTranslate

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}
  {θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}

theorem isCuspFun_rTr {φ : GA D V → ℂ} (h : IsCuspFun V φ) (x : GA D V) : IsCuspFun V (rTr V x φ) := by
  intro r C hC μ 𝓕 hμ h𝓕 g
  simpa only [rTr, mul_assoc] using h r C hC μ 𝓕 hμ h𝓕 (g * x)

theorem isMultMap_rTr {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} {x : GA D V} (hx : x ∈ GfC V)
    (hJ : ∀ k ∈ J', x⁻¹ * k * x ∈ J ∧ χ' k = χ (x⁻¹ * k * x)) {T : MMap M} (h : IsMultMap θ M J χ T) :
    IsMultMap θ M J' χ' (postOn M (GlobalTheory.FinTranslate.rTrL V x) T) := by
  constructor
  · intro v
    exact GlobalTheory.FinTranslate.isAutFunSm_rTr θ V x hx _ (h.aut v)
  · intro v
    exact isCuspFun_rTr (h.cusp v) x
  · intro v k hk g
    change T v (g * k * x) = χ' k * T v (g * x)
    rw [(hJ k hk).2, ← h.lev v _ (hJ k hk).1]
    group
  · intro τ g hg v w hw
    funext y
    change T (Function.update v τ w) (y * x) = T v (y * atTau θ V τ g * x)
    rw [h.equiv τ g hg v w hw, mul_assoc,
      ← GlobalTheory.FinTranslate.comm_fin_real V hx (GlobalTheory.FinTranslate.atTau_mem θ V τ g), ← mul_assoc]
    rfl
  · intro τ v y
    exact h.cont τ v (y * x)

theorem postOn_mem_goodPart {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} {x : GA D V} (hx : x ∈ GfC V)
    (hJ : ∀ k ∈ J', x⁻¹ * k * x ∈ J ∧ χ' k = χ (x⁻¹ * k * x)) {L L' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)}
    (hL : ∀ f, L' (rTr V x f) = rTr V x (L f)) {T : MMap M} (h : T ∈ goodPart θ M J χ L) :
    postOn M (GlobalTheory.FinTranslate.rTrL V x) T ∈ goodPart θ M J' χ' L' := by
  rw [mem_goodPart, GlobalTheory.MultMem.mem_mult_iff] at h ⊢
  refine ⟨isMultMap_rTr hx hJ h.1, fun v => ?_⟩
  change L' (rTr V x (T v)) = rTr V x (T v)
  rw [hL, h.2]

end GlobalTheory.MultTranslate

end
end

