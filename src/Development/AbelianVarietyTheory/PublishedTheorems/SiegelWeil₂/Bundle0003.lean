module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
section
noncomputable section

open scoped Matrix NNReal Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.PolesModel

open GlobalTheory.StdUnn GlobalTheory.StdUnn.HeightExists GlobalTheory.Eis

variable {D : D7} {n : ℕ}

def detP : P D n →* (AE D)ˣ := Matrix.GeneralLinearGroup.det.comp leviBlock

def modP : P D n →* ℝ≥0 := (absA D).comp detP

theorem continuous_modP : Continuous (modP (D := D) (n := n)) :=
  continuous_absE.comp (continuous_detGL.comp continuous_leviBlock)

theorem isIwasawa : IsIwasawa (modP (D := D) (n := n)) (K D n) :=
  haveI := t2Space_adeleRing' (F := D.host.F)
  isIwasawa_of_isCompact isClosed_P continuous_modP isCompact_K fun g =>
    let ⟨p, hp, k, hk, e⟩ := Iwasawa.exists_mul D n g; ⟨⟨p, hp⟩, k, hk, e⟩

theorem height_eq {H : G D n → ℝ≥0} (h : IsHeight H) : H = iwAbs modP (K D n) := funext fun g => by
  obtain ⟨p, k, hk, rfl⟩ := isIwasawa.1 g
  rw [isIwasawa.iwAbs_mul p hk]
  exact h p p.2 (leviBlock (D := D) (n := n) p) rfl k hk

theorem isSection_iff {χ : (AE D)ˣ →* Circle} {s : ℂ} {φ : G D n → ℂ} :
    IsSection χ s φ ↔ φ ∈ indSpace modP (K D n) (χ.comp detP) (s + (n : ℂ) / 2) := by
  refine and_congr_left fun _ => ⟨fun h p g => h p p.2 (leviBlock (D := D) (n := n) p) rfl g, fun h p hp a ha g => ?_⟩
  rw [show a = leviBlock (D := D) (n := n) ⟨p, hp⟩ from Units.ext ha.symm]
  exact h ⟨p, hp⟩ g

theorem isSection_stdSec {χ : (AE D)ˣ →* Circle} {H : G D n → ℝ≥0} (h : IsHeight H) {s₁ : ℂ} {φ : G D n → ℂ}
    (hφ : IsSection χ s₁ φ) (s : ℂ) : IsSection χ s (stdSec H φ s₁ s) := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  rw [height_eq h, isSection_iff]
  exact isIwasawa.flatSec_mem isClosed_P continuous_modP isCompact_K (isSection_iff.1 hφ) s

theorem hypotheses_hold (D : D7) (n k : ℕ) (s₁ : ℂ) : ∃ (H : G D n → ℝ≥0) (φ : G D n → ℂ),
    IsHeckeChar D 1 ∧ ResEta D 1 (2 * k) ∧ IsHeight H ∧ IsSection 1 s₁ φ ∧ ∀ g, φ g ≠ 0 := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  obtain ⟨H, hH⟩ := exists_height D n
  refine ⟨H, fun g => npow (iwAbs modP (K D n) g) (s₁ + (n : ℂ) / 2), ⟨continuous_const, fun _ => rfl⟩,
    SimplePoleModel.resEta_one_two_mul D k, hH, isSection_iff.2 ?_, fun g => npow_ne_zero (iwAbs_pos _ _ g) _⟩
  exact isIwasawa.npow_iwAbs_mem isClosed_P continuous_modP isCompact_K _

theorem summable_of_rank (A : HSp D) (τ : ℝ) (hτ : (A.rank : ℝ) / 2 < τ) : Summable fun q =>
    ((term (P D A.rank) (GF D A.rank) (iwAbs modP (K D A.rank)) 1 q : ℝ≥0) : ℝ) ^ (τ + (A.rank : ℝ) / 2) := by
  obtain ⟨μ, hμ, hconj⟩ := GlobalTheory.StdUnn.ConjElt.exists_isConj D
  obtain ⟨κ, hκ⟩ := chart_exists D A μ hμ
  obtain ⟨a, ha⟩ := exists_isMaj A
  obtain ⟨p, hp⟩ := hconj A a ha κ hκ
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha
  have hf := ((sphConv_iff hI).1 (sphConv D A a hI)).1 τ hτ
  have hH := height_eq (isHeight_hgtStd D A μ hμ κ hκ a p hp)
  have := (cosetSum_along_mulEquiv _ _ κ.symm (P D A.rank) (GF D A.rank) (siegel A) (GQ (dblSp A))
    (fun g => by rw [mem_siegel_iff_chart_mem_P D A μ hμ κ hκ, MulEquiv.apply_symm_apply])
    (fun g => by rw [chart_mem_GF_iff D A μ hμ κ hκ, MulEquiv.apply_symm_apply])
    (sph A a τ) (κ (p : GA D (dblSp A))⁻¹) (npow (absA D (aP A p)) (τ + (A.rank : ℂ) / 2))
    (fun g => npow (hgtStd A a κ p g) (τ + (A.rank : ℂ) / 2))
    (fun g => by rw [hgtStd, npow_mul, map_mul, MulEquiv.symm_apply_apply, sph, mul_comm]) hf.1).2 1
  refine (this.1 (hf.2 _)).congr fun q => ?_
  simp only [term, hH]
  rw [norm_npow (iwAbs_pos _ _ _)]
  simp

theorem summable_spherical (τ : ℝ) (hτ : (n : ℝ) / 2 < τ) : Summable fun q =>
    ((term (P D n) (GF D n) (iwAbs modP (K D n)) 1 q : ℝ≥0) : ℝ) ^ (τ + (n : ℝ) / 2) :=
  summable_of_rank (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral n) τ hτ

theorem cosetConv_stdSec {χ : (AE D)ˣ →* Circle} {H : G D n → ℝ≥0} (h : IsHeight H) {s₁ : ℂ} {φ : G D n → ℂ}
    (hφ : IsSection χ s₁ φ) {s : ℂ} (hs : (n : ℝ) / 2 < s.re) (g : G D n) :
    CosetConv (P D n) (GF D n) (stdSec H φ s₁ s) g := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  have h1 : Continuous (iwAbs modP (K D n)) := isIwasawa.continuous_iwAbs isClosed_P continuous_modP isCompact_K
  have h2 : Continuous fun g => Real.log (iwAbs modP (K D n) g) :=
    (NNReal.continuous_coe.comp h1).log fun g => (NNReal.coe_pos.2 (iwAbs_pos _ _ g)).ne'
  refine cosetConv_of_spherical (χ := χ.comp detP) (ρ := (n : ℝ) / 2) isIwasawa isCompact_K (Continuous.continuousOn ?_)
    (fun z _ => ?_) summable_spherical hs g
  · simp only [stdSec, height_eq h, npow_eq_exp (iwAbs_pos _ _ _)]
    exact (hφ.2.1.comp continuous_snd).mul (((Complex.continuous_ofReal.comp (h2.comp continuous_snd)).mul
      (continuous_fst.sub continuous_const)).cexp)
  · have := (isSection_iff.1 (isSection_stdSec h hφ z)).1
    push_cast
    exact this

end GlobalTheory.StdUnn.PolesModel

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelSectionLeviMulEqAbsDetPow
section
noncomputable section

open scoped Matrix NNReal TensorProduct Classical ComplexOrder
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RegSch

namespace GlobalTheory.Published.SiegelSectionIwasawa

variable {D : D7}

private theorem isFullLattice_of_good {V : HSp D} {l : Lvl V} (hl : l.Good) :
    Submodule.IsFullLattice D.host.E l.L := by
  exact hl.1

def relat (V : HSp D) (l : Lvl V) (hl : l.Good) : HSp D :=
  { V with
    L0 := l.L.comap (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))
    standardTuple_isLattice := by
      have e : l.L.comap (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E)) =
          l.L.map (V.frame.equivFun.symm.toLinearMap.restrictScalars (𝓞 D.host.E)) := by
        ext x
        constructor
        · intro hx; exact ⟨_, hx, V.frame.equivFun.symm_apply_apply x⟩
        · rintro ⟨y, hy, rfl⟩
          change V.frame.equivFun (V.frame.equivFun.symm y) ∈ l.L
          rwa [LinearEquiv.apply_symm_apply]
      rw [e]
      exact Submodule.IsLattice.of_fg D.host.E (hl.1.fg.map _)
    baseLattice_isUnimodular := by
      have h := (SelfDual.forall_isSelfDualAt_iff
        (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero
        (isFullLattice_of_good hl)).1 hl.2.1
      have e : ∀ x y, hE D.sp.cm.sig V.gram (V.frame.equivFun x) (V.frame.equivFun y) = V.hT x y := fun x y => by
        rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]
        simp only [← Module.Basis.equivFun_apply]
        rfl
      ext z
      have h2 : z ∈ Formalism.HermitianLatticesTheory.dual V.hT (l.L.comap (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))) ↔
          ∀ x ∈ l.L.comap (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E)),
            V.hT x z ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
        simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual]
      refine h2.trans (Iff.trans ?_ (h (V.frame.equivFun z)).symm)
      constructor
      · intro H x hx
        obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective x
        rw [e]
        exact Submodule.mem_one.1 (H x hx)
      · intro H x hx
        rw [← e]
        exact Submodule.mem_one.2 (H _ hx) }

theorem frameLat_relat (V : HSp D) (l : Lvl V) (hl : l.Good) : frameLat (relat V l hl) = l.L := by
  ext y
  exact iff_of_eq (congrArg (· ∈ l.L) (V.frame.equivFun.apply_symm_apply y))

theorem hasIw_of_good {V V₀ : HSp D} {r : ℕ} (d : HypDec V V₀ r) (l : Lvl V) (hl : l.Good) : HasIw d l.K := by
  let d' : HypDec (relat V l hl) V₀ r := ⟨d.e, d.e', d.i₀, d.ee, d.e'e', d.e'e, d.iso, d.i₀e, d.i₀e', d.rank_add⟩
  have h := GlobalTheory.Core.Rk.IwAd.hasIw_Kmax D (relat V l hl) V₀ r d' l.c GlobalTheory.Core.Rk.IP.Model.isSplit_two hl.2.2
  intro g
  obtain ⟨q, k, hk, e⟩ := h g
  have e2 : (Kmax (relat V l hl) l.c : Subgroup (GA D V)) = l.K :=
    congrArg (fun L => levelAll D.sp.cm.sig V.gram L l.c) (frameLat_relat V l hl)
  exact ⟨⟨q.1, q.2⟩, k, e2 ▸ hk, e⟩

section Arch

variable {m k r : ℕ} {X Y : Matrix (Fin m) (Fin r) ℂ} {Z : Matrix (Fin m) (Fin k) ℂ} {P R : Matrix (Fin r) (Fin m) ℂ}
  {Q : Matrix (Fin k) (Fin m) ℂ} {G : Matrix (Fin m) (Fin m) ℂ} {G₀ s₀ B B' : Matrix (Fin k) (Fin k) ℂ}

end Arch

section Standard

variable {V V₀ : HSp D} {r : ℕ} (d : HypDec V V₀ r)

variable {L₀ : Submodule (𝓞 D.host.E) (Fin V₀.rank → D.host.E)}

end Standard

end GlobalTheory.Published.SiegelSectionIwasawa

end
end

