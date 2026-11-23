module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0200
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RangeBesselAnisotropicEmbeddingEqSecondModelSubg
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.AdBridge GlobalTheory.BesselChar

noncomputable section

namespace GlobalTheory.Core.SBesLevi

variable {D : D7}

theorem bridge_fix (D : D7) (g : GA D (D.sp.Y 0)) (x : Fin (Formalism.L2.SG.InstExistsPf.instOf D).n → (Formalism.L2.SG.InstExistsPf.instOf D).E) :
    (mt (D.sp.Y 0) g *ᵥ (fun k => incA D (x k)) = fun k => incA D (x k)) ↔
    ((∀ v, uMat ((Formalism.IndefR.RationalEmbedding.iota D g).1 v) *ᵥ rv (Formalism.L2.SG.InstExistsPf.instOf D) v x = rv (Formalism.L2.SG.InstExistsPf.instOf D) v x) ∧
      (Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 *ᵥ incl (Formalism.L2.SG.InstExistsPf.instOf D) x = incl (Formalism.L2.SG.InstExistsPf.instOf D) x) := by
  have hb := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D g)
  have key : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D g) = g :=
    (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply g
  have hb1 : ∀ v, uMat ((Formalism.IndefR.RationalEmbedding.iota D g).1 v) = ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) g v :=
    fun v => (hb.1 v).trans (congrArg (fun q => ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) q v) key)
  have hb2 : (Formalism.IndefR.RationalEmbedding.inst D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 = ofHAFin (Formalism.IndefR.RationalEmbedding.inst D) g :=
    hb.2.trans (congrArg (fun q => ofHAFin (Formalism.IndefR.RationalEmbedding.inst D) q) key)
  have hdet : ∀ v, IsUnit ((Formalism.L2.SG.InstExistsPf.instOf D).P v).det :=
    fun v => (Matrix.isUnit_iff_isUnit_det _).1 ((Formalism.L2.SG.InstExistsPf.instOf D).P_unit v)
  have hinf : ∀ v, (uMat ((Formalism.IndefR.RationalEmbedding.iota D g).1 v) *ᵥ rv (Formalism.L2.SG.InstExistsPf.instOf D) v x = rv (Formalism.L2.SG.InstExistsPf.instOf D) v x) ↔
      ∀ i, thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) i) =
        thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v (incA D (x i)) := by
    intro v
    have hθ : (hmat (Formalism.L2.SG.InstExistsPf.instOf D) g).map (thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v) *ᵥ
        (fun i => (Formalism.L2.SG.InstExistsPf.instOf D).φ v (x i)) =
        fun i => thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) i) := by
      funext i
      refine Eq.trans ?_ (RingHom.map_mulVec (thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v) (hmat (Formalism.L2.SG.InstExistsPf.instOf D) g) (fun k => incA D (x k)) i).symm
      congr 1
      funext k
      exact (GlobalTheory.Core.SBesFlagTie.thetaV_incA v (x k)).symm
    have hφ : (fun i => (Formalism.L2.SG.InstExistsPf.instOf D).φ v (x i)) =
        fun i => thetaV (Formalism.L2.SG.InstExistsPf.instOf D) v (incA D (x i)) :=
      funext fun i => (GlobalTheory.Core.SBesFlagTie.thetaV_incA v (x i)).symm
    rw [hb1 v]
    unfold ofHAInf rv
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hdet v), Matrix.mul_one,
      ← Matrix.mulVec_mulVec, hθ, hφ]
    constructor
    · intro h i
      have := congrArg (fun w => (Formalism.L2.SG.InstExistsPf.instOf D).P v *ᵥ w) h
      simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hdet v), Matrix.one_mulVec] at this
      exact congrFun this i
    · intro h
      rw [funext h]
  have hfin : ((Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 *ᵥ incl (Formalism.L2.SG.InstExistsPf.instOf D) x =
      incl (Formalism.L2.SG.InstExistsPf.instOf D) x) ↔
      ∀ i, tauF (Formalism.L2.SG.InstExistsPf.instOf D) ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) i) =
        tauF (Formalism.L2.SG.InstExistsPf.instOf D) (incA D (x i)) := by
    have hτ : (hmat (Formalism.L2.SG.InstExistsPf.instOf D) g).map (tauF (Formalism.L2.SG.InstExistsPf.instOf D)) *ᵥ
        incl (Formalism.L2.SG.InstExistsPf.instOf D) x =
        fun i => tauF (Formalism.L2.SG.InstExistsPf.instOf D) ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) i) := by
      funext i
      refine Eq.trans ?_ (RingHom.map_mulVec (tauF (Formalism.L2.SG.InstExistsPf.instOf D)) (hmat (Formalism.L2.SG.InstExistsPf.instOf D) g) (fun k => incA D (x k)) i).symm
      congr 1
      funext k
      exact (GlobalTheory.Core.SBesFlagTie.tauF_incA (x k)).symm
    have hi : incl (Formalism.L2.SG.InstExistsPf.instOf D) x = fun i => tauF (Formalism.L2.SG.InstExistsPf.instOf D) (incA D (x i)) :=
      funext fun i => (GlobalTheory.Core.SBesFlagTie.tauF_incA (x i)).symm
    have e1 := hb2
    unfold ofHAFin at e1
    change (Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 = _ at e1
    rw [e1, hτ, hi]
    exact funext_iff
  rw [hfin, forall_congr' hinf]
  change ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) = fun k => incA D (x k)) ↔ _
  constructor
  · intro h
    exact ⟨fun v i => by rw [congrFun h i], fun i => by rw [congrFun h i]⟩
  · rintro ⟨h1, h2⟩
    funext i
    have := Formalism.L2.SG.Pf.TT_ext (Formalism.L2.SG.InstExistsPf.instOf D)
      ((hmat (Formalism.L2.SG.InstExistsPf.instOf D) g *ᵥ fun k => incA D (x k)) i - (show AF (Formalism.L2.SG.InstExistsPf.instOf D).F ⊗[(Formalism.L2.SG.InstExistsPf.instOf D).F] (Formalism.L2.SG.InstExistsPf.instOf D).E from incA D (x i)))
      (fun v => by rw [map_sub, h1 v i, sub_self]) (by rw [map_sub, h2 i, sub_self])
    exact sub_eq_zero.1 this

theorem transport_fix (D : D7) (I : AutInst) (ιE : I.E ≃+* D.host.E) (hId : ∀ y, HEq (ιE y) y)
    (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (hr : (D.sp.Y 0).rank = I.n) (S : Set (Fin I.n → I.E))
    (s : (Formalism.L2.SG.InstExistsPf.instOf D).GA) :
    ((castGA hI.symm s).1 ∈ Formalism.L2.SG.PoincareInHH.HinfS I S ∧ (castGA hI.symm s).2 ∈ Formalism.L2.SG.PoincareInHH.HfinS I S) ↔
    ∀ p ∈ S, (∀ v, uMat (s.1 v) *ᵥ rv (Formalism.L2.SG.InstExistsPf.instOf D) v (fun k => ιE (p (Fin.cast hr k))) =
        rv (Formalism.L2.SG.InstExistsPf.instOf D) v (fun k => ιE (p (Fin.cast hr k)))) ∧
      (Formalism.L2.SG.InstExistsPf.instOf D).fmat s.2 *ᵥ incl (Formalism.L2.SG.InstExistsPf.instOf D) (fun k => ιE (p (Fin.cast hr k))) =
        incl (Formalism.L2.SG.InstExistsPf.instOf D) (fun k => ιE (p (Fin.cast hr k))) := by
  generalize hI.symm = e
  subst hI
  have hid : ∀ y, ιE y = y := fun y => eq_of_heq (hId y)
  have hv : ∀ p : Fin (Formalism.L2.SG.InstExistsPf.instOf D).n → (Formalism.L2.SG.InstExistsPf.instOf D).E,
      (fun k : Fin (Formalism.L2.SG.InstExistsPf.instOf D).n => ιE (p (Fin.cast hr k))) = p := fun p => funext fun k => by rw [hid]; rfl
  rw [GlobalTheory.Core.SBesFlagTie.castGA_self]
  change ((∀ v, ∀ x ∈ S, uMat (s.1 v) *ᵥ rv _ v x = rv _ v x) ∧ (∀ y ∈ S, _)) ↔ _
  constructor
  · rintro ⟨h1, h2⟩ p hp
    rw [hv p]
    exact ⟨fun v => h1 v p hp, h2 p hp⟩
  · intro H
    refine ⟨fun v p hp => ?_, fun p hp => ?_⟩
    · have := (H p hp).1 v
      rw [hv p] at this
      exact this
    · have := (H p hp).2
      rw [hv p] at this
      exact this

theorem fix_smul {S : HSp D} (g : GA D S) {c : D.host.E} (hc : c ≠ 0) (y : Fin S.rank → D.host.E) :
    (mt S g *ᵥ (fun k => incA D ((c • y) k)) = fun k => incA D ((c • y) k)) ↔
      (mt S g *ᵥ (fun k => incA D (y k)) = fun k => incA D (y k)) := by
  have hs : (fun k => incA D ((c • y) k)) = incA D c • fun k => incA D (y k) := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  have hu : IsUnit (incA D c) := (IsUnit.mk0 c hc).map (incA D)
  rw [hs, Matrix.mulVec_smul]
  exact hu.smul_left_cancel

theorem fix_cols {S : HSp D} (g : GA D S) {ρ : ℕ} (e : Matrix (Fin S.rank) (Fin ρ) D.host.E) :
    mt S g ⬝ rat e = rat e ↔ ∀ a, (mt S g *ᵥ (fun k => incA D (e k a)) = fun k => incA D (e k a)) := by
  constructor
  · intro h a
    funext k
    exact congrFun (congrFun h k) a
  · intro h
    funext k a
    exact congrFun (h a) k

theorem rat_mulVec {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (w : Fin n → D.host.E) :
    (fun k => incA D ((M *ᵥ w) k)) = rat M *ᵥ fun k => incA D (w k) := by
  funext k
  exact RingHom.map_mulVec (incA D) M w k

theorem range_embA_iff {S V₀ A L : HSp D} {ρ : ℕ} (d : HypDec S V₀ ρ) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E)
    (hζ : IsLineVec L ζ) (g : GA D S) :
    g ∈ (embA d o).range ↔ (mt S g ⬝ d.jX = d.jX ∧ mt S g ⬝ d.jY = d.jY ∧
      (mt S g *ᵥ (fun k => incA D ((d.i₀ *ᵥ vecB o ζ) k)) = fun k => incA D ((d.i₀ *ᵥ vecB o ζ) k))) := by
  have hw : (fun k => incA D (vecB o ζ k)) = o.jB *ᵥ fun k => incA D (ζ k) := rat_mulVec o.iB ζ
  rw [rat_mulVec d.i₀ (vecB o ζ)]
  change _ ↔ (_ ∧ _ ∧ mt S g *ᵥ (d.j0 *ᵥ _) = d.j0 *ᵥ _)
  constructor
  · rintro ⟨a, rfl⟩
    change mt S (d.emb0 (o.emb (a, 1))) ⬝ d.jX = d.jX ∧ mt S (d.emb0 (o.emb (a, 1))) ⬝ d.jY = d.jY ∧
      mt S (d.emb0 (o.emb (a, 1))) *ᵥ (d.j0 *ᵥ _) = d.j0 *ᵥ _
    refine ⟨d.wittDecomp_anisotropicEmbedding_inclX _, d.wittDecomp_anisotropicEmbedding_inclY _, ?_⟩
    rw [Matrix.mulVec_mulVec, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_mulVec (M := mt V₀ _), o.emb_jB,
      MixModel.mt_one, Matrix.mul_one]
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨b, rfl⟩ := GlobalTheory.T.exists_levi_preimage_of_fix_isotropic_frames d g h1 h2
    have hb : (mt V₀ b *ᵥ fun k => incA D (vecB o ζ k)) = fun k => incA D (vecB o ζ k) := by
      rw [Matrix.mulVec_mulVec, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec] at h3
      have := congrArg (fun w => d.p0 *ᵥ w) h3
      simp only [Matrix.mulVec_mulVec, d.p0_j0, Matrix.one_mulVec] at this
      simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, d.p0_j0, Matrix.one_mul] using this
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.LineFix.exists_emb_of_fix_line o ζ hζ b hb
    exact ⟨a, by rw [← ha]; rfl⟩

theorem range_embA_eq_H : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (t lam : D.host.E), t ≠ 0 → lam ≠ 0 → IdE X → ∀ (V₀ L : HSp D) (d : HypDec (D.sp.Y 0) V₀ D.R.rS) (o : OrthDec V₀ (D.sp.X 0) L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → d.e = GlobalTheory.Core.SBesEx.eM X h t lam → d.e' = GlobalTheory.Core.SBesEx.e'M X h t lam → d.i₀ *ᵥ vecB o ζ = t • GlobalTheory.Core.SBesEx.cY X h (X.zu u) → ∀ g, g ∈ (embA d o).range ↔ (iotaX X h g).1 ∈ Hinf X u ∧ (iotaX X h g).2 ∈ Hfin X u := by
  intro D X h u t lam ht hl hId V₀ L d o ζ hζ he he' hz g
  have hsc : ∀ a, GlobalTheory.Core.SBesEx.scl t lam a ≠ 0 := fun a => mul_ne_zero ht (pow_ne_zero _ hl)
  have hR : ((iotaX X h g).1 ∈ Hinf X u ∧ (iotaX X h g).2 ∈ Hfin X u) ↔
      ∀ p ∈ fixSet X u, (mt (D.sp.Y 0) g *ᵥ (fun k => incA D (X.ιE (p (Fin.cast (rank_eq X h) k)))) =
        fun k => incA D (X.ιE (p (Fin.cast (rank_eq X h) k)))) :=
    (transport_fix D X.B.I X.ιE hId h (rank_eq X h) (fixSet X u) (Formalism.IndefR.RationalEmbedding.iota D g)).trans
      (forall₂_congr fun p _ => (bridge_fix D g _).symm)
  rw [range_embA_iff d o ζ hζ g, hR, HypDec.jX, HypDec.jY, fix_cols, fix_cols]
  change _ ↔ ∀ p ∈ Set.range X.eR ∪ Set.range X.fR ∪ {X.zR u}, _
  have hE : ∀ a, (fun k => d.e k a) = GlobalTheory.Core.SBesEx.scl t lam a • GlobalTheory.Core.SBesEx.cY X h (X.eX a) := by
    intro a; funext k; rw [he]; rfl
  have hE' : ∀ a, (fun k => d.e' k a) = (star (GlobalTheory.Core.SBesEx.scl t lam a))⁻¹ • GlobalTheory.Core.SBesEx.cY X h (X.fY a) := by
    intro a; funext k; rw [he']; rfl
  have hA : ∀ a, ((mt (D.sp.Y 0) g *ᵥ fun k => incA D (d.e k a)) = fun k => incA D (d.e k a)) ↔
      ((mt (D.sp.Y 0) g *ᵥ fun k => incA D (X.ιE (X.eR a (Fin.cast (rank_eq X h) k)))) =
        fun k => incA D (X.ιE (X.eR a (Fin.cast (rank_eq X h) k)))) := fun a => by
    have := fix_smul g (hsc a) (GlobalTheory.Core.SBesEx.cY X h (X.eX a))
    rw [← hE a] at this
    exact this
  have hB : ∀ a, ((mt (D.sp.Y 0) g *ᵥ fun k => incA D (d.e' k a)) = fun k => incA D (d.e' k a)) ↔
      ((mt (D.sp.Y 0) g *ᵥ fun k => incA D (X.ιE (X.fR a (Fin.cast (rank_eq X h) k)))) =
        fun k => incA D (X.ιE (X.fR a (Fin.cast (rank_eq X h) k)))) := fun a => by
    have := fix_smul g (inv_ne_zero (star_ne_zero.2 (hsc a))) (GlobalTheory.Core.SBesEx.cY X h (X.fY a))
    rw [← hE' a] at this
    exact this
  have hC : ((mt (D.sp.Y 0) g *ᵥ fun k => incA D ((d.i₀ *ᵥ vecB o ζ) k)) = fun k => incA D ((d.i₀ *ᵥ vecB o ζ) k)) ↔
      ((mt (D.sp.Y 0) g *ᵥ fun k => incA D (X.ιE (X.zR u (Fin.cast (rank_eq X h) k)))) =
        fun k => incA D (X.ιE (X.zR u (Fin.cast (rank_eq X h) k)))) := by
    have := fix_smul g ht (GlobalTheory.Core.SBesEx.cY X h (X.zu u))
    rw [← hz] at this
    exact this
  simp only [hA, hB, hC]
  constructor
  · rintro ⟨h1, h2, h3⟩ p hp
    rcases hp with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hp
    · exact h1 a
    · exact h2 a
    · rw [Set.mem_singleton_iff] at hp
      subst hp
      exact h3
  · intro H
    exact ⟨fun a => H _ (Or.inl (Or.inl ⟨a, rfl⟩)), fun a => H _ (Or.inl (Or.inr ⟨a, rfl⟩)), H _ (Or.inr rfl)⟩

end GlobalTheory.Core.SBesLevi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorant
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SchwartzMaj

variable {D : D7}

theorem finPart_section (D : D7) : Continuous (finPart D) ∧
    ∃ s : (Af D.host.F ⊗[D.host.F] D.host.E) → AE D, Continuous s ∧ ∀ z, finPart D (s z) = z := by
  letI ti : TopologicalSpace (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E)
  obtain ⟨e, he, hec, hes⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨?_, fun z => e.symm (0, z), hes.comp (continuous_const.prodMk continuous_id), fun z => ?_⟩
  · have : (finPart D : AE D → _) = fun z => (e z).2 := funext fun z => (he z).2.symm
    rw [this]
    exact continuous_snd.comp hec
  · rw [← (he _).2, RingEquiv.apply_symm_apply]

theorem maj_mono (θ : InfFam D) {m n : ℕ} {K K' : Set (Mx D m n)} (h : K ⊆ K') (N : ℕ) (x : Mx D m n) :
    GlobalTheory.Unf.maj θ K N x ≤ GlobalTheory.Unf.maj θ K' N x := by
  by_cases hx : GlobalTheory.Unf.InBox K x
  · have hx' : GlobalTheory.Unf.InBox K' x := let ⟨k, hk, h0⟩ := hx; ⟨k, h hk, h0⟩
    unfold GlobalTheory.Unf.maj
    rw [if_pos hx, if_pos hx']
  · have h0 : GlobalTheory.Unf.maj θ K N x = 0 := by unfold GlobalTheory.Unf.maj; rw [if_neg hx]
    rw [h0]
    exact GlobalTheory.Unf.maj_nonneg θ K' N x

theorem realSize_le (θ : InfFam D) (m n : ℕ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ x : Mx D m n,
    1 + GlobalTheory.Unf.realSize θ x ≤
      c * (1 + ‖(fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ)‖) := by
  set a : ℝ := ∑ _τ : D.what₂.Tau, ∑ _i : Fin m, ∑ _j : Fin n, (1 : ℝ) with ha
  have ha0 : 0 ≤ a :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => zero_le_one
  refine ⟨1 + a, by linarith, fun x => ?_⟩
  set y : D.what₂.Tau → Fin m → Fin n → ℂ := fun τ i j => compAt θ τ x i j with hy
  have h1 : GlobalTheory.Unf.realSize θ x ≤ a * ‖y‖ := by
    rw [ha]
    simp only [Finset.sum_mul, one_mul]
    refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    exact (norm_le_pi_norm (y τ i) j).trans ((norm_le_pi_norm (y τ) i).trans (norm_le_pi_norm y τ))
  have h2 := norm_nonneg y
  nlinarith

def HasMaj (θ : InfFam D) {m n : ℕ} (φ : Mx D m n → ℂ) : Prop :=
  Continuous φ ∧ ∃ K : Set (Mx D m n), IsCompact K ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C * GlobalTheory.Unf.maj θ K N x

theorem HasMaj.zero (θ : InfFam D) (m n : ℕ) : HasMaj θ (0 : Mx D m n → ℂ) :=
  ⟨continuous_const, ∅, isCompact_empty, fun _ => ⟨0, fun _ => by simp⟩⟩

theorem HasMaj.add {θ : InfFam D} {m n : ℕ} {φ φ' : Mx D m n → ℂ} (h : HasMaj θ φ) (h' : HasMaj θ φ') :
    HasMaj θ (φ + φ') := by
  obtain ⟨hc, K, hK, hb⟩ := h
  obtain ⟨hc', K', hK', hb'⟩ := h'
  refine ⟨hc.add hc', K ∪ K', hK.union hK', fun N => ?_⟩
  obtain ⟨C, hC⟩ := hb N
  obtain ⟨C', hC'⟩ := hb' N
  refine ⟨|C| + |C'|, fun x => ?_⟩
  have h1 : ‖φ x‖ ≤ |C| * GlobalTheory.Unf.maj θ (K ∪ K') N x :=
    (hC x).trans (mul_le_mul (le_abs_self C) (maj_mono θ Set.subset_union_left N x) (GlobalTheory.Unf.maj_nonneg θ K N x)
      (abs_nonneg C))
  have h2 : ‖φ' x‖ ≤ |C'| * GlobalTheory.Unf.maj θ (K ∪ K') N x :=
    (hC' x).trans (mul_le_mul (le_abs_self C') (maj_mono θ Set.subset_union_right N x) (GlobalTheory.Unf.maj_nonneg θ K' N x)
      (abs_nonneg C'))
  rw [add_mul]
  exact (norm_add_le (φ x) (φ' x)).trans (add_le_add h1 h2)

theorem HasMaj.smul {θ : InfFam D} {m n : ℕ} {φ : Mx D m n → ℂ} (a : ℂ) (h : HasMaj θ φ) : HasMaj θ (a • φ) := by
  obtain ⟨hc, K, hK, hb⟩ := h
  refine ⟨hc.const_smul a, K, hK, fun N => ?_⟩
  obtain ⟨C, hC⟩ := hb N
  refine ⟨‖a‖ * C, fun x => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg a)

theorem hasMaj_pure {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ)
    (g : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) :
    HasMaj θ fun x : Mx D m n => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j)) := by
  obtain ⟨hfc, s, hs, hsec⟩ := finPart_section D
  have hgc : Continuous g := hg.1.continuous
  have hgs : HasCompactSupport g := hg.2
  have hy : Continuous fun x : Mx D m n => (fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ) :=
    continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
      (GlobalTheory.RealWeil.continuous_compAt hθ τ m n).matrix_elem i j
  have hz : Continuous fun x : Mx D m n =>
      (fun i j => finPart D (x i j) : Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    continuous_pi fun i => continuous_pi fun j => hfc.comp (continuous_id.matrix_elem i j)
  let t : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → Mx D m n := fun z => Matrix.of fun i j => s (z i j)
  have ht : Continuous t :=
    continuous_matrix fun i j => hs.comp ((continuous_apply j).comp (continuous_apply i))
  refine ⟨(f.continuous.comp hy).mul (hgc.comp hz), t '' tsupport g, hgs.isCompact.image ht, fun N => ?_⟩
  obtain ⟨G, hG⟩ := hgs.exists_bound_of_continuous hgc
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  obtain ⟨c, hc0, hc⟩ := realSize_le θ m n
  obtain ⟨S, hS⟩ : ∃ S : ℝ, ∀ y, (1 + ‖y‖) ^ N * ‖f y‖ ≤ S := by
    have h := fun y =>
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0)) (k := N) (n := 0) le_rfl le_rfl f y
    simp only [norm_iteratedFDeriv_zero] at h
    exact ⟨_, h⟩
  have hS0 : 0 ≤ S := le_trans (by positivity) (hS 0)
  refine ⟨c ^ N * S * G, fun x => ?_⟩
  by_cases h0 : g (fun i j => finPart D (x i j)) = 0
  · simp only [h0, mul_zero, norm_zero]
    exact mul_nonneg (by positivity) (GlobalTheory.Unf.maj_nonneg θ _ N x)
  · have hin : GlobalTheory.Unf.InBox (t '' tsupport g) x := by
      refine ⟨t fun i j => finPart D (x i j), ⟨_, subset_tsupport g h0, rfl⟩, ?_⟩
      ext i j
      change finPart D (x i j - s (finPart D (x i j))) = 0
      rw [(finPart D).map_sub, hsec, sub_self]
    have hr := GlobalTheory.Unf.realSize_nonneg θ x
    unfold GlobalTheory.Unf.maj
    rw [if_pos hin, le_mul_inv_iff₀ (by positivity), norm_mul]
    have h1 := hc x
    have h2 := hS (fun τ i j => compAt θ τ x i j)
    have h3 := hG (fun i j => finPart D (x i j))
    generalize (fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ) = y at h1 h2 ⊢
    generalize g (fun i j => finPart D (x i j)) = b at h3 ⊢
    have h4 : (1 + GlobalTheory.Unf.realSize θ x) ^ N ≤ c ^ N * (1 + ‖y‖) ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) h1 N
    calc ‖f y‖ * ‖b‖ * (1 + GlobalTheory.Unf.realSize θ x) ^ N ≤ ‖f y‖ * G * (c ^ N * (1 + ‖y‖) ^ N) := by gcongr
      _ = c ^ N * ((1 + ‖y‖) ^ N * ‖f y‖) * G := by ring
      _ ≤ c ^ N * S * G := by gcongr

theorem hasMaj_of_mem {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} {φ : Mx D m n → ℂ}
    (hφ : φ ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ m n) : HasMaj θ φ := by
  refine Submodule.span_induction (p := fun φ _ => HasMaj θ φ) ?_ (HasMaj.zero θ m n)
    (fun _ _ _ _ h h' => h.add h') (fun a _ _ h => h.smul a) hφ
  rintro _ ⟨f, g, hg, rfl⟩
  exact hasMaj_pure hθ f g hg

theorem continuous_and_le_maj : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (φ : Mx D m n → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → Continuous φ ∧ ∃ K : Set (Mx D m n), IsCompact K ∧
      ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C * GlobalTheory.Unf.maj θ K N x :=
  fun D θ hθ m n φ hφ => hasMaj_of_mem hθ ((_root_.GlobalTheory.SchwartzIff.isSchwartzBruhat_iff_mem_schwartzA D θ hθ m n φ).1 hφ)

end GlobalTheory.SchwartzMaj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaContractionExtendByZeroDoubleCombination
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ContrComb

variable {D : D7}

theorem heisO_resS_symm_zero {V₀ A L : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (o : OrthDec V₀ A L) (S : HSp D)
    (f : WO V₀ S → ℂ) (a u : WO A S) (x : WO L S) :
    heisO ψ V₀ S ((o.resS S).symm (a, 0)) f ((o.resS S).symm (u, x)) =
      ψ (symplOH A S u a) * f ((o.resS S).symm (u + a, x)) := by
  have h1 : (o.resS S).symm (u, x) + (o.resS S).symm (a, 0) = (o.resS S).symm (u + a, x) := by
    rw [← map_add (f := _)]; simp
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_right, add_zero, h1]

theorem heisO_resT_symm_zero {T A L : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (o : OrthDec T A L) (S : HSp D)
    (f : WO S T → ℂ) (b v : WO S A) (x : WO S L) :
    heisO ψ S T ((o.resT S).symm (b, 0)) f ((o.resT S).symm (v, x)) =
      ψ (symplOH S A v b) * f ((o.resT S).symm (v + b, x)) := by
  have h1 : (o.resT S).symm (v, x) + (o.resT S).symm (b, 0) = (o.resT S).symm (v + b, x) := by
    rw [← map_add (f := _)]; simp
  simp only [heisO]
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_right, add_zero, h1]

theorem comb_extS {V₀ A L : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (o : OrthDec V₀ A L) (S : HSp D)
    (c : WO A S →₀ ℂ) (f : WO V₀ S → ℂ) :
    comb ψ V₀ S (extS o S c) f = ∑ a ∈ c.support, c a • heisO ψ V₀ S ((o.resS S).symm (a, 0)) f := by
  have inj : Function.Injective fun a : WO A S => (o.resS S).symm (a, 0) := fun a b h =>
    (Prod.ext_iff.1 ((o.resS S).symm.injective h)).1
  exact Finsupp.sum_mapDomain_index_inj (h := fun u x => x • heisO ψ V₀ S u f) inj

theorem comb_extT {T A L : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (o : OrthDec T A L) (S : HSp D)
    (c : WO S A →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (extT o S c) f = ∑ b ∈ c.support, c b • heisO ψ S T ((o.resT S).symm (b, 0)) f := by
  have inj : Function.Injective fun b : WO S A => (o.resT S).symm (b, 0) := fun a b h =>
    (Prod.ext_iff.1 ((o.resT S).symm.injective h)).1
  exact Finsupp.sum_mapDomain_index_inj (h := fun u x => x • heisO ψ S T u f) inj

theorem contr_comb_ext : ∀ (D : D7) (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D)
    (vL : VolM D B'.L.rank S.rank) (ψ : AddChar (AF D.host.F) ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ),
    (∀ (u : WO B.A S) (v : WO S B'.A), IntegrableOn (fun w => f₂ ((B'.o.resT S).symm (v, w)) *
      f₁ ((B.o.resS S).symm (u, l.κ S w))) vL.𝓕 vL.μ) →
    ∀ (c : WO B.A S →₀ ℂ) (c' : WO S B'.A →₀ ℂ),
      contr l S vL (comb ψ B.V₀ S (extS B.o S c) f₁) (comb ψ S B'.V₀ (extT B'.o S c') f₂) =
        biComb ψ B.A S B'.A c c' (contr l S vL f₁ f₂) := by
  intro D ρ σ B B' l S vL ψ f₁ f₂ hint c c'
  funext u v
  rw [comb_extS, comb_extT]
  simp only [contr, biComb, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO_resS_symm_zero,
    heisO_resT_symm_zero]
  simp only [heisO]
  have hI : ∀ a b, Integrable (fun w => f₂ ((B'.o.resT S).symm (v + b, w)) * f₁ ((B.o.resS S).symm (u + a, l.κ S w)))
      (vL.μ.restrict vL.𝓕) := fun a b => hint (u + a) (v + b)
  calc _ = ∫ w in vL.𝓕, ∑ a ∈ c.support, ∑ b ∈ c'.support, (c a * ψ (symplOH B.A S u a) * (c' b * ψ (symplOH S B'.A v b))) *
          (f₂ ((B'.o.resT S).symm (v + b, w)) * f₁ ((B.o.resS S).symm (u + a, l.κ S w))) ∂vL.μ := by
        congr 1
        funext w
        rw [mul_comm, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ a ∈ c.support, ∑ b ∈ c'.support, (c a * ψ (symplOH B.A S u a) * (c' b * ψ (symplOH S B'.A v b))) *
          contr l S vL f₁ f₂ (u + a) (v + b) := by
        rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hI a b).const_mul _]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [integral_finsetSum _ fun b _ => (hI a b).const_mul _]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [integral_const_mul]
        rfl
    _ = _ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring

end GlobalTheory.ContrComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaZeroMeanLogNormConjugatesOfWeberStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaZero_mean_log_norm_conjugates_of_weber : PeriodLatticeAgreement.LatticePeriodEta → ThetaConstantWeber.ThetaWeberStatement → SignedLogMeans.Theta0Mean := by
  first | exact @GlobalTheory.Theta0MeanCore.theta0Mean | exact GlobalTheory.Theta0MeanCore.theta0Mean | (intros; apply GlobalTheory.Theta0MeanCore.theta0Mean <;> assumption)
end

