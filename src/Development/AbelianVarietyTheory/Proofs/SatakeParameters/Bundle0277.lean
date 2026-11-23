module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0266
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0269
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0261
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivFr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0260
public import Formalism.LocalToGlobal.Columns.Bundle0035
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTwistPrimeInvariantCongruentFrames
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0271
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.MqRowSGUnif
public import Formalism.SharpRestriction.GlobalSchurBounds.Joints
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalizedLatticeEqOfAdelicMatricesAgreeAtPlace
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntAtAdeleMulOfPlaceComponentEqZeroStatement
section
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intAtAdele_mul_of_placeComponent_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (Q : HeightOneSpectrum (𝓞 E)), Formalism.L2.Col.IsOver v Q → ∀ a : TensorProduct F E (FiniteAdeleRing (𝓞 F) F), Formalism.UG.prV (E := E) v a = 0 → ∀ c : E, Formalism.L2.Col.IntAtA (F := F) Q (Formalism.L2.Col.iA F E c * a) := by
  first | exact @GlobalTheory.VanishAtOver.intAtA_mul_of_prV_eq_zero | exact GlobalTheory.VanishAtOver.intAtA_mul_of_prV_eq_zero | (intros; apply GlobalTheory.VanishAtOver.intAtA_mul_of_prV_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IwahoriNeBotOfSpherical
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Cong.LimitAtL

theorem mem_fixed {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] {ρ : Representation k G V}
    {H : Subgroup G} {v : V} : v ∈ GlobalTheory.PRep.fixed ρ H ↔ ∀ h ∈ H, ρ h v = v := by
  show (∀ h : H, ρ (h : G) v = ((1 : H →* kˣ) h : k) • v) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g g.2⟩

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime]
  {a : ℕ}

end GlobalTheory.Cong.LimitAtL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumEquivariantRationalUnitary
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TopRat

section Frames
variable {X : Fields} {Pr : Primes X} {R : Ranks} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) {u : Pr.Word} {j : ℕ}

theorem frsF_rat_notG (p : ChPt (R := R) sel mu u j) (g : UF X.E (R.N j)) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) :
    frsF sel mu (((g, 1, 1) : UF X.E (R.N j) × GLG (E := X.E) (n := R.N j) (SG := Pr.vGs) × GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) • p) P =
      g.1 * frsF sel mu p P := by
  unfold frsF
  rw [dite_eq_right hP, dite_eq_right hP]
  show g.1 * p.fr _ * (((1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) _)⁻¹).1 = _
  simp

theorem frsF_rat_G (hq : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2)
    (p : ChPt (R := R) sel mu u j) (g : UF X.E (R.N j)) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) :
    ∃ κ : ↥(GLint X.E (R.N j) P.1),
      frsF sel mu (((g, 1, 1) : UF X.E (R.N j) × GLG (E := X.E) (n := R.N j) (SG := Pr.vGs) × GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) • p) P =
        g.1 * frsF sel mu p P * κ.1 ∧
      ∀ x ∈ stdAt X.E (R.N j) P.1, ((qOf P.1 : X.E) ^ 1)⁻¹ • (κ.1 x - x) ∈ stdAt X.E (R.N j) P.1 := by
  obtain ⟨κ, he, hr⟩ := liftFr_smul p.deco (g, (1 : GLG (E := X.E) (n := R.N j) (SG := Pr.vGs))) ⟨P.1, hP⟩
  refine ⟨κ, ?_, fun x hx => ?_⟩
  · unfold frsF
    rw [dite_eq_left hP, dite_eq_left hP]
    exact he
  · rw [GlobalTheory.TopStep.mem_stdAt]
    intro i
    have hkx := GlobalTheory.TopStep.mem_stdAt.1 ((κ.2 x).2 hx) i
    have hxi := GlobalTheory.TopStep.mem_stdAt.1 hx i
    have h1 := congrFun (hr x hx) i
    simp only [Pi.one_apply, inv_one, Units.val_one, Matrix.one_mulVec] at h1
    have hred : redP P.1 (κ.1 x i - x i) = 0 := by
      rw [GlobalTheory.TopStep.reduction_sub hkx hxi]
      have h2 : redP P.1 (κ.1 x i) = redP P.1 (x i) := h1
      rw [h2, sub_self]
    have h := GlobalTheory.TopStep.intAt_div_of_redP (hq P hP) (GlobalTheory.TopStep.intAt_sub hkx hxi) hred
    have e : (((qOf P.1 : X.E) ^ 1)⁻¹ • (κ.1 x - x)) i = (κ.1 x i - x i) / (qOf P.1 : X.E) := by
      simp [div_eq_inv_mul]
    rw [e]
    exact h

end Frames

theorem xiPt_top_smul : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m), t.m2 < i → ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG (E := t.X.E) (n := D.R.N (i + 1)) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie i hi hlt β β' x x' p p' _hp _hp' g g' w
  have hm := m_eq t μ
  obtain rfl : i = t.m2 + 1 := by omega
  have hn1 : ¬ (t.m2 + 1 < t.m2) := by omega
  have hn2 : t.m2 + 1 ≠ t.m2 := by omega
  unfold xiPt
  rw [dite_eq_right hn1, if_neg hn2, dite_eq_right hn1, if_neg hn2, XiTop_eq, XiTop_eq]
  congr 1
  · exact phiT_smul t.X.K p.deco p'.deco g 1 g' 1 w
  · have hX : t.X.Ok := hPin.fields.ok
    have hok := t.idx_ok μ
    have hc := hok.cst_ok
    have hrep : ∀ q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1),
        repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β q) ∈ cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β q := by
      intro q
      obtain ⟨y, hy⟩ := GlobalTheory.CplCosetPt.exists_sameCoset_frames t.sel (t.tup μ) (t.cst μ) (fun P => frsF t.sel (t.tup μ) q P)
        (fun P => y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P)
      exact Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β q) ⟨y, hy⟩
    have hy0 := GlobalTheory.T.intAt_scaled_baseCosetRep_of_adTie D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie β
    refine Finset.prod_congr rfl fun P _ => ?_
    have hq0 : (qOf P.1 : t.X.E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
    have hqI : IntAt P.1 (qOf P.1 : t.X.E) := by simpa using IntAt.coe P.1 ((qOf P.1 : ℕ) : 𝓞 t.X.E)
    have hyy : y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P = A.y0 β P := by
      unfold y0At
      rw [dite_eq_left rfl]
    by_cases hP : P.1 ∈ t.Pr.vGs
    · have hq2 : ∀ P : rowSG t.Pr t.sel (t.tup μ), P.1 ∈ t.Pr.vGs → ((qOf P.1 : ℕ) : 𝓞 t.X.E) ∉ P.1.asIdeal ^ 2 :=
        fun P hP => GlobalTheory.TopStep.qOf_notMem_sq hX t.pr_ok hP
      obtain ⟨κ, hF, hκc⟩ := frsF_rat_G t.sel (t.tup μ) hq2 p g P hP
      obtain ⟨κ', hF', hκc'⟩ := frsF_rat_G t.sel (t.tup μ) hq2 p' g' P hP
      have hD1 : (t.cst μ).D P = 1 := hok.depthG P hP
      have hκD : ∀ z ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ.1 z - z) ∈ stdAt t.X.E _ P.1 := by
        rw [hD1]; exact hκc
      have hκD' : ∀ z ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ'.1 z - z) ∈ stdAt t.X.E _ P.1 := by
        rw [hD1]; exact hκc'
      have hy0P : ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * A.y0 β P l) := by
        intro l
        have h := hy0 P l
        simpa only [hP, if_true, pow_one] using h
      have key1 : ∀ (F1 : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1))) (u1 u0 : Sp t.X.E (D.R.N (t.m2 + 1))),
          F1 = g.1 * frsF t.sel (t.tup μ) p P * κ.1 →
          SameCoset t.sel (t.tup μ) (t.cst μ) P (F1.symm u1) (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P) →
          SameCoset t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) p P).symm u0) (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P) →
          topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P
              (inFr F1 (g'.1 * frsF t.sel (t.tup μ) p' P * κ'.1) (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap)) (F1.symm u1) =
            topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P
              (inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w) ((frsF t.sel (t.tup μ) p P).symm u0) := by
        rintro F1 u1 u0 rfl h1 h2
        unfold SameCoset at h1 h2
        simp only [hP, if_true, pow_zero, inv_one, one_mul, hyy] at h1 h2
        have e1 : inFr (g.1 * frsF t.sel (t.tup μ) p P * κ.1) (g'.1 * frsF t.sel (t.tup μ) p' P * κ'.1)
            (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) =
            κ'.1.symm.toLinearMap ∘ₗ inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w ∘ₗ κ.1.toLinearMap := by
          refine LinearMap.ext fun v => ?_
          show κ'.1.symm ((frsF t.sel (t.tup μ) p' P).symm (g'.1.symm (g'.1 (w (g.1.symm (g.1 ((frsF t.sel (t.tup μ) p P) (κ.1 v)))))))) = _
          rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
          rfl
        have e2 : (g.1 * frsF t.sel (t.tup μ) p P * κ.1).symm u1 = κ.1.symm ((frsF t.sel (t.tup μ) p P).symm (g.1.symm u1)) := rfl
        rw [e1, e2]
        rw [e2] at h1
        generalize (frsF t.sel (t.tup μ) p P).symm (g.1.symm u1) = v1 at h1 ⊢
        generalize (frsF t.sel (t.tup μ) p P).symm u0 = v at h2 ⊢
        generalize inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w = Yw
        have hbd : ∀ z : Sp t.X.E (D.R.N (t.m2 + 1)), (∀ l, IntAt P.1 ((z - A.y0 β P) l)) →
            ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * z l) := by
          intro z hz l
          have e : (qOf P.1 : t.X.E) * z l = (qOf P.1 : t.X.E) * (z - A.y0 β P) l + (qOf P.1 : t.X.E) * A.y0 β P l := by
            simp only [Pi.sub_apply]; ring
          rw [e]
          exact (hqI.mul (hz l)).add (hy0P l)
        have hw : (qOf P.1 : t.X.E) • κ.1.symm v1 ∈ stdAt t.X.E _ P.1 :=
          GlobalTheory.TopStep.mem_stdAt.2 fun l => by simpa using hbd _ h1 l
        have hw1 : (qOf P.1 : t.X.E) • v1 ∈ stdAt t.X.E _ P.1 := by
          have h := (κ.2 ((qOf P.1 : t.X.E) • κ.1.symm v1)).2 hw
          rwa [map_smul, LinearEquiv.apply_symm_apply] at h
        have hv1 : ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * v1 l) := fun l => by
          simpa using GlobalTheory.TopStep.mem_stdAt.1 hw1 l
        rw [GlobalTheory.TwV.AwayTopG.topDat_frames_vGs A dtU a hPin hTie P hP κ.1 κ'.1 κ.2 hκD κ'.2 hκD' Yw v1 hv1]
        have hs := GlobalTheory.TwV.AwayTopG.symm_near κ.2 hκc hw1
        rw [map_smul, ← smul_sub, smul_smul, pow_one, inv_mul_cancel₀ hq0, one_smul] at hs
        have hdiff : v1 - v ∈ stdAt t.X.E _ P.1 := by
          refine GlobalTheory.TopStep.mem_stdAt.2 fun l => ?_
          have e : (v1 - v) l = (κ.1.symm v1 - A.y0 β P) l - (κ.1.symm v1 - v1) l - (v - A.y0 β P) l := by
            simp only [Pi.sub_apply]; ring
          rw [e]
          exact GlobalTheory.TopStep.intAt_sub (GlobalTheory.TopStep.intAt_sub (h1 l) (GlobalTheory.TopStep.mem_stdAt.1 hs l)) (h2 l)
        unfold topDat
        congr 1
        have h := GlobalTheory.TopLaw.ftY_comp_glint t.sel (t.tup μ) (t.cst μ) hc P (hok.depthQ P) (κ := 1)
          (atNL t.X.E (D.R.N (t.m2 + 1 + 1)) (D.R.N (t.m2 + 1 + 1) - 1) ∘ₗ Yw) v v1 (fun _ => hbd _ h2)
          (fun h => absurd hP h) (fun _ => hdiff) (fun h => absurd hP h)
        exact h
      rw [hF']
      exact key1 _ _ _ hF (hrep _ P) (hrep _ P)
    · have hy0P : ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) ^ (t.cst μ).M * A.y0 β P l) := by
        intro l
        have h := hy0 P l
        simpa only [hP, if_false] using h
      have hqM : (qOf P.1 : t.X.E) ^ (t.cst μ).M ≠ 0 := pow_ne_zero _ hq0
      have key2 : ∀ (F1 : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1))) (u1 u0 : Sp t.X.E (D.R.N (t.m2 + 1))),
          F1 = g.1 * frsF t.sel (t.tup μ) p P →
          SameCoset t.sel (t.tup μ) (t.cst μ) P (F1.symm u1) (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P) →
          SameCoset t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) p P).symm u0) (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P) →
          topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P
              (inFr F1 (g'.1 * frsF t.sel (t.tup μ) p' P) (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap)) (F1.symm u1) =
            topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P
              (inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w) ((frsF t.sel (t.tup μ) p P).symm u0) := by
        rintro F1 u1 u0 rfl h1 h2
        unfold SameCoset at h1 h2
        simp only [hP, if_false, hyy] at h1 h2
        have e1 : inFr (g.1 * frsF t.sel (t.tup μ) p P) (g'.1 * frsF t.sel (t.tup μ) p' P)
            (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w := by
          refine LinearMap.ext fun v => ?_
          show (frsF t.sel (t.tup μ) p' P).symm (g'.1.symm (g'.1 (w (g.1.symm (g.1 ((frsF t.sel (t.tup μ) p P) v)))))) = _
          rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
          rfl
        have e2 : (g.1 * frsF t.sel (t.tup μ) p P).symm u1 = (frsF t.sel (t.tup μ) p P).symm (g.1.symm u1) := rfl
        rw [e1, e2]
        rw [e2] at h1
        generalize (frsF t.sel (t.tup μ) p P).symm (g.1.symm u1) = v1 at h1 ⊢
        generalize (frsF t.sel (t.tup μ) p P).symm u0 = v at h2 ⊢
        generalize inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w = Yw
        have hv : ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) ^ (t.cst μ).M * v l) := by
          intro l
          have e : (qOf P.1 : t.X.E) ^ (t.cst μ).M * v l = (qOf P.1 : t.X.E) ^ (t.cst μ).M * (qOf P.1 : t.X.E) ^ (t.cst μ).M *
              (((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (v - A.y0 β P) l) + (qOf P.1 : t.X.E) ^ (t.cst μ).M * A.y0 β P l := by
            simp only [Pi.sub_apply]
            field_simp
            ring
          rw [e]
          exact (((GlobalTheory.TopStep.intAt_pow hqI _).mul (GlobalTheory.TopStep.intAt_pow hqI _)).mul (h2 l)).add (hy0P l)
        have hdiff : ((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ • (v1 - v) ∈ stdAt t.X.E _ P.1 := by
          refine GlobalTheory.TopStep.mem_stdAt.2 fun l => ?_
          have e : (((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ • (v1 - v)) l =
              ((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (v1 - A.y0 β P) l - ((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (v - A.y0 β P) l := by
            simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
          rw [e]
          exact GlobalTheory.TopStep.intAt_sub (h1 l) (h2 l)
        unfold topDat
        congr 1
        have h := GlobalTheory.TopLaw.ftY_comp_glint t.sel (t.tup μ) (t.cst μ) hc P (hok.depthQ P) (κ := 1)
          (atNL t.X.E (D.R.N (t.m2 + 1 + 1)) (D.R.N (t.m2 + 1 + 1) - 1) ∘ₗ Yw) v v1 (fun h => absurd h hP)
          (fun _ => hv) (fun h => absurd h hP) (fun _ => hdiff)
        exact h
      rw [frsF_rat_notG t.sel (t.tup μ) p' g' P hP]
      exact key2 _ _ _ (frsF_rat_notG t.sel (t.tup μ) p g P hP) (hrep _ P) (hrep _ P)

end GlobalTheory.TopRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumFixedCongruentFrameChangeTwistPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopStep GlobalTheory.TopLaw GlobalTheory.TopFrameQ

namespace GlobalTheory.TopFrameQM

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu))

theorem topDat_frames_qM {m2 : ℕ} (hm : R.m = m2 + 2) (hc : cst.Ok) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (hD : 2 * cst.M ≤ cst.D P)
    (κ : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1)))
    (κ' : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1)))
    (hκ : κ ∈ GLint X.E _ P.1)
    (hκc : ∀ w ∈ stdAt X.E _ P.1, ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E _ P.1)
    (hκ' : κ' ∈ GLint X.E _ P.1)
    (hκ'c : ∀ w ∈ stdAt X.E _ P.1, ((qOf P.1 : X.E) ^ (2 * cst.M))⁻¹ • (κ' w - w) ∈ stdAt X.E _ P.1)
    (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y'' : Sp X.E (R.N (m2 + 1)))
    (hy'' : ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y'' l)) :
    topDat Ch sel mu cst (m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
      topDat Ch sel mu cst (m2 + 1) P y y'' := by
  have hM1 : 1 ≤ cst.M := hc.M_pos
  have hMD : cst.M + 1 ≤ cst.D P := by omega
  have hMD' : cst.M + 1 ≤ 2 * cst.M := by omega
  have hq : (qOf P.1 : X.E) ≠ 0 := qOf_ne_zero
  have hκ's : κ'.symm ∈ GLint X.E _ P.1 := (GLint X.E _ P.1).inv_mem hκ'
  have hκs : κ.symm ∈ GLint X.E _ P.1 := (GLint X.E _ P.1).inv_mem hκ
  have hκ'sc := cong_symm hκ' hκ'c
  by_cases hg : ∀ j, abelian₂ P.1 (R.N (m2 + 1 + 1)) cst.M (y (Pi.single j 1))
  · unfold topDat
    congr 1
    · unfold PhiTopG
      rw [if_neg hP]
      have hc0 : cOf R (m2 + 1) = 0 := cOf_topB hm
      have hw : ∀ w ∈ stdAt X.E (R.N (m2 + 1)) P.1, ∀ l : Fin (R.N (m2 + 1 + 1)), l.1 + 1 < R.N (m2 + 1 + 1) →
          IntAt P.1 ((κ'.symm (y (κ w)) - y w) l / (qOf P.1 : X.E)) := by
        intro w hw l hl
        have hu := abelian₂.of_basis y hg (glint_mem (⟨κ, hκ⟩ : GLint X.E _ P.1) hw)
        have d1 := mem_stdAt.1 (abelian₂.move hκ's hκ'sc hMD' hu).2 l
        have e1 := intAt_inv_pow_le (a := 1) (by omega) d1
        have hu' : ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E _ P.1 := hκc w hw
        have hyu := (abelian₂.of_basis y hg hu').2 l hl
        rw [map_smul, map_sub, Pi.smul_apply, smul_eq_mul] at hyu
        have e2 := intAt_inv_pow_le (a := 1) (by omega) hyu
        rw [pow_one] at e1 e2
        have e3 := e1.add e2
        rw [← add_div] at e3
        convert e3 using 2
        simp only [Pi.sub_apply]
        ring
      have key := fun z hz => GlobalTheory.TopInv.PhiQ_add (K := X.K) (GlobalTheory.TopInv.qOf_mem P.1) hq
        (resChar (mu : Chr X.F X.E X.K) P.1) R.k R.r (cOf R (m2 + 1)) (R.N (m2 + 1)) (R.N (m2 + 1 + 1) - 1) hc0
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) z hz
      refine (congrArg _ (add_sub_cancel _ _)).symm.trans (key _ ?_)
      intro s l
      have hws : (LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) (Pi.single s (1 : X.E)) : Sp X.E _) ∈
          stdAt X.E (R.N (m2 + 1)) P.1 :=
        mem_stdAt.2 fun a => GlobalTheory.TopInv.single_int s (Fin.castAdd _ a)
      have := hw _ hws ⟨l.1, by omega⟩ (by show l.1 + 1 < _; omega)
      exact this
    · have h1 := ftY_comp_glint sel mu cst hc P (fun _ => hD) ⟨κ, hκ⟩
          (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.symm.toLinearMap ∘ₗ y) y'' (κ.symm y'')
          (fun h => absurd h hP) (fun _ => hy'') (fun h => absurd h hP)
          (fun _ => by
            show ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (κ (κ.symm y'') - y'') ∈ _
            rw [LinearEquiv.apply_symm_apply, sub_self, smul_zero]
            exact zero_mem _)
      refine h1.trans ?_
      have hy''s : ((qOf P.1 : X.E) ^ cst.M) • y'' ∈ stdAt X.E _ P.1 :=
        mem_stdAt.2 fun l => by simpa only [Pi.smul_apply, smul_eq_mul] using hy'' l
      have hδ : ∀ i, IntAt P.1 (((qOf P.1 : X.E) ^ cst.M)⁻¹ *
          ((atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.symm.toLinearMap ∘ₗ y) -
            atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) (Pi.single i 1)) := by
        intro i
        have d1 := mem_stdAt.1 (abelian₂.move hκ's hκ'sc (v := y (Pi.single i 1)) hMD' (hg i)).2
        have e1 : ∀ l, IntAt P.1 ((κ'.symm (y (Pi.single i 1)) - y (Pi.single i 1)) l / (qOf P.1 : X.E) ^ cst.M) :=
          fun l => intAt_inv_pow_le (by omega) (d1 l)
        have e2 := GlobalTheory.TopInv.atNL_int (R.N (m2 + 1 + 1) - 1) _ _ e1
        rw [inv_mul_eq_div]
        convert e2 using 2
        simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
        rfl
      have h2 := GlobalTheory.ftY_pert_qM sel mu cst hc P hP hD (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y)
        _ y'' hδ hy''s
      rw [add_sub_cancel] at h2
      exact h2
  · have h0 : topDat Ch sel mu cst (m2 + 1) P y y'' = 0 := by
      by_contra hne
      exact hg (lam_of_topDat_ne Ch sel mu cst _ P hP y y'' hne)
    rw [h0]
    by_contra hne
    apply hg
    have h1 := lam_of_topDat_ne Ch sel mu cst _ P hP _ _ hne
    have h2 := lam_comp hκs hκ' hκ'c hMD' _ h1
    intro j
    have := h2 j
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using this

end Main

end GlobalTheory.TopFrameQM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelFrameLiftUnitaryAutNearAdelicMatrixDepthOneStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelFrameLift_unitaryAut_near_adelicMatrix_depth_one : ∀ {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) (w : SG) (g : UF X.E n), ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2 → ∀ (y : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), NearAt (seamP s w.1) 1 y (seamGL s (d.1.liftFr w)) → NearAt (seamP s w.1) 1 (ratA D.host.F (seamGL s g.1) * y) (seamGL s (((g, (1 : GLG (E := X.E) (n := n) (SG := SG))) • d).1.liftFr w)) := by
  first | exact @GlobalTheory.FrameRat.nearAt_liftFr_smul | exact GlobalTheory.FrameRat.nearAt_liftFr_smul | (intros; apply GlobalTheory.FrameRat.nearAt_liftFr_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalIsometry
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.TwV

theorem funMoved_ptAd_rat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → ∀ (P : t.Pr.vT (t.word u)) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal),
        IsOver v (seamP t.seam P.1) →
        FunMoved t.seam ((St i hi).K β).lev P v h (iotaOf A i hi β P v h) (ratA D.host.F (A.crd i hi) * x₁.1) ((((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)).deco.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie i hi β x x₁ γ hγ hx g hg p hp P v h hv
  have H := funMoved_ratA_act t.seam _ P v h _ _ _ g.1 1 (hp.fnl P v h hv)
  have e : ratA D.host.F (A.crd i hi) * x₁.1 = ratA D.host.F (seamGL t.seam g.1) * (ratA D.host.F (A.crd i hi) * x.1) := by
    rw [hx, hg, map_mul, map_mul, map_inv]; group
  rw [e]
  exact H

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalLatticeAutStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrimeFunctionals_move_rational_lattice_aut : ∀ {D : D7} {X : Fields} (s : Seam D X) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : Formalism.L2.Forms.StepLevel D.host.F D.host.E (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D i hi) T D.R.f bad) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (P : ST) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (T : 𝓞 D.host.F) ∈ v.asIdeal) (ι : lev.fM v h →+ 𝓞 X.E ⧸ P.1.asIdeal) (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (d : Deco X.E (D.R.N i) ST SG) (g : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)) (hh : GLG (E := X.E) (n := D.R.N i) (SG := SG)), FunMoved s lev P v h ι x d → FunMoved s lev P v h ι (ratA D.host.F (seamGL s g) * x) (d.act g hh) := by
  first | exact @GlobalTheory.TwU.funMoved_ratA_act | exact GlobalTheory.TwU.funMoved_ratA_act | (intros; apply GlobalTheory.TwU.funMoved_ratA_act <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalizedLatticeEqOfAdelicMatricesAgreeAtPlaceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localizedLattice_eq_of_adelic_matrices_agree_at_place : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : t.Pr.vT (t.word u),
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    p₁.deco.1.at P.1 = p.deco.1.at P.1 := by
  first | exact @GlobalTheory.LatAway.decoAt_eq | exact GlobalTheory.LatAway.decoAt_eq | (intros; apply GlobalTheory.LatAway.decoAt_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceComponentEqOneIffComponentsOverEqOneStatement
section
open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeComponent_eq_one_iff_components_over_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (z : AfE F E), Formalism.UG.prV (E := E) v z = 1 ↔ ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → GlobalTheory.Mem.Col2.afIso F E z P = 1 := by
  first | exact @GlobalTheory.AfIsoPrV.prV_eq_one_iff_afIso | exact GlobalTheory.AfIsoPrV.prV_eq_one_iff_afIso | (intros; apply GlobalTheory.AfIsoPrV.prV_eq_one_iff_afIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalMatrixEntriesCongruentOneOfAdelicCongrueStatement
section
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalMatrix_entries_congruent_one_of_adelic_congruent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Q : HeightOneSpectrum (𝓞 E)) (n N : ℕ) (g : GL (Fin N) E), GlobalTheory.TwU.CongAt (F := F) Q n (GlobalTheory.TwU.ratA F g) → ∀ a b : Fin N, Formalism.L2.Col.IntAt Q ((((Formalism.L2.Col.qOf Q : ℕ) : E) ^ n)⁻¹ * ((g : Matrix (Fin N) (Fin N) E) a b - (1 : Matrix (Fin N) (Fin N) E) a b)) := by
  first | exact @GlobalTheory.TwU.ratA_congAt_entry | exact GlobalTheory.TwU.ratA_congAt_entry | (intros; apply GlobalTheory.TwU.ratA_congAt_entry <;> assumption)
end

