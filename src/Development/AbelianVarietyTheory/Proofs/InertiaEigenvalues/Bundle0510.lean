module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0426
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0050
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0454
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0486

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvLift
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.InvLift

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) (m : ℕ)

def InvSet : Subring bk.S where
  carrier := {x | ∀ g : ↥(GK K), bk.ev bk.E ^ m ∣ Per.σA (g : GQ l) (bk.ev x) - bk.ev x}
  zero_mem' g := by simp
  one_mem' g := by simp
  neg_mem' {x} hx g := by
    have := (hx g).neg_right
    simpa [map_neg, neg_sub, sub_eq_add_neg, add_comm] using this
  add_mem' {x y} hx hy g := by
    have h := dvd_add (hx g) (hy g)
    rw [map_add (f := _), map_add (f := _)]
    convert h using 1
    ring
  mul_mem' {x y} hx hy g := by
    have h := dvd_add (dvd_mul_of_dvd_right (hy g) (Per.σA (g : GQ l) (bk.ev x)))
      (dvd_mul_of_dvd_left (hx g) (bk.ev y))
    rw [map_mul, map_mul]
    convert h using 1
    ring

theorem C_mem (w : Wq l bk.a) : (C w : bk.S) ∈ InvSet bk m := fun g => by
  rw [bk.ev_C, bk.gal_w, sub_self]
  exact dvd_zero _

omit hl in
theorem coe_sum_fin {R : Type} [CommRing R] {e : ℕ} (c : Fin e → R) :
    ((∑ i, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ) : Polynomial R) : R⟦X⟧) = ∑ i, C (c i) * X ^ (i : ℕ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  simp [Polynomial.coeToPowerSeries.ringHom_apply]

theorem exists_div (s : bk.S) : ∃ (q : bk.S) (c : Fin bk.Ep.natDegree → Wq l bk.a),
    s = bk.E * q + ∑ i, C (c i) * X ^ (i : ℕ) := by
  haveI : IsAdicComplete (Ideal.span {(l : Wq l bk.a)}) (Wq l bk.a) := WittVector.isAdicCompleteIdealSpanP
  have hdist : bk.Ep.IsDistinguishedAt (Ideal.span {(l : Wq l bk.a)}) :=
    { mem := fun {i} hi => Ideal.mem_span_singleton.2 (bk.dvd_coeff i hi)
      monic := bk.monic }
  have hI : Ideal.span {(l : Wq l bk.a)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (WittVector.irreducible l (k := Fq l bk.a)).not_isUnit
  obtain ⟨h1, h2⟩ := (hdist.isWeierstrassDivisorAt hI).isWeierstrassDivisionAt_div_mod s
  refine ⟨(hdist.isWeierstrassDivisorAt hI).div s, fun i => ((hdist.isWeierstrassDivisorAt hI).mod s).coeff i,
    h2.trans ?_⟩
  rw [← coe_sum_fin]
  congr 2
  have ho : bk.Ep.natDegree = _ := congr(ENat.toNat $(hdist.coe_natDegree_eq_order_map (bk.Ep : (Wq l bk.a)⟦X⟧) 1
    (by rwa [constantCoeff_one, ← Ideal.ne_top_iff_one]) (by simp)))
  rw [← ho] at h1
  rw [Polynomial.sum_fin (fun i a => Polynomial.C a * Polynomial.X ^ i) (by simp) h1,
    Polynomial.sum_C_mul_X_pow_eq]

variable {bk m} in
theorem cancel_pow_l (k : ℕ) (a : Ainf l) (h : bk.ev bk.E ^ m ∣ (l : Ainf l) ^ k * a) : bk.ev bk.E ^ m ∣ a := by
  induction k generalizing a with
  | zero => simpa using h
  | succ k ih =>
    apply (_root_.GlobalTheory.AinfEPow.ePow_facts l K bk m).1
    apply ih
    rwa [pow_succ, mul_assoc] at h

end GlobalTheory.BSP.InvLift


open GlobalTheory.BSP.InvLift in
theorem GlobalTheory.BSP.BK.exists_inv_lift : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ), ∃ k : ℕ, ∀ s : bk.S, ∃ γ : bk.S, bk.E ∣ γ - (l : bk.S) ^ k * s ∧ ∀ g : ↥(GK K), bk.ev bk.E ^ m ∣ Per.σA (g : GQ l) (bk.ev γ) - bk.ev γ := by
  intro l hl K bk m
  obtain ⟨M, q, hq1, hq2⟩ := GlobalTheory.BSP.BK.exists_approx_root l K bk m
  have hqinv : q ∈ InvSet bk m := fun g => by
    obtain ⟨k, hk⟩ := GlobalTheory.BSP.approx_root_indep l K bk m M q hq1 hq2 (ainfObj K) bk.ι ((ainfHom K g).comp bk.ι)
    change bk.ev bk.E ^ m ∣ (l : Ainf l) ^ k * (bk.ev q - Per.σA (g : GQ l) (bk.ev q)) at hk
    rw [← neg_sub]
    exact (cancel_pow_l k _ hk).neg_right
  set e := bk.Ep.natDegree
  refine ⟨M * e, fun s => ?_⟩
  obtain ⟨q', c, hs⟩ := exists_div bk s
  refine ⟨∑ i : Fin e, C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ), ?_, fun g => ?_⟩
  · have key : ∀ i : Fin e, bk.E ∣ C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ) -
        (l : bk.S) ^ (M * e) * (C (c i) * X ^ (i : ℕ)) := by
      intro i
      have h1 : (l : bk.S) ^ (M * e) * X ^ (i : ℕ) = (l : bk.S) ^ (M * (e - i)) * ((l : bk.S) ^ M * X) ^ (i : ℕ) := by
        rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add, ← Nat.mul_add]
        congr 3
        have := i.2
        omega
      rw [mul_left_comm, h1]
      have := (hq1.trans (sub_dvd_pow_sub_pow q ((l : bk.S) ^ M * X) i)).mul_left (C (c i) * (l : bk.S) ^ (M * (e - i)))
      convert this using 1
      ring
    have heq : (∑ i : Fin e, C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ)) - (l : bk.S) ^ (M * e) * s =
        (∑ i : Fin e, (C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ) -
          (l : bk.S) ^ (M * e) * (C (c i) * X ^ (i : ℕ)))) - bk.E * ((l : bk.S) ^ (M * e) * q') := by
      rw [hs, Finset.sum_sub_distrib, mul_add, Finset.mul_sum]
      ring
    rw [heq]
    exact dvd_sub (Finset.dvd_sum fun i _ => key i) (dvd_mul_right _ _)
  · have hmem : (∑ i : Fin e, C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ)) ∈ InvSet bk m :=
      Subring.sum_mem _ fun i _ => Subring.mul_mem _ (Subring.mul_mem _ (C_mem bk m _)
        (Subring.pow_mem _ (natCast_mem _ _) _)) (Subring.pow_mem _ hqinv _)
    exact hmem g
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsGrpPullbackGenericFibre
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)

noncomputable section

open scoped CategoryTheory.Obj

namespace GlobalTheory.GenericFibreUnif

theorem exists_isGrpPullback_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (χ : Sp R ⟶ Y.X) (t : SAB H (Sp R)) (m : SABMap t Y.t χ) (P : PELUnif I t) (z : Sp (FractionRing R) ⟶ Xo.XF c), z ≫ Y.j = jK R ≫ χ → letI := H.starRing; ∃ ψ : P.A.A.left ⟶ Y.oF.t.G.left, IsGrpPullback P.A.A Y.oF.t.G z ψ ∧ LBIso P.A.L (Y.oF.t.PP.L.pull ψ) ∧ (∀ a : 𝓞 E, (P.oA.act a).left ≫ ψ = ψ ≫ (Y.oF.t.act.act a).left) ∧ ψ ≫ Y.m.φ = P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ m.φ := by
  intro E _ _ _ H Dw l Xo c O _ β Y R _ _ I χ t m P z hz
  letI := H.starRing
  have := P.U.gen_hom
  have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
  set k : P.A.A.left ⟶ t.G.left := P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) with hk
  have gpG : IsGrpPullback P.A.A t.G (jK R) k :=
    ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK R))).congr (Category.id_comp _) rfl
  have n₀ : IsGrpPullback P.A.A Y.t.G (jK R ≫ χ) (k ≫ m.φ) := gpG.comp m.cart
  have hw : (k ≫ m.φ) ≫ Y.t.G.hom = (P.A.A.hom ≫ z) ≫ (Y.jQ ≫ pullback.fst _ _) := by
    refine n₀.1.w.trans ?_
    rw [← hz, Category.assoc]; rfl
  let ψ : P.A.A.left ⟶ Y.oF.t.G.left := Y.m.cart.1.lift (k ≫ m.φ) (P.A.A.hom ≫ z) hw
  have hψ₁ : ψ ≫ Y.m.φ = k ≫ m.φ := Y.m.cart.1.lift_fst _ _ _
  have hψ₂ : ψ ≫ Y.oF.t.G.hom = P.A.A.hom ≫ z := Y.m.cart.1.lift_snd _ _ _
  have n : IsGrpPullback P.A.A Y.t.G (z ≫ (Y.jQ ≫ pullback.fst _ _)) (ψ ≫ Y.m.φ) :=
    n₀.congr hz.symm hψ₁.symm
  have cart : IsGrpPullback P.A.A Y.oF.t.G z ψ := Y.m.cart.cancel n hψ₂
  have actA : ∀ x, (P.oA.act x).left ≫ k = k ≫ (t.act.act x).left := by
    intro x
    have e : P.oA.act x ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK R)).map (t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext x)).symm
    rw [hk, ← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)

  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have B₁ : LBIso (P.A.L.pull (𝟙 _)) (P.U.LG.L.pull k) :=
    LBIso.chartPull (chartPullSame P.A.L (fun _ => 𝟙 _) (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left
        (fun _ => hgi.symm))
      (chartPullSame P.U.LG.L (fun _ => k) (fun _ => pullback.fst t.G.hom (jK R)) _ P.U.gen.inv.left
        (fun _ => rfl)) P.U.ext
  have B₁' : LBIso P.A.L (t.PP.L.pull k) := by
    rw [← P.bundle]
    exact LBIso.chartPull (chartPullUnpull P.A.L (𝟙 _) rfl) (chartPullId _) B₁
  obtain ⟨w₂, -, g₂, -⟩ := rigIso_congr rfl m.cm m.lin rfl rfl
  have B₂ : LBIso (t.PP.L.pull k) (Y.t.PP.L.pull (ψ ≫ Y.m.φ)) :=
    LBIso.chartPull (chartPullPull t.PP.L k k rfl)
      (chartPullSame Y.t.PP.L (fun _ => ψ ≫ Y.m.φ) (fun _ => m.φ) _ k (fun _ => hψ₁.trans (Category.assoc _ _ _)))
      ⟨w₂, g₂⟩
  obtain ⟨w₃, -, g₃, -⟩ := rigIso_congr rfl Y.m.cm Y.m.lin rfl rfl
  have B₃ : LBIso (Y.oF.t.PP.L.pull ψ) (Y.t.PP.L.pull (ψ ≫ Y.m.φ)) :=
    LBIso.chartPull (chartPullPull Y.oF.t.PP.L ψ ψ rfl)
      (chartPullSame Y.t.PP.L (fun _ => ψ ≫ Y.m.φ) (fun _ => Y.m.φ) _ ψ (fun _ => rfl)) ⟨w₃, g₃⟩
  have BL : LBIso P.A.L (Y.oF.t.PP.L.pull ψ) :=
    LBIso.trans P.A.isLB (pull_isLB Y.t.PP.isLB _) (pull_isLB Y.oF.t.PP.isLB _)
      (LBIso.trans P.A.isLB (pull_isLB t.PP.isLB _) (pull_isLB Y.t.PP.isLB _) B₁' B₂) (LBIso.symm B₃)
  refine ⟨ψ, cart, BL, fun a => ?_, hψ₁.trans (Category.assoc _ _ _)⟩
  apply Y.m.cart.1.hom_ext
  · calc ((P.oA.act a).left ≫ ψ) ≫ Y.m.φ = (P.oA.act a).left ≫ k ≫ m.φ := by rw [Category.assoc, hψ₁]
      _ = k ≫ m.φ ≫ (Y.t.act.act a).left := by rw [← Category.assoc, actA, Category.assoc, m.act a]
      _ = (ψ ≫ (Y.oF.t.act.act a).left) ≫ Y.m.φ := by
        rw [Category.assoc ψ, Y.m.act a, ← Category.assoc ψ, hψ₁]; exact (Category.assoc _ _ _).symm
  · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w (P.oA.act a), Category.assoc, Over.w (Y.oF.t.act.act a), hψ₂]

end GlobalTheory.GenericFibreUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsPrismLocalizationAwayOfGenerated
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

variable {l : ℕ} {R : Type} [CommRing R]

theorem adI_pow_eq_map_of_map_I {B C : Obj l R} (h : Hom B C) (hI : B.I.map h.f = C.I) (m : ℕ) :
    adI C ^ m = (adI B ^ m).map h.f := by
  rw [Ideal.map_pow]
  congr 1
  simp only [adI, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast, hI]

theorem isLoc_of_locP (hrig : ∀ (B B' : Obj l R) (f : Hom B B'), B.I.map f.f = B'.I)
    {B : Obj l R} {s d : B.A} (L : LocP B s d) : IsLoc s L.inl := by
  have hJ : ∀ m, adI L.Q ^ m = (adI B ^ m).map L.inl.f :=
    adI_pow_eq_map_of_map_I L.inl (hrig _ _ _)
  refine ⟨fun m => ?_, fun Q a ha => ?_⟩
  · letI := (qmap L.inl m).toAlgebra
    have hmap : ∀ b : B.A, algebraMap (B.A ⧸ adI B ^ m) (L.Q.A ⧸ adI L.Q ^ m) (Ideal.Quotient.mk _ b) =
        Ideal.Quotient.mk _ (L.inl.f b) := fun b => rfl
    refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
    · rintro ⟨y, k, rfl⟩
      change IsUnit (algebraMap (B.A ⧸ adI B ^ m) (L.Q.A ⧸ adI L.Q ^ m) (Ideal.Quotient.mk _ s ^ k))
      rw [map_pow, hmap]
      exact (L.unit.map _).pow k
    · intro z
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨k, b, hkb⟩ := L.surj c m
      refine ⟨⟨Ideal.Quotient.mk _ b, ⟨Ideal.Quotient.mk _ s ^ k, k, rfl⟩⟩, ?_⟩
      change Ideal.Quotient.mk _ c * algebraMap (B.A ⧸ adI B ^ m) (L.Q.A ⧸ adI L.Q ^ m)
        (Ideal.Quotient.mk _ s ^ k) = algebraMap (B.A ⧸ adI B ^ m) (L.Q.A ⧸ adI L.Q ^ m) (Ideal.Quotient.mk _ b)
      rw [map_pow, hmap, hmap, ← map_pow, ← map_mul, Ideal.Quotient.eq, hJ, mul_comm]
      exact hkb
    · intro x y hxy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [hmap, hmap, Ideal.Quotient.eq, hJ, ← map_sub] at hxy
      obtain ⟨k, hk⟩ := L.ker (a - b) m hxy
      refine ⟨⟨Ideal.Quotient.mk _ s ^ k, k, rfl⟩, ?_⟩
      change Ideal.Quotient.mk _ s ^ k * Ideal.Quotient.mk _ a = Ideal.Quotient.mk _ s ^ k * Ideal.Quotient.mk _ b
      rw [← map_pow, ← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub]
      exact hk
  · obtain ⟨c, hc, -⟩ := L.univ Q a ha
    exact ⟨c, hc⟩

theorem exists_isLoc : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (s d : B.A), GenAway B s d →
    ∃ (C : Obj l R) (h : Hom B C), IsLoc s h ∧ C.I = Ideal.span {h.f d} := by
  intro l _ R _ B s d hg
  obtain ⟨L⟩ := _root_.GlobalTheory.BSP.GenAway₂ l R B s d hg
  exact ⟨L.Q, L.inl, isLoc_of_locP (GlobalTheory.T.prism_hom_map_ideal_eq l R) L, L.I_eq⟩

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKernelVectorMemOEOfFrobeniusStable
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.KernelDescent

theorem shape_mul {T : Type*} [CommRing T] {d : ℕ} (I : Finset (Fin d)) (P P' : Matrix (Fin d) (Fin d) T)
    (hP : ∀ i, ∀ j ∉ I, P i j = 0) (hP' : ∀ i ∈ I, ∀ j, P' i j = if i = j then 1 else 0) : P * P' = P := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · by_cases hj : j ∈ I
    · rw [hP' j hj j, if_pos rfl, mul_one]
    · rw [hP i j hj, zero_mul]
  · intro k _ hk
    by_cases hkI : k ∈ I
    · rw [hP' k hkI j, if_neg hk, mul_zero]
    · rw [hP i k hkI, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem mul_eq_of_ker {C : Type*} [CommRing C] {d : ℕ} (Y Q M : Matrix (Fin d) (Fin d) C)
    (hQ : ∀ v, Y.mulVec v = 0 → Q.mulVec v = v) (hM : Y * M = 0) : Q * M = M := by
  ext i j
  have h := hQ (fun k => M k j) (by
    funext a
    have := congrFun (congrFun hM a) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this)
  have := congrFun h i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

theorem shape_map {C T : Type*} [CommRing C] [CommRing T] {d : ℕ} (I : Finset (Fin d))
    (Q : Matrix (Fin d) (Fin d) C) (h₁ : ∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0)
    (h₂ : ∀ i, ∀ j ∉ I, Q i j = 0) (f g : C →+* T) : Q.map f * Q.map g = Q.map f := by
  refine shape_mul I _ _ (fun i j hj => ?_) (fun i hi j => ?_)
  · rw [Matrix.map_apply, h₂ i j hj, map_zero]
  · rw [Matrix.map_apply, h₁ i hi j]
    split_ifs
    · exact map_one g
    · exact map_zero g

theorem two_copies {l : ℕ} [Fact l.Prime] {C : Type} [Field C] [CharP C l] {d : ℕ} (I : Finset (Fin d))
    (A Q Λ : Matrix (Fin d) (Fin d) C) (h₁ : ∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0)
    (h₂ : ∀ i, ∀ j ∉ I, Q i j = 0) (hΛ : Q = A * Q.map (frobenius C l) * Λ)
    (hQA : Q * (A * Q.map (frobenius C l)) = A * Q.map (frobenius C l))
    (T : Type) [CommRing T] (i₁ i₂ : C →+* T) (hA : A.map i₁ = A.map i₂) :
    ∃ c : Fin d × Fin d → Fin d × Fin d → T, ∀ j : Fin d × Fin d,
      i₁ (Q j.1 j.2) - i₂ (Q j.1 j.2) = ∑ i : Fin d × Fin d, (i₁ (Q i.1 i.2) - i₂ (Q i.1 i.2)) ^ l * c i j := by
  rcases subsingleton_or_nontrivial T with hT | hT
  · exact ⟨0, fun _ => Subsingleton.elim _ _⟩
  haveI : CharP T l := charP_of_injective_ringHom i₁.injective l
  have e1 : Q.map i₂ * Q.map i₁ = Q.map i₂ := shape_map I Q h₁ h₂ i₂ i₁
  have e2 : Q.map i₁ = A.map i₂ * (Q.map (frobenius C l)).map i₁ * Λ.map i₁ := by
    rw [← hA, ← Matrix.map_mul, ← Matrix.map_mul, ← hΛ]
  have e3 : Q.map i₂ * (A.map i₂ * (Q.map (frobenius C l)).map i₂) = A.map i₂ * (Q.map (frobenius C l)).map i₂ := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hQA]
  have e4 : Q.map i₁ - Q.map i₂ = ((1 - Q.map i₂) * A.map i₂) *
      ((Q.map (frobenius C l)).map i₁ - (Q.map (frobenius C l)).map i₂) * Λ.map i₁ := by
    have a1 : ((1 - Q.map i₂) * A.map i₂) * (Q.map (frobenius C l)).map i₂ = 0 := by
      rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, e3, sub_self]
    rw [Matrix.mul_sub, a1, sub_zero, Matrix.mul_assoc (1 - Q.map i₂), Matrix.mul_assoc (1 - Q.map i₂), ← e2,
      Matrix.sub_mul, Matrix.one_mul, e1]
  refine ⟨fun i j => ((1 - Q.map i₂) * A.map i₂) j.1 i.1 * i₁ (Λ i.2 j.2), fun j => ?_⟩
  have := congrFun (congrFun e4 j.1) j.2
  rw [Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply] at this
  rw [this, Matrix.mul_apply, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.sub_apply, Matrix.map_apply, frobenius_def, map_pow, sub_pow_char]
  ring

theorem invariant {C : Type} [CommRing C] {d : ℕ} (I : Finset (Fin d))
    (Y Q R : Matrix (Fin d) (Fin d) C) (h₀ : Y * Q = 0) (hQ : ∀ v, Y.mulVec v = 0 → Q.mulVec v = v)
    (h₁ : ∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0)
    (h₂ : ∀ i, ∀ j ∉ I, Q i j = 0) (g : C →+* C) (hR : R * Y.map g = Y) : Q.map g = Q := by
  have a1 : Y * Q.map g = 0 := by
    rw [← hR, Matrix.mul_assoc, ← Matrix.map_mul, h₀, Matrix.map_zero _ (map_zero g), Matrix.mul_zero]
  have a2 := mul_eq_of_ker Y Q _ hQ a1
  have a3 : Q * Q.map g = Q := shape_map I Q h₁ h₂ (RingHom.id C) g
  rw [← a2, a3]

end GlobalTheory.BSP.KernelDescent

namespace GlobalTheory.BSP


open KernelDescent in
theorem exists_ker_vector_mem_OE : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (Y A : Matrix (Fin d) (Fin d) (Cb l)), A.det ≠ 0 → (∀ i j, A i j ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l))) → Y.map (frobenius (Cb l) l) = Y * A → (∀ g : ↥(GK K), bk.FixFlat g → ∃ R : Matrix (Fin d) (Fin d) (Cb l), IsUnit R ∧ R * Y.map (autCb l (galTilt l (g : GQ l))) = Y) → Y.det = 0 → ∃ v : Fin d → Cb l, v ≠ 0 ∧ (∀ i, v i ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l))) ∧ Y.mulVec v = 0 := by
  intro l _ K bk d Y A hA hAm hY hg hdet
  obtain ⟨I, Q, Λ, h₀, hQ, h₁, h₂, hΛ⟩ := GlobalTheory.T.echelon_projector_kernel_frobenius l (Cb l) d Y A hA hY
  have hQA : Q * (A * Q.map (frobenius (Cb l) l)) = A * Q.map (frobenius (Cb l) l) := by
    refine mul_eq_of_ker Y Q _ hQ ?_
    rw [← Matrix.mul_assoc, ← hY, ← Matrix.map_mul, h₀, Matrix.map_zero _ (map_zero _)]
  have hmem := GlobalTheory.T.tilt_invariant_mem_reduction_of_frobenius_equation l K bk (Fin d × Fin d) (fun j => Q j.1 j.2) (fun g hgf j => by
    obtain ⟨R, -, hR⟩ := hg g hgf
    have := invariant I Y Q R h₀ hQ h₁ h₂ (autCb l (galTilt l (g : GQ l)) : Cb l →+* Cb l) hR
    exact congrFun (congrFun this j.1) j.2) (fun T _ i₁ i₂ h =>
      two_copies I A Q Λ h₁ h₂ hΛ hQA T i₁ i₂ (by
        ext i j
        exact h _ (hAm i j)))
  obtain ⟨v, hv, hYv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hne : ∃ j, (fun i => Q i j) ≠ 0 := by
    by_contra hc
    push Not at hc
    have : Q = 0 := by
      ext i j
      exact congrFun (hc j) i
    apply hv
    rw [← hQ v hYv, this, Matrix.zero_mulVec]
  obtain ⟨j, hj⟩ := hne
  refine ⟨fun i => Q i j, hj, fun i => hmem (i, j), ?_⟩
  funext a
  have := congrFun (congrFun h₀ a) j
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSpanCornerSeparable
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.SpanRing

theorem exists_mem_span_corner_separable {K Γ : Type} [Field K] [Infinite K] [Group Γ] {n t : ℕ}
    (σ : Γ →* Matrix (Fin n) (Fin n) K) (a : Matrix (Fin n) (Fin t) K)
    (b : Matrix (Fin t) (Fin n) K) (h : AbsIrrDistinct (matRep σ)) (hba : b * a = 1)
    (hab : a * b ∈ Submodule.span K (Set.range σ)) :
    ∃ m ∈ Submodule.span K (Set.range σ), (b * m * a).charpoly.Separable := by
  obtain ⟨ι, _, _, Vs, hs, hint, -, hspan, hdist⟩ := h
  have hstab : ∀ j, ∀ M ∈ Submodule.span K (Set.range σ), ∀ v ∈ Vs j, M.mulVec v ∈ Vs j := by
    intro j M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      intro v hv
      exact hs j g v hv
    | zero => intro v _; simp
    | add x y _ _ hx hy =>
      intro v hv
      rw [Matrix.add_mulVec]
      exact (Vs j).add_mem (hx v hv) (hy v hv)
    | smul c x _ hx =>
      intro v hv
      rw [show (c • x).mulVec v = c • x.mulVec v by
        ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]]
      exact (Vs j).smul_mem c (hx v hv)
  obtain ⟨m, hm, hsep⟩ := _root_.GlobalTheory.SpanRing.exists_corner_separable_charpoly ι Vs a b hint hba (fun j => hstab j _ hab)
  refine ⟨m, ?_, hsep⟩
  have hlin := GlobalTheory.T.span_representation_density_of_isInternal_constituents (matRep σ) ι Vs hs hint hspan hdist (Matrix.toLin' m)
    (fun j v hv => by simpa [Matrix.toLin'_apply] using hm j v hv)
  have hfun : (⇑(matRep σ)) = ⇑(Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K] _) ∘ ⇑σ := rfl
  rw [hfun, Set.range_comp] at hlin
  have hle : Submodule.span K (⇑(Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K] _) '' Set.range ⇑σ) ≤
      (Submodule.span K (Set.range σ)).map
        (Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K] _).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨M, hM, rfl⟩
    exact ⟨M, Submodule.subset_span hM, rfl⟩
  obtain ⟨y, hy, hye⟩ := hle hlin
  have hym : y = m := Matrix.toLin'.injective hye
  rwa [hym] at hy

end GlobalTheory.SpanRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLevelCupSwapCoboundaryIffStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_level_cup_swap_coboundary_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), ∀ s ∈ quotientCocycles LA _ hI, ∀ d : ↥(latticeCocycles LA'), CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r s (redT LA' _ d)) ↔ CobO (P.PD K) L1 (cupLD LA m.flip (d : ↥(GK K) → A'.V) (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (s g))) := by
  first | exact @GlobalTheory.BKSwapCup.cobO_cupQ_iff | exact GlobalTheory.BKSwapCup.cobO_cupQ_iff | (intros; apply GlobalTheory.BKSwapCup.cobO_cupQ_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaFixesMaximalUnramifiedExtensionQl
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing

namespace GlobalTheory.InertQlUnr

theorem IK_qlExt_fixes_Kur : ∀ (l : ℕ) [Fact l.Prime] (g : ↥(GK (Formalism.MainNotions.ElementDenominator.qlExt l))), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) → ∀ x ∈ MaximalUnramifiedExtension l, (g : GQ l) x = x := by
  intro l _ g hg x hx
  exact GlobalTheory.InerQl.IK_fixes_Kur _ hg hx

end GlobalTheory.InertQlUnr
end

