module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValDetSubOneLt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedCompAtDetIdl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TildeQDetPtEqChiId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdeleEquivFin
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.Th
open Formalism.L2.JoinChr Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace GlobalTheory.DetRootRead

theorem exists_adele_equiv_fin (D : D7)
    (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (hι : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x)
    (hint : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) :
    ∃ Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E, Continuous Φ ∧ Continuous Φ.symm ∧
      (∀ x : D.host.E, Φ (incA D x) = algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) x) ∧
      (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ k : D.host.Eˣ,
        Φ (locE D e (k : D.host.E)) =
          ((localIdele D.host.E P (atFin P k) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E)) ∧
      ∀ z : AE D, ((Φ z).1 = 1 → infPart D z = 1) ∧ (Φ z).2 = ι (finPart D z) := by
  obtain ⟨hιc, hιc'⟩ := GlobalTheory.HeckeTensorRead.continuous_finite_equiv D ι hint
  obtain ⟨j, hjc, hjc', hj⟩ := GlobalTheory.HeckeTensorRead.exists_infinite_equiv D.host.F D.host.E D.sp.cm.sig
    ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, D.sp.cm.cmUnram.2.1⟩
  obtain ⟨s, hs, hsc, hsc'⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  let Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E := s.trans (j.prodCongr ι)
  have hΦ : ∀ z, Φ z = (j (infPart D z), ι (finPart D z)) := fun z =>
    Prod.ext (congrArg j (hs z).1) (congrArg ι (hs z).2)
  refine ⟨Φ, (hjc.prodMap hιc).comp hsc, hsc'.comp (hjc'.prodMap hιc'), fun x => ?_, fun P e he k => ?_,
    fun z => ⟨fun h => ?_, by rw [hΦ]⟩⟩
  · rw [hΦ]
    exact Prod.ext (hj x) (hι x)
  · obtain ⟨h1, h2, h3⟩ := GlobalTheory.HeckeTensorRead.isPlIdem_parts D ι hι hint he
    rw [hΦ]
    refine Prod.ext ?_ ?_
    · have h5 : j (infPart D e) = 0 := by rw [h1]; exact j.map_zero
      exact (GlobalTheory.HeckeTensorRead.map_loc (j.toRingHom.comp (infPart D)) e _).trans (by
        change 1 + j (infPart D e) * _ = 1
        rw [h5, zero_mul, add_zero])
    · have h4 : ι (finPart D (incA D (k : D.host.E))) = algebraMap D.host.E _ (k : D.host.E) := hι k
      refine (GlobalTheory.HeckeTensorRead.map_loc (ι.toRingHom.comp (finPart D)) e _).trans ?_
      exact GlobalTheory.HeckeTensorRead.loc_eq_finSingle P _ _ _ h4 h2 h3
  · rw [hΦ] at h
    exact j.injective (h.trans j.map_one.symm)

theorem read_of_equiv (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (h : ChrEq c χ)
    (Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E) (hΦ : Continuous Φ.symm)
    (h1 : ∀ x : D.host.E, Φ (incA D x) = algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) x)
    (h2 : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ k : D.host.Eˣ,
        Φ (locE D e (k : D.host.E)) =
          ((localIdele D.host.E P (atFin P k) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E))
    (z : (AE D)ˣ) : ((c z : Circle) : ℂ) = ((χ.1 (Units.map Φ.toRingHom.toMonoidHom z) : ℂˣ) : ℂ) := by
  let u : Ideles D.host.E →* (AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦ
  have ht : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, by
      have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
      refine h.congr fun z => ?_
      simp⟩
  let χ' : HChar D.host.E := ⟨Circle.toUnits.comp (MonoidHom.comp c u), ht.comp (h.1.1.comp hu), fun k => by
    have : u (diagUnits D.host.E k) = Units.map (incA D).toMonoidHom k :=
      Units.ext (Φ.symm_apply_eq.2 (h1 k).symm)
    change Circle.toUnits (c (u _)) = 1
    rw [this, h.1.2, map_one]⟩
  have h' : ChrEq c χ' := ⟨h.1, fun P e he k x hx => by
    have : x = u (localIdele D.host.E P (atFin P k)) :=
      Units.ext (Φ.eq_symm_apply.2 (by rw [hx, h2 P e he k]))
    rw [this]
    rfl⟩
  rw [GlobalTheory.ChrEqUnique.hchar_unique D c χ χ' h h']
  have : u (Units.map Φ.toRingHom.toMonoidHom z) = z := Units.ext (Φ.symm_apply_apply _)
  show ((c z : Circle) : ℂ) = ((Circle.toUnits (c (u (Units.map Φ.toRingHom.toMonoidHom z))) : ℂˣ) : ℂ)
  rw [this]
  rfl

theorem comm_sigR (D : D7) (w : Af D.host.F ⊗[D.host.F] D.host.E) :
    Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (sigR (Af D.host.F) D.sp.cm.sig w) =
      Formalism.UG.sigR D.sp.cm.sig (Af D.host.F) (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add v w hv hw => rw [RingHom.map_add (f := _), map_add (f := _), hv, hw, map_add (f := _), RingHom.map_add (f := _)]

end GlobalTheory.DetRootRead

namespace GlobalTheory.DetRootRead


set_option maxHeartbeats 1000000 in
theorem chr_at_detRoot : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → χ.TrivOn D.host.F →
  ∀ (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (y : GL (Fin n) (Formalism.L2.DIV.AfE D.host.F D.host.E)), g ∈ GfC V →
    finM V hn g = (y : Matrix (Fin n) (Fin n) (Formalism.L2.DIV.AfE D.host.F D.host.E)) → ∀ x, IsDetRoot V g x → ∀ a : Neutral.B1.Ideles D.host.E,
      IsDetLift (host_cmData D.R D.host) y a → (c x : ℂ) = ((χ.1 (Chr.finPartI D.host.E a) : ℂˣ) : ℂ) := by
  intro D c χ hc ht V n hn g y hg hy x hx a ha
  let ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv.trans (afIso D.host.F D.host.E)
  have hι : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x := fun x => afIso_tmul_one _ _ x
  have hint : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1 := fun y =>
    (GlobalTheory.HostAdeleIso.mem_intAE_iff_comm D y).trans (mem_rInt_iff _ _ _)
  obtain ⟨Φ, -, hΦ', h1, h2, h3⟩ := exists_adele_equiv_fin D ι hι hint
  let b : (AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom (Chr.finPartI D.host.E a)
  have hbΦ : Φ (b : AE D) = ((Chr.finPartI D.host.E a : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E) :=
    Φ.apply_symm_apply _
  have hbinf : infPart D (b : AE D) = 1 := (h3 _).1 (by rw [hbΦ]; rfl)
  have hbfin : Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D (b : AE D)) =
      (finAf D.host.F D.host.E a : Formalism.L2.DIV.AfE D.host.F D.host.E) := by
    apply (afIso D.host.F D.host.E).injective
    rw [afIso_finAf]
    have := (h3 (b : AE D)).2
    rw [hbΦ] at this
    exact this.symm
  have hcb : ((c b : Circle) : ℂ) = ((χ.1 (Chr.finPartI D.host.E a) : ℂˣ) : ℂ) := by
    rw [read_of_equiv D c χ hc Φ hΦ' h1 h2 b]
    have hb' : Units.map Φ.toRingHom.toMonoidHom b = Chr.finPartI D.host.E a := Units.ext hbΦ
    rw [hb']
  rw [← hcb]
  obtain ⟨d, hd_def⟩ : ∃ d : AE D, d = ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det := ⟨_, rfl⟩
  have hdinf : infPart D d = 1 := by rw [hd_def]; exact GlobalTheory.DetOnto.infPart_det V g hg
  have hdfin : Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D d) =
      ((Matrix.GeneralLinearGroup.det y : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← hy]
    unfold GlobalTheory.AdForm.finM
    rw [Matrix.det_reindex_self, hd_def]
    exact (Formalism.IndefR.Datum.toEAf D).map_det (mt V g)
  have hfa : (finAf D.host.F D.host.E a : Formalism.L2.DIV.AfE D.host.F D.host.E) =
      ((Matrix.GeneralLinearGroup.det y : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E) *
        Formalism.UG.sigR D.sp.cm.sig (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (finAf D.host.F D.host.E a : Formalism.L2.DIV.AfE D.host.F D.host.E) := by
    unfold IsDetLift Formalism.L2.DIV.h90 at ha
    rw [MonoidHom.div_apply, div_eq_iff_eq_mul] at ha
    exact congrArg Units.val ha
  have hbfin' : finPart D (b : AE D) = finPart D d * sigR (Af D.host.F) D.sp.cm.sig (finPart D (b : AE D)) := by
    apply (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
    have e1 := comm_sigR D (finPart D (b : AE D))
    rw [hbfin] at e1
    refine hbfin.trans (hfa.trans ?_)
    refine Eq.trans ?_ (map_mul (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) _ _).symm
    rw [hdfin, e1]
  obtain ⟨s, hs, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have split : ∀ z w : AE D, infPart D z = infPart D w → finPart D z = finPart D w → z = w := fun z w hi hf =>
    s.injective (Prod.ext ((hs z).1.trans (hi.trans (hs w).1.symm)) ((hs z).2.trans (hf.trans (hs w).2.symm)))
  have hbd : (b : AE D) = d * sigR (AF D.host.F) D.sp.cm.sig (b : AE D) := by
    refine split _ _ ?_ ?_
    · rw [RingHom.map_mul, GlobalTheory.DetOnto.infPart_sigR, hbinf, hdinf, map_one, one_mul]
    · rw [RingHom.map_mul, GlobalTheory.DetRootChar.finPart_sigR]
      exact hbfin'
  let σU : (AE D)ˣ →* (AE D)ˣ := Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom
  have key : x * σU b = σU x * b := by
    apply Units.ext
    change (x : AE D) * sigR (AF D.host.F) D.sp.cm.sig (b : AE D) = sigR (AF D.host.F) D.sp.cm.sig (x : AE D) * (b : AE D)
    have hx' : (x : AE D) = d * sigR (AF D.host.F) D.sp.cm.sig (x : AE D) := by rw [hd_def]; exact hx
    conv_lhs => rw [hx']
    conv_rhs => rw [hbd]
    ring
  let q : (AE D)ˣ := x * b⁻¹
  have hq : σU q = q := by
    change σU (x * b⁻¹) = x * b⁻¹
    rw [map_mul, map_inv, mul_inv_eq_iff_eq_mul, mul_right_comm, eq_mul_inv_iff_mul_eq]
    exact key.symm
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
    intro x
    apply (D.sp.cm.fixed _).1
    change D.sp.cm.sig _ = _
    rw [map_add (f := _), hσ, add_comm]
  obtain ⟨t, htq⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (AF D.host.F) D.sp.cm.sig htr q (congrArg Units.val hq)
  have hcq : c q = 1 := by
    rw [← htq]
    exact GlobalTheory.GridWeil.triv_base hc ht t
  have hxq : x = q * b := by simp [q]
  rw [hxq, map_mul, hcq, one_mul]

end GlobalTheory.DetRootRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitPt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_eq_zero_of_toEAf (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (a : AE D) (ha : toEAf D a = 0) : q.pr a = 0 := by
  have h0 : infPart D q.e = 0 := (GlobalTheory.IdemSupport.delta_of_isIdemAt (GlobalTheory.StdFrames.comp_toAd D) he).1
  have h1 : finPart D a = 0 :=
    (Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E).injective (by
      rw [map_zero]; exact ha)
  have h2 : q.e * a = 0 := GlobalTheory.LatVac.eq_zero_of_parts _ (by rw [map_mul, h0, zero_mul]) (by rw [map_mul, h1, mul_zero])
  rw [← q.pr_sec (q.pr a), q.sec_pr, h2, map_zero]

def prF (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) : EAf D →+* k :=
  (RingHom.liftOfSurjective (toEAf D) (fun s => GlobalTheory.ResLoc.toEAf_surj s))
    ⟨q.pr, fun a ha => (RingHom.mem_ker).2 (q.pr_eq_zero_of_toEAf he a ((RingHom.mem_ker).1 ha))⟩

theorem prF_toEAf (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (a : AE D) :
    q.prF he (toEAf D a) = q.pr a :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem pr_mem_iff (q : SplitPt D k) (a : AE D) :
    q.pr a ∈ 𝒪[k] ↔ toEAf D q.e * toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [q.int_iff, q.sec_pr, ← map_mul]
  exact ⟨GlobalTheory.IdemRes.toEAf_mem_of_finPart, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf⟩

end GlobalTheory.FinPl.SplitPt

namespace GlobalTheory.FinPl.SplitPt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_iff_val_lt (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (x : 𝓞 D.host.E) : x ∈ PP.asIdeal ↔
      valuation k (q.prF he (Formalism.L2.DIV.oToS D.host.F D.host.E x : EAf D)) < 1 := by
  have e1 : ((Formalism.L2.DIV.oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      toEAf D (incA D (x : D.host.E)) := rfl
  rw [e1, prF_toEAf]
  by_cases hx : x = 0
  · subst hx
    simp only [map_zero, Submodule.zero_mem, true_iff]
    simp
  have hx' : (x : D.host.E) ≠ 0 := fun h => hx (RingOfIntegers.coe_eq_zero_iff.1 h)
  set y := q.pr (incA D (x : D.host.E)) with hy
  have hy0 : y ≠ 0 := fun h => by
    have : (q.pr.comp (incA D)) (x : D.host.E) = 0 := h
    exact hx' ((map_eq_zero_iff _ (q.pr.comp (incA D)).injective).1 this)
  have hinv : q.pr (incA D ((x : D.host.E)⁻¹)) = y⁻¹ := map_inv₀ (q.pr.comp (incA D)) _
  rw [he.2 x hx, ← q.sec_pr, ← q.int_iff, hinv]
  change ¬ valuation k y⁻¹ ≤ 1 ↔ _
  rw [not_le, Valuation.one_lt_val_iff _ (inv_ne_zero hy0), inv_inv]

theorem val_lt_of_mem_idS (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    {s : Formalism.L2.Herm.intAf D.host.F D.host.E} (hs : s ∈ Formalism.L2.DIV.idS D.host.F PP.asIdeal) :
    valuation k (q.prF he s.1) < 1 := by
  have hint : ∀ c : Formalism.L2.Herm.intAf D.host.F D.host.E, valuation k (q.prF he c.1) ≤ 1 := fun c => by
    obtain ⟨a, ha⟩ := GlobalTheory.ResLoc.toEAf_surj c.1
    have := (q.pr_mem_iff a).2 (by rw [ha]; exact mul_mem (GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he).1 c.2)
    rw [← ha, prF_toEAf]; exact this
  refine Submodule.span_induction (p := fun s _ => valuation k (q.prF he s.1) < 1) ?_ ?_ ?_ ?_ hs
  · rintro _ ⟨a, ha, rfl⟩
    exact (q.mem_iff_val_lt he a).1 ha
  · simp
  · intro x y _ _ hx hy
    rw [Subring.coe_add, map_add (f := _)]
    exact Valuation.map_add_lt _ hx hy
  · intro c x _ hx
    rw [smul_eq_mul, Subring.coe_mul, map_mul, Valuation.map_mul]
    exact (mul_le_mul_of_nonneg_right (hint c) zero_le').trans_lt (by rwa [one_mul])

theorem resS_eq_zero_of_mem {PP : Formalism.L2.DIV.Pl D.host.E} {s : Formalism.L2.Herm.intAf D.host.F D.host.E}
    (hs : s ∈ Formalism.L2.DIV.idS D.host.F PP.asIdeal) : Formalism.L2.DIV.resS D.host.F PP s = 0 := by
  have : Formalism.L2.DIV.idS D.host.F PP.asIdeal ≤ RingHom.ker (Formalism.L2.DIV.resS D.host.F PP) :=
    Ideal.map_le_iff_le_comap.2 fun b hb => Ideal.mem_comap.2 ((RingHom.mem_ker).2 (by
      rw [Formalism.L2.DIV.resS_oToS]; exact Ideal.Quotient.eq_zero_iff_mem.2 hb))
  exact (RingHom.mem_ker).1 (this hs)

end GlobalTheory.FinPl.SplitPt

namespace GlobalTheory.FinPl.SplitPt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prF_mem_iff (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (z : EAf D) :
    q.prF he z ∈ 𝒪[k] ↔ toEAf D q.e * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨a, rfl⟩ := GlobalTheory.ResLoc.toEAf_surj z
  rw [prF_toEAf]; exact q.pr_mem_iff a

theorem resS_eq_zero_iff (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (s : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    Formalism.L2.DIV.resS D.host.F PP s = 0 ↔ valuation k (q.prF he s.1) < 1 := by
  obtain ⟨a, ha0⟩ := GlobalTheory.FunObj.Comparison₂.exists_approx PP.ne_bot s
  have ha : s - Formalism.L2.DIV.oToS D.host.F D.host.E a ∈ Formalism.L2.DIV.idS D.host.F PP.asIdeal := ha0
  have h1 : Formalism.L2.DIV.resS D.host.F PP s = Ideal.Quotient.mk PP.asIdeal a := by
    rw [← Formalism.L2.DIV.resS_oToS (F := D.host.F) PP a, ← sub_eq_zero, ← map_sub]
    exact resS_eq_zero_of_mem ha
  have h2 := q.val_lt_of_mem_idS he ha
  have e2 : ((s - Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      (s : EAf D) - ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := rfl
  rw [e2, RingHom.map_sub] at h2
  rw [h1, Ideal.Quotient.eq_zero_iff_mem, q.mem_iff_val_lt he]
  constructor
  · intro h; simpa using Valuation.map_add_lt _ h2 h
  · intro h; simpa using Valuation.map_sub_lt _ h h2

theorem mem_intAf_iff (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (z : EAf D) :
    z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ q.prF he z ∈ 𝒪[k] := by
  obtain ⟨hint, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he
  rw [q.prF_mem_iff he]
  constructor
  · intro hz
    exact ⟨mul_mem (sub_mem (one_mem _) hint) hz, mul_mem hint hz⟩
  · rintro ⟨h1, h2⟩
    have : z = (1 - toEAf D q.e) * z + toEAf D q.e * z := by
      rw [sub_mul, one_mul, sub_add_cancel]
    rw [this]; exact add_mem h1 h2

set_option maxHeartbeats 1000000 in
theorem resS_off (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (PP' : Formalism.L2.DIV.Pl D.host.E) (hne : PP' ≠ PP) (z : EAf D) (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hz' : (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    Formalism.L2.DIV.resS D.host.F PP' ⟨(1 - toEAf D q.e) * z, hz'⟩ = Formalism.L2.DIV.resS D.host.F PP' ⟨z, hz⟩ := by
  obtain ⟨hint, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he
  have h0 : Formalism.L2.DIV.resS D.host.F PP' ⟨toEAf D q.e, hint⟩ = 0 := by
    obtain ⟨a, h1, h2⟩ := GlobalTheory.FunObj.Comparison₂.exists_resS_eq PP' ⟨toEAf D q.e, hint⟩
    rw [h1, GlobalTheory.FunObj.Comparison₂.mk_eq_zero_iff]
    rw [GlobalTheory.FunObj.Comparison₂.cptO_apply PP' ⟨toEAf D q.e, hint⟩] at h2
    change Valued.v (GlobalTheory.StdFrames.cpt PP' (toEAf D q.e) - _) < 1 at h2
    rw [(GlobalTheory.StdFrames.cpt_of_isIdemAt he).2 PP' hne, zero_sub, Valuation.map_neg] at h2
    exact h2
  have e1 : (⟨(1 - toEAf D q.e) * z, hz'⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      (1 - ⟨toEAf D q.e, hint⟩) * ⟨z, hz⟩ :=
    Subtype.ext (by rw [Subring.coe_mul, AddSubgroupClass.coe_sub, OneMemClass.coe_one])
  refine (congrArg (Formalism.L2.DIV.resS D.host.F PP') e1).trans ?_
  rw [map_mul, map_sub, map_one, h0, sub_zero, one_mul]

end GlobalTheory.FinPl.SplitPt

namespace GlobalTheory.FinPl.SplitPt

theorem exists_lift_isRed : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∃ π' : EAf D →+* k, (∀ a, π' (toEAf D a) = q.pr a) ∧ GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) ∧ (∀ z : EAf D, z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ π' z ∈ 𝒪[k]) ∧ ∀ PP' : Formalism.L2.DIV.Pl D.host.E, PP' ≠ PP → ∀ (z : EAf D) (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hz' : (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.resS D.host.F PP' ⟨(1 - toEAf D q.e) * z, hz'⟩ = Formalism.L2.DIV.resS D.host.F PP' ⟨z, hz⟩ := by
  intro D k _ _ _ _ q PP he
  obtain ⟨hint, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he
  refine ⟨q.prF he, q.prF_toEAf he, ⟨(Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 PP.isMaximal,
    fun s => (q.prF_mem_iff he s.1).2 (mul_mem hint s.2), fun s => q.resS_eq_zero_iff he s⟩,
    q.mem_intAf_iff he, fun PP' hne z hz hz' => q.resS_off he PP' hne z hz hz'⟩

end GlobalTheory.FinPl.SplitPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFrameCol
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KappaModel

def finv {k : Type} [Field k] [MeasurableSpace k] {n : Type} [Fintype n] (ψk : AddChar k Circle) (ν : Measure k) (C : ℂ)
    (Φ : Matrix Unit n k → ℂ) (x : Matrix n Unit k) : ℂ :=
  C * ∫ η : n → k, Φ (Matrix.of fun _ r => η r) * (ψk (η ⬝ᵥ fun r => x r ()) : ℂ) ∂(Measure.pi fun _ => ν)

end GlobalTheory.KappaModel

namespace GlobalTheory.KappaModel
open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem integrable_row (ψk : AddChar k Circle) (hψ : Continuous ψk) (ν : Measure k) [ν.IsAddHaarMeasure]
    {Φ : Matrix Unit n k → ℂ} (hΦ : Φ ∈ SB (Matrix Unit n k)) (x : Matrix n Unit k) :
    Integrable (fun η : n → k => Φ (Matrix.of fun _ r => η r) * (ψk (η ⬝ᵥ fun r => x r ()) : ℂ)) (Measure.pi fun _ => ν) := by
  have := secondCountable k
  have := t2Space k
  let e : (n → k) ≃ₜ Matrix Unit n k :=
    { toFun := fun η => Matrix.of fun _ r => η r
      invFun := fun M => M ()
      left_inv := fun _ => rfl
      right_inv := fun M => by ext i j; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have h1 : Continuous fun η : n → k => Φ (Matrix.of fun _ r => η r) := hΦ.1.continuous.comp e.continuous
  have h2 : HasCompactSupport fun η : n → k => Φ (Matrix.of fun _ r => η r) := hΦ.2.comp_homeomorph e
  refine Continuous.integrable_of_hasCompactSupport (h1.mul ?_) h2.mul_right
  exact continuous_subtype_val.comp (hψ.comp (by fun_prop))

theorem finv_add (ψk : AddChar k Circle) (hψ : Continuous ψk) (ν : Measure k) [ν.IsAddHaarMeasure] (C : ℂ)
    {Φ Ψ : Matrix Unit n k → ℂ} (hΦ : Φ ∈ SB (Matrix Unit n k)) (hΨ : Ψ ∈ SB (Matrix Unit n k)) :
    finv ψk ν C (Φ + Ψ) = finv ψk ν C Φ + finv ψk ν C Ψ := by
  funext x
  simp only [finv, Pi.add_apply, add_mul]
  rw [integral_add (integrable_row ψk hψ ν hΦ x) (integrable_row ψk hψ ν hΨ x), mul_add]

theorem finv_smul (ψk : AddChar k Circle) (ν : Measure k) (C a : ℂ) (Φ : Matrix Unit n k → ℂ) :
    finv ψk ν C (a • Φ) = a • finv ψk ν C Φ := by
  funext x
  simp only [finv, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  ring

theorem finv_trans (ψk : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (C : ℂ) (x : Matrix Unit n k)
    {Φ Φ' : Matrix Unit n k → ℂ} (h : ∀ t, Φ' t = Φ (t + x)) (a : Matrix n Unit k) :
    finv ψk ν C Φ' a = (ψk (-(∑ r, x () r * a r ())) : ℂ) * finv ψk ν C Φ a := by
  have := secondCountable k
  simp only [finv, h]
  rw [mul_left_comm]
  congr 1
  rw [← integral_const_mul]
  conv_lhs => rw [← integral_add_right_eq_self _ (fun r => -(x () r))]
  congr 1
  funext η
  have e1 : (Matrix.of fun _ r => (η + fun r => -(x () r)) r : Matrix Unit n k) + x = Matrix.of fun _ r => η r := by
    ext i j; simp [Subsingleton.elim i ()]
  rw [e1]
  have e2 : (η + fun r => -(x () r)) ⬝ᵥ (fun r => a r ()) = (η ⬝ᵥ fun r => a r ()) + -(∑ r, x () r * a r ()) := by
    simp only [dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib]
  rw [e2, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

theorem finv_mod (ψk : AddChar k Circle) (ν : Measure k) (C : ℂ) (t₀ : Matrix n Unit k)
    {Φ Φ' : Matrix Unit n k → ℂ} (h : ∀ t, Φ' t = (ψk (∑ r, t () r * t₀ r ()) : ℂ) * Φ t) (a : Matrix n Unit k) :
    finv ψk ν C Φ' a = finv ψk ν C Φ (a + t₀) := by
  simp only [finv, h]
  congr 1
  congr 1
  funext η
  have e : (η ⬝ᵥ fun r => (a + t₀) r ()) = (η ⬝ᵥ fun r => a r ()) + ∑ r, η r * t₀ r () := by
    simp [dotProduct, mul_add, Finset.sum_add_distrib]
  rw [e, AddChar.map_add_eq_mul, Circle.coe_mul]
  simp only [Matrix.of_apply]
  ring

end GlobalTheory.KappaModel

namespace GlobalTheory.KappaModel
open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj)

theorem heis_comp {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (L S L'' : HSp D) (κ : WO S L'' → WO L S)
    (hadd : ∀ w w', κ (w + w') = κ w + κ w') (hs : ∀ w w', symplO L S (κ w) (κ w') = symplO S L'' w w')
    (u : WO S L'') (f : WO L S → ℂ) :
    (fun w => heisO ψ L S (κ u) f (κ w)) = heisO ψ S L'' u (fun w => f (κ w)) := by
  funext w
  simp only [heisO, symplOH, hs, hadd]

theorem exists_frame_col {k : Type} [Field k] {N : ℕ} (hN : N = 1) (z₀ : Fin N → k) (hz : z₀ ≠ 0) :
    ∃ F : Frame k N Unit, ∀ r, F.β r () = z₀ r := by
  let i₀ : Fin N := ⟨0, by omega⟩
  have hu : ∀ i : Fin N, i = i₀ := fun i => Fin.ext (by omega)
  have h0 : z₀ i₀ ≠ 0 := fun h => hz (funext fun i => by rw [hu i]; exact h)
  refine ⟨⟨Matrix.of fun r _ => z₀ r, Matrix.of fun _ _ => (z₀ i₀)⁻¹, ?_, ?_⟩, fun _ => rfl⟩
  · ext i j
    rw [hu i, hu j, Matrix.mul_apply, Matrix.one_apply_eq]
    simp [h0]
  · ext i j
    rw [Matrix.mul_apply, Subsingleton.elim i j, Matrix.one_apply_eq, Fintype.sum_eq_single i₀ fun x hx => absurd (hu x) hx]
    simp [h0]

end GlobalTheory.KappaModel
end
end

