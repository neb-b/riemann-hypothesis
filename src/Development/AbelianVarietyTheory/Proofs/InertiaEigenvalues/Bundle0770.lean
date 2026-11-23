module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0766
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0838
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicValueSpaceMapEqDualWeylModuleFunctio
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open MvPolynomial

namespace GlobalTheory.ExportSeries.Onto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {n : ℕ}

def coefLin (lam : D.what₂.Tau → DomWeight n) : Pol ℂ D.what₂.Tau n →ₗ[ℂ] (GLR D n → ℂ) where
  toFun F := coefFn (RingHom.id ℂ) lam F
  map_add' F G := by
    funext x
    simp only [coefFn, map_add (f := _), mul_add, Pi.add_apply]
  map_smul' c F := by
    funext x
    simp only [coefFn, smul_eq_C_mul, map_mul, eval₂Hom_C, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem coefFn_actP (lam : D.what₂.Tau → DomWeight n) (u : GLR D n) (F : Pol ℂ D.what₂.Tau n) (x : GLR D n) :
    coefFn (RingHom.id ℂ) lam (actP lam (invTrK u) F) x = coefFn (RingHom.id ℂ) lam F (u⁻¹ * x) := by
  have e1 : actP lam (invTrK u) F = detTwK lam (invTrK u) • trAct (invTrK u) F := rfl
  have e2 : (eval₂Hom (RingHom.id ℂ) (fun v : D.what₂.Tau × Fin n × Fin n => (x v.1).val v.2.1 v.2.2)).comp
        (trAct (invTrK u) : Pol ℂ D.what₂.Tau n →+* Pol ℂ D.what₂.Tau n) =
      eval₂Hom (RingHom.id ℂ) (fun v => ((u⁻¹ * x) v.1).val v.2.1 v.2.2) := by
    refine MvPolynomial.ringHom_ext (fun a => by simp [trAct, Formalism.GradedWeylDivisibility.blockAct]) fun v => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [RingHom.comp_apply, RingHom.coe_coe, trAct, Formalism.GradedWeylDivisibility.blockAct, aeval_X, map_sum, map_mul, eval₂Hom_C,
      eval₂Hom_X', Pi.mul_apply, Pi.inv_apply, Units.val_mul, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => rfl
  have e3 : (RingHom.id ℂ) (detTwK lam (invTrK u)) =
      ((detFam (fun τ => (lam τ).detShift) u⁻¹ : ℂˣ) : ℂ) := by
    simp only [detTwK, detPow, detFam, map_prod, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val,
      map_zpow₀, GeneralLinearGroup.val_det_apply]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    change (((u τ)⁻¹).valᵀ).det = _
    rw [det_transpose]
    rfl
  rw [coefFn, coefFn, e1, smul_eq_C_mul, map_mul, eval₂Hom_C, e3, ← e2, map_mul, Units.val_mul]
  simp only [RingHom.comp_apply, RingHom.coe_coe]
  ring

theorem invTrK_invTrK (g : GLR D n) : invTrK (invTrK g) = g := by
  funext τ
  exact Units.ext rfl

theorem map_harm_eq (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n) (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m) :
    (harm m w B).map (harmFn m w B) =
      Submodule.span ℂ {φ | ∃ F : VV ℂ w.lam, φ = coefFn (RingHom.id ℂ) w.lam (F : Pol ℂ D.what₂.Tau n)} := by
  obtain ⟨s, hs⟩ := _root_.GlobalTheory.ExportSeries.DeltaExtremal.harmFn_delta D m n w B hw hm
  have hs0 : ((s : ℤ) : ℂ) ≠ 0 := by exact_mod_cast s.ne_zero
  have h1 : {φ | ∃ F : VV ℂ w.lam, φ = coefFn (RingHom.id ℂ) w.lam (F : Pol ℂ D.what₂.Tau n)} =
      ((VV ℂ w.lam).map (coefLin w.lam) : Set (GLR D n → ℂ)) := by
    ext φ
    constructor
    · rintro ⟨F, rfl⟩
      exact ⟨F, F.2, rfl⟩
    · rintro ⟨F, hF, rfl⟩
      exact ⟨⟨F, hF⟩, rfl⟩
  have key : ∀ u : GLR D n, harmFn m w B (fockGL m w B u (w.delta m)) =
      ((s : ℤ) : ℂ) • coefLin w.lam (actP w.lam (invTrK (u * B)) (ten fun τ => extremal ℂ n (w.lam τ))) := fun u => by
    funext x
    rw [harmFn_fockGL, hs, Pi.smul_apply, smul_eq_mul]
    congr 1
    change _ = coefFn _ _ _ _
    rw [coefFn_actP, _root_.mul_inv_rev, mul_assoc]
  rw [h1, Submodule.span_eq, GlobalTheory.OrbitSpan.VV_eq_span_orbit, harm, Submodule.map_span, Submodule.map_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    rw [key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    have h2 := key (invTrK g * B⁻¹)
    rw [inv_mul_cancel_right, invTrK_invTrK] at h2
    refine (Submodule.smul_mem_iff _ hs0).1 ?_
    beta_reduce
    rw [← h2]
    exact Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩

end GlobalTheory.ExportSeries.Onto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixReductionEqOfHalfIdempotentSubset
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open scoped TensorProduct

namespace GlobalTheory.RedHalfDrop

variable {D : D7}

theorem toEAf_cA_sig (a : AE D) :
    toEAf D (cA D a) = Formalism.UG.sigR D.sp.cm.sig (Af D.host.F) (toEAf D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add a b ha hb => simp only [RingHom.map_add (f := _), ha, hb]
  | tmul y e => rfl

theorem int_idemAt {P : Finset (Pl D.host.E)} (h : SplitSet P) {PP : Pl D.host.E} (hPP : PP ∈ P) :
    toEAf D (idemAt PP) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨hu, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ PP (h.isIdemAt hPP)
  exact hu

theorem int_cA_idemAt {P : Finset (Pl D.host.E)} (h : SplitSet P) {PP : Pl D.host.E} (hPP : PP ∈ P) :
    toEAf D (cA D (idemAt PP)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [toEAf_cA_sig]
  exact GlobalTheory.ResConjPlace.conj_mem_int _ (int_idemAt h hPP)

theorem resS_eq_zero_of_mul {e a : AE D} {PP : Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e PP)
    (ha : toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (h0 : e * a = 0) :
    resS D.host.F PP ⟨toEAf D a, ha⟩ = 0 := by
  obtain ⟨hu, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e PP he
  have hm : (⟨toEAf D e, hu⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) *
      ⟨toEAf D a, ha⟩ = 0 :=
    Subtype.ext (by show toEAf D e * toEAf D a = 0; rw [← map_mul, h0, map_zero])
  have h2 := congrArg (resS D.host.F PP) hm
  rwa [map_mul, h1, one_mul, map_zero] at h2

theorem subring_hom_dite_sub_mul_eq_of_kernel {R k : Type} [CommRing R] [CommRing k] (O : Subring R) (f : O →+* k) (x c : R) (hx : x ∈ O)
    (hc : c ∈ O) (h0 : f ⟨c, hc⟩ = 0) [Decidable (x - c * x ∈ O)] [Decidable (x ∈ O)] :
    (if h : x - c * x ∈ O then f ⟨x - c * x, h⟩ else 0) = if h : x ∈ O then f ⟨x, h⟩ else 0 := by
  have hm : x - c * x ∈ O := sub_mem hx (mul_mem hc hx)
  rw [dite_eq_left hm, dite_eq_left hx]
  have e : (⟨x - c * x, hm⟩ : O) = ⟨x, hx⟩ - ⟨c, hc⟩ * ⟨x, hx⟩ := rfl
  rw [e, map_sub, map_mul, h0, zero_mul, sub_zero]

theorem redM_sub_smul (PP : Pl D.host.E) {b a : ℕ} {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) {c : EAf D}
    (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (h0 : resS D.host.F PP ⟨c, hc⟩ = 0) :
    redM PP (N - c • N) = redM PP N := by
  ext i j
  unfold redM
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact subring_hom_dite_sub_mul_eq_of_kernel _ (resS D.host.F PP) _ _ (hN i j) hc h0

theorem frMapO_smul_eq {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (x : WO S T) : frMapO S T βS βT (e • x) = toEAf D e • frMapO S T βS βT x := by
  unfold frMapO
  have : (e • x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D e • x.map (toEAf D) :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem frMapAdj_smul_eq {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (x : WO S T) : frMapAdj S T βS βT (e • x) = toEAf D (cA D e) • frMapAdj S T βS βT x := by
  unfold frMapAdj
  have h1 : ((e • x : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D) =
      cA D e • (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D) :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]
  have h2 : ∀ M : Matrix (Fin S.rank) (Fin T.rank) (AE D),
      (cA D e • M).map (toEAf D) = toEAf D (cA D e) • M.map (toEAf D) :=
    fun M => Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]
  rw [h1, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, h2, Matrix.mul_smul, Matrix.smul_mul]

theorem redM_drop : ∀ {D : D7} {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) {Pg Qa Qb : Finset (Pl D.host.E)}, PlacesOK Pg Qa → Qb ⊆ Qa → ∀ {x : WO S T}, IsHalf (halfIdem Pg Qa) x → IsIntM (frMapAdj S T βS βT x) → IsIntM (frMapO S T βS βT x) → (∀ PP ∈ Pg, redM PP (frMapAdj S T βS βT x) = redM PP (frMapAdj S T βS βT (halfIdem Pg Qb • x))) ∧ (∀ PP ∈ Qb, redM PP (frMapO S T βS βT x) = redM PP (frMapO S T βS βT (halfIdem Pg Qb • x))) := by
  intro D S T βS βT Pg Qa Qb hP hQ x hx h1 h2
  obtain ⟨P, hPg, hQa, hS⟩ := hP.split
  have hab : halfIdem Pg Qa = halfIdem Pg Qb + idem (Qa \ Qb) := by
    unfold halfIdem idem
    rw [← Finset.sum_sdiff hQ]
    ring
  have hxx : (halfIdem Pg Qb + idem (Qa \ Qb)) • x = x := by
    rw [← hab]
    ext i j
    exact hx i j
  have hsub : ∀ P' ∈ Qa \ Qb, P' ∈ P := fun P' hP' => hQa (Finset.sdiff_subset hP')
  constructor
  · intro PP hPP
    have e1 := frMapAdj_smul_eq βS βT (halfIdem Pg Qb + idem (Qa \ Qb)) x
    rw [hxx, map_add (f := _), map_add (f := _), add_smul] at e1
    have e2 : frMapAdj S T βS βT (halfIdem Pg Qb • x) =
        frMapAdj S T βS βT x - toEAf D (cA D (idem (Qa \ Qb))) • frMapAdj S T βS βT x := by
      rw [frMapAdj_smul_eq]
      exact eq_sub_of_add_eq e1.symm
    have hint : toEAf D (cA D (idem (Qa \ Qb))) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      unfold idem
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum]
      exact sum_mem fun P' hP' => int_cA_idemAt hS (hsub P' hP')
    have hz : resS D.host.F PP ⟨_, hint⟩ = 0 := resS_eq_zero_of_mul (hS.isIdemAt (hPg hPP)) hint (by
      unfold idem
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.mul_sum]
      exact Finset.sum_eq_zero fun P' hP' => hS.mul_conj (hPg hPP) (hsub P' hP'))
    rw [e2, redM_sub_smul PP h1 hint hz]
  · intro PP hPP
    have e1 := frMapO_smul_eq βS βT (halfIdem Pg Qb + idem (Qa \ Qb)) x
    rw [hxx, map_add (f := _), add_smul] at e1
    have e2 : frMapO S T βS βT (halfIdem Pg Qb • x) =
        frMapO S T βS βT x - toEAf D (idem (Qa \ Qb)) • frMapO S T βS βT x := by
      rw [frMapO_smul_eq]
      exact eq_sub_of_add_eq e1.symm
    have hint : toEAf D (idem (Qa \ Qb)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      unfold idem
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact sum_mem fun P' hP' => int_idemAt hS (hsub P' hP')
    have hz : resS D.host.F PP ⟨_, hint⟩ = 0 := resS_eq_zero_of_mul (hS.isIdemAt (hQa (hQ hPP))) hint (by
      unfold idem
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun P' hP' => hS.mul_eq_zero (hQa (hQ hPP)) (hsub P' hP')
        fun e => (Finset.mem_sdiff.1 hP').2 (e ▸ hPP))
    rw [e2, redM_sub_smul PP h2 hint hz]

end GlobalTheory.RedHalfDrop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedPrimeToDenomGLAndInvOfEqOneOffFinite
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.StdAtPrime

namespace GlobalTheory.StdAtPrime

theorem natCast_adicCompletion_v_le_one {E : Type} [Field E] [NumberField E]
    (Q : HeightOneSpectrum (𝓞 E)) (k : ℕ) : Valued.v ((k : Q.adicCompletion E)) ≤ 1 := by
  have h := HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := E) (v := Q) (k : 𝓞 E)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
  simpa using h

theorem exists_coprime_natCast_mul_v_le_one {E : Type} [Field E] [NumberField E]
    (p : ℕ) (hp : p.Prime) (Q : HeightOneSpectrum (𝓞 E)) (hpQ : (p : 𝓞 E) ∉ Q.asIdeal)
    (x : Q.adicCompletion E) :
    ∃ r : ℕ, r.Coprime p ∧ Valued.v ((r : Q.adicCompletion E) * x) ≤ 1 := by
  obtain ⟨b, hb, hbx⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers Q x
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hbx
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set N := Ideal.absNorm (Ideal.span {b}) with hNdef
  have hN0 : N ≠ 0 := by
    rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb0
  have hmem : (N : 𝓞 E) ∈ Ideal.span {b} := Ideal.absNorm_mem _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨N / p ^ N.factorization p, (Nat.coprime_ordCompl hp hN0).symm, ?_⟩
  have hsplit := Nat.ordProj_mul_ordCompl_eq_self N p
  have hvp : Valued.v ((p : Q.adicCompletion E)) = 1 := by
    have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := E) (v := Q) (p : 𝓞 E)
    have h2 : Q.valuation E (algebraMap (𝓞 E) E (p : 𝓞 E)) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem Q).mpr hpQ
    simp only [map_natCast] at h1 h2
    rw [h1, h2]
  have hNx : Valued.v ((N : Q.adicCompletion E) * x) ≤ 1 := by
    have e : ((N : Q.adicCompletion E)) = (algebraMap (𝓞 E) (Q.adicCompletion E) c) *
        (algebraMap (𝓞 E) (Q.adicCompletion E) b) := by
      rw [← map_mul, hc, map_natCast]
    rw [e, mul_assoc, Valuation.map_mul, mul_comm _ x]
    refine mul_le_one' ?_ hbx
    have h := HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := E) (v := Q) c
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at h
  rw [← hsplit] at hNx
  push_cast at hNx
  rw [mul_assoc, Valuation.map_mul, map_pow, hvp, one_pow, one_mul] at hNx
  exact_mod_cast hNx

end GlobalTheory.StdAtPrime

namespace GlobalTheory.StdAtPrime

theorem bnd_of_local {E : Type} [Field E] [NumberField E] (p : ℕ) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) (S : Set (HeightOneSpectrum (𝓞 E)))
    (hS : S.Finite)
    (hin : ∀ Q ∈ S, ∀ i j, ∃ r : ℕ, r.Coprime p ∧ Valued.v ((r : Q.adicCompletion E) * (A i j) Q) ≤ 1)
    (hout : ∀ Q ∉ S, ∀ i j, Valued.v ((A i j) Q) ≤ 1) : Bnd p A := by
  classical
  let f : HeightOneSpectrum (𝓞 E) × Fin n × Fin n → ℕ := fun t =>
    if h : t.1 ∈ S then Classical.choose (hin t.1 h t.2.1 t.2.2) else 1
  have hf : ∀ t, (f t).Coprime p := by
    intro t
    by_cases h : t.1 ∈ S
    · simp only [f, dif_pos h]; exact (Classical.choose_spec (hin t.1 h t.2.1 t.2.2)).1
    · simp only [f, dif_neg h]; exact Nat.coprime_one_left p
  let T : Finset (HeightOneSpectrum (𝓞 E) × Fin n × Fin n) := hS.toFinset ×ˢ Finset.univ
  refine ⟨∏ t ∈ T, f t, Nat.Coprime.prod_left fun t _ => hf t, fun i j Q => ?_⟩
  let ev : FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E := RestrictedProduct.evalRingHom _ Q
  have hev : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = ev x := fun _ => rfl
  rw [hev, map_mul, map_natCast, ← hev]
  by_cases hQ : Q ∈ S
  · have hmem : (Q, i, j) ∈ T := by simp [T, hQ]
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem f hmem
    rw [hk, Nat.cast_mul, mul_comm ((f (Q, i, j) : ℕ) : Q.adicCompletion E), mul_assoc,
      Valuation.map_mul]
    refine mul_le_one' (natCast_adicCompletion_v_le_one Q k) ?_
    have := (Classical.choose_spec (hin Q hQ i j)).2
    simpa only [f, dif_pos hQ] using this
  · rw [Valuation.map_mul]
    exact mul_le_one' (natCast_adicCompletion_v_le_one Q _) (hout Q hQ i j)

theorem one_entry_v_le_one {E : Type} [Field E] [NumberField E] (n : ℕ)
    (Q : HeightOneSpectrum (𝓞 E)) (i j : Fin n) :
    Valued.v (((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q) ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs
  · have := natCast_adicCompletion_v_le_one Q 1
    simpa using this
  · let ev : FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E := RestrictedProduct.evalRingHom _ Q
    change Valued.v (ev 0) ≤ 1
    rw [map_zero, map_zero]
    exact zero_le_one

theorem inv_eq_one_off {E : Type} [Field E] [NumberField E] (n : ℕ)
    (G : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (Q : HeightOneSpectrum (𝓞 E))
    (hQ : ∀ i j, (G.1 i j) Q = ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q) :
    ∀ i j, ((G⁻¹).1 i j) Q = ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q := by
  let ev : FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E := RestrictedProduct.evalRingHom _ Q
  have hev : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = ev x := fun _ => rfl
  have hone : ∀ i j, ev ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) =
      (1 : Matrix (Fin n) (Fin n) (Q.adicCompletion E)) i j := by
    intro i j; rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  have h1 : ev.mapMatrix G.1 = 1 := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, ← hev, hQ, hev, hone]
  have h2 : ev.mapMatrix G.1 * ev.mapMatrix (G⁻¹).1 = 1 := by
    rw [← map_mul]
    have : G.1 * (G⁻¹).1 = 1 := by
      have := congrArg Units.val (mul_inv_cancel G)
      simpa using this
    rw [this, map_one]
  rw [h1, one_mul] at h2
  intro i j
  rw [hev, hev, hone]
  have := congrFun (congrFun h2 i) j
  rwa [RingHom.mapMatrix_apply, Matrix.map_apply] at this

theorem bnd_and_bnd_inv_of_eq_one_off_finite : ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (G : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (S : Set (HeightOneSpectrum (𝓞 E))), S.Finite → (∀ Q ∈ S, (p : 𝓞 E) ∉ Q.asIdeal) → (∀ Q ∉ S, ∀ i j, (G.1 i j) Q = ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q) → Bnd p G.1 ∧ Bnd p (G⁻¹).1 := by
  intro E _ _ p hp n G S hS hpS hG
  have hGi := fun Q hQ => inv_eq_one_off n G Q (hG Q hQ)
  have key : ∀ A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E),
      (∀ Q ∉ S, ∀ i j, (A i j) Q = ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q) →
      Bnd p A := by
    intro A hA
    refine bnd_of_local p n A S hS (fun Q hQ i j => ?_) (fun Q hQ i j => ?_)
    · exact exists_coprime_natCast_mul_v_le_one p hp Q (hpS Q hQ) _
    · rw [hA Q hQ i j]; exact one_entry_v_le_one n Q i j
  exact ⟨key G.1 hG, key (G⁻¹).1 hGi⟩

end GlobalTheory.StdAtPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeStableUnderAction
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.LatKeep

variable {D : D7}

theorem intGL_mulVec_int {n : ℕ} (y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) (v : Fin n → EAf D)
    (hv : ∀ i, v i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (i : Fin n) :
    (((Formalism.L2.DIV.intGL D.host.F D.host.E n y : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ v) i ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
  simp only [Matrix.mulVec, dotProduct]
  refine sum_mem fun j _ => mul_mem ?_ (hv j)
  exact (y.val i j).2

theorem isFrame_mul_intGL {n : ℕ} {β : GL (Fin n) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) (y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) :
    Formalism.L2.DIV.IsFrame (β * Formalism.L2.DIV.intGL D.host.F D.host.E n y) Λ := by
  intro x
  rw [hβ x]
  have e1 : (((β * Formalism.L2.DIV.intGL D.host.F D.host.E n y)⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x
      = ((Formalism.L2.DIV.intGL D.host.F D.host.E n y⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ
          (((β⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x) := by
    have hm : (β * Formalism.L2.DIV.intGL D.host.F D.host.E n y)⁻¹ = Formalism.L2.DIV.intGL D.host.F D.host.E n y⁻¹ * β⁻¹ := by
      rw [_root_.mul_inv_rev, MonoidHom.map_inv]
    rw [hm, Units.val_mul, Matrix.mulVec_mulVec]
  have e2 : ((β⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x
      = ((Formalism.L2.DIV.intGL D.host.F D.host.E n y : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ
          ((((β * Formalism.L2.DIV.intGL D.host.F D.host.E n y)⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x) := by
    rw [e1, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]
  constructor
  · intro h i
    rw [e1]
    exact intGL_mulVec_int _ _ h i
  · intro h i
    rw [e2]
    exact intGL_mulVec_int _ _ h i

end GlobalTheory.LatKeep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallRingEquivFixed
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.FixedAlgebraic

theorem mem_of_forall_ringEquiv_fixed :
    ∀ (K : Subfield ℂ) (x : ℂ), IsAlgebraic ℚ x →
      (∀ τ : ℂ ≃+* ℂ, (∀ y ∈ K, τ y = y) → τ x = x) → x ∈ K := by
  intro K x _ hx
  obtain ⟨y, hy⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := K) x
    fun σ => hx σ.toRingEquiv fun y hy => σ.commutes ⟨y, hy⟩
  rw [← hy]
  exact y.2

end GlobalTheory.FixedAlgebraic
end

