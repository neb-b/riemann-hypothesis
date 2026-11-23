module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0388
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0363
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionZeroOneProperties
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevInductionGrowBoundOfPresentation
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmDecompIffDecomp
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.DecompForms

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π ↔ ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := by
  intro D i r ρ π
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, fun g u => he g u⟩
  · rintro ⟨e, he⟩
    exact ⟨e, fun g u => he g u⟩

end GlobalTheory.DecompForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmIntOfSupLaws
section
noncomputable section

namespace GlobalTheory.IntSup

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
open scoped TensorProduct

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X)

theorem mall_map_le (i : X.Tw) (j : ℕ) (b : Bool) (φ : Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    (hφ : ∀ f ∈ Y.Bsup i j b, φ f ∈ Y.Bsup i j b)
    (hc : ∀ g, (Y.actG i j b g).toLinearMap ∘ₗ φ = φ ∘ₗ (Y.actG i j b g).toLinearMap) :
    (IntegralHeckeForms.Mall Y i j b).map (φ.restrictScalars (X.O i)) ≤ IntegralHeckeForms.Mall Y i j b := by
  rintro _ ⟨f, ⟨hf, hf0⟩, rfl⟩
  refine ⟨hφ f hf, ?_⟩
  change φ f ∈ IntegralHeckeForms.Fm0 Y i j b
  replace hf0 : f ∈ IntegralHeckeForms.Fm0 Y i j b := hf0
  simp only [IntegralHeckeForms.Fm0, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at hf0 ⊢
  intro u
  have h := LinearMap.congr_fun (hc u) f
  simp only [LinearMap.comp_apply] at h
  rw [h, hf0 u, map_smul]

theorem admInt_of_sup : ∀ (D : D7) (E : IntegralHeckeForms.XD D), SupG D → SupFull D → SupHk D → UnivSup D E → TypeKept E → CommG D →
    IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E := by
  intro D E hG hF hH hU hT hC i hi j hj b
  obtain ⟨hfg, hsp⟩ := hF i hi j hj b
  refine ⟨fun g => ?_, ?_,
    GlobalTheory.IntRestBall.span_inf_of_span_top _ hsp _ _ (fun _ => Iff.rfl),
    fun k P hk => mall_map_le D.nexp i j b _ (hH i hi j hj b k P hk) (fun g => hC i hi b j hj g k P hk),
    ?_, hT i hi j hj b⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact hG i hi j hj b g f hf
  · exact hfg.of_le (fun f hf => hf.1)
  · intro a ha
    obtain ⟨c, hc⟩ := hU i hi j hj b a ha
    refine ⟨c, fun Q M h1 h2 h3 h4 => ?_⟩
    obtain ⟨Xi, hXi, hδ⟩ := hc Q M h1 h2 h3 h4
    rw [hXi, Finsupp.sum, Finset.smul_sum]
    refine Submodule.sum_mem _ fun δ _ => ?_
    have hm : ((D.ntw.l i : D.ntw.O i) ^ c) • Xi δ ∈ IntegralHeckeForms.Mall D.nexp i j b :=
      ⟨(hδ δ).2, ((IntegralHeckeForms.Fm0 D.nexp i j b).restrictScalars (D.ntw.O i)).smul_mem _ (hδ δ).1⟩
    exact ⟨(⟨_, hm⟩ : IntegralHeckeForms.Mall D.nexp i j b) ⊗ₜ AddMonoidAlgebra.single δ (1 : D.ntw.O i), by
      simp [TensorProduct.smul_tmul']⟩

end GlobalTheory.IntSup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT3OfHeckeSemisimple
section
open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.EigRed

open Formalism.MainNotions.IntegralHeckeForms

theorem admT3_of_semisimple_good : ∀ (D : D7) (E : IntegralHeckeForms.XD D), IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E → IntegralHeckeForms.GroupAlgebraIntegrality D.nexp → D.nexp.sig_all → HkSS D → IntegralHeckeForms.GoodLatticePoints D.nexp := by
  intro D E hI hA hS hss i hi j hj b x hxB hxm ev hev
  by_contra hno
  apply hxm
  have hcomm := ((hA i hi b).2 j hj).1
  have hM := (hI i hi j hj b).2.2.2.1
  have hx := hss i hi j hj b hxB.2
  obtain ⟨f, hf, hfx⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx
  refine mem_smul_of_sum_eigenvectors (ι := {p : ℕ × PlE D.host // HkIdx i p.1 p.2}) _ _
    (fun p => hkO D.nexp i j b p.1.1 p.1.2) (fun p z hz => ?_) (fun p => ev p.1.1 p.1.2) f.support
    (fun a => f a) x (fun a _ => ?_) ?_ hxB (fun p => hev _ _ p.2)
  · exact ⟨hM _ _ p.2 ⟨z, hz.1, rfl⟩, idempotentImage_stable_of_equivariant D.nexp i j b _ (fun g => hcomm g _ _ p.2) z hz.2⟩
  · by_cases h0 : f a = 0
    · exact Or.inl h0
    right
    have hex : eG D.nexp i j b (f a) = f a := by
      obtain ⟨y, -, hy⟩ := (hf a).2
      rw [← hy, eG_idem]
    have heig : ∀ k P, HkIdx i k P → D.nexp.hkF i j b k P (f a) = a k P • f a := by
      intro k P hk
      have h1 := (hf a).1
      simp only [Eigsp, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h1
      exact h1 k P hk
    obtain ⟨s, hs1, hs2, hs3⟩ := hS i j b _ a h0 hex
      (fun k P h1 h2 h3 h4 => heig k P ⟨h1, h2, h3, h4⟩)
    refine ⟨fun p => D.ntw.hEig i s p.1.1 p.1.2, fun p => ?_, ?_⟩
    · change D.nexp.hkF i j b _ _ _ = _
      rw [heig _ _ p.2, ← hs3 _ _ p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2, algebraMap_smul]
    · by_contra hu
      refine hno ⟨s, hs1, hs2, fun k P hk => ?_⟩
      exact fun h => hu ⟨⟨(k, P), hk⟩, h⟩
  · exact hfx.symm

end GlobalTheory.EigRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDeterminant
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

namespace GlobalTheory.Proof.BlockDeterminant

theorem det_eq_of_conj {ι A B : Type} [Fintype ι] [DecidableEq ι] [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Injective φ) (M M' : Matrix ι ι A) (P : Matrix ι ι B)
    (hP : IsUnit P.det) (h : P * M.map φ = M'.map φ * P) : M.det = M'.det := by
  apply hφ
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm _ P.det] at h1
  have h2 := hP.mul_left_cancel h1
  rw [RingHom.map_det, RingHom.map_det]
  exact h2

theorem conj_sum {ι κ A B : Type} [Fintype ι] [Fintype κ] [CommRing A] [CommRing B]
    (φ : A →+* B) (c : κ → A) (M M' : κ → Matrix ι ι A) (P : Matrix ι ι B)
    (h : ∀ k, P * (M k).map φ = (M' k).map φ * P) :
    P * (∑ k, c k • M k).map φ = (∑ k, c k • M' k).map φ * P := by
  have e : ∀ M : κ → Matrix ι ι A, (∑ k, c k • M k).map φ = ∑ k, φ (c k) • (M k).map φ := by
    intro M
    ext a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.sum_apply, map_sum]
  rw [e, e, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, h]

theorem det_generic_eq {ι κ A B : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Injective φ) (M M' : κ → Matrix ι ι A) (P : Matrix ι ι B)
    (hP : IsUnit P.det) (h : ∀ k, P * (M k).map φ = (M' k).map φ * P) :
    (∑ k, (MvPolynomial.X k : MvPolynomial κ A) • (M k).map (MvPolynomial.C : A →+* MvPolynomial κ A)).det =
      (∑ k, (MvPolynomial.X k : MvPolynomial κ A) • (M' k).map (MvPolynomial.C : A →+* MvPolynomial κ A)).det := by
  refine det_eq_of_conj (MvPolynomial.map φ) (MvPolynomial.map_injective φ hφ) _ _
    (P.map (MvPolynomial.C : B →+* MvPolynomial κ B)) ?_ ?_
  · have := hP.map (MvPolynomial.C : B →+* MvPolynomial κ B)
    rwa [RingHom.map_det] at this
  · refine conj_sum _ _ _ _ _ fun k => ?_
    have e : ∀ Q : Matrix ι ι A, (Q.map (MvPolynomial.C : A →+* MvPolynomial κ A)).map (MvPolynomial.map φ) =
        (Q.map φ).map (MvPolynomial.C : B →+* MvPolynomial κ B) := by
      intro Q
      ext1 a b
      simp
    rw [e, e, ← Matrix.map_mul, ← Matrix.map_mul, h]

theorem det_block_eq {ι κ A B : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Injective φ) (M M' : κ → κ → Matrix ι ι A) (P : Matrix ι ι B)
    (hP : IsUnit P.det) (h : ∀ k l, P * (M k l).map φ = (M' k l).map φ * P) :
    (Matrix.of fun (pa qb : κ × ι) => M pa.1 qb.1 pa.2 qb.2).det =
      (Matrix.of fun (pa qb : κ × ι) => M' pa.1 qb.1 pa.2 qb.2).det := by
  refine det_eq_of_conj φ hφ _ _ (Matrix.kroneckerMap (· * ·) (1 : Matrix κ κ B) P) ?_ ?_
  · rw [Matrix.det_kronecker]
    simpa using hP.pow _
  · ext ⟨k, a⟩ ⟨l, b⟩
    have := congrFun (congrFun (h k l) a) b
    simp only [Matrix.mul_apply, Matrix.map_apply] at this
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, Finset.sum_ite_eq, this]

theorem main : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r r' : (N.X i → (GE N →* GL (Fin R.nV) (N.O i)))) (Pm : N.X i → GL (Fin R.nV) (KK N i)), (∀ x g, (Pm x : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (rO N i r x g).map (toK N i) = (rO N i r' x g).map (toK N i) * (Pm x : Matrix (Fin R.nV) (Fin R.nV) (KK N i))) → ∀ (X' : Type) (p : X' → N.X i) (T' : Subalgebra (N.O i) (X' → N.O i)), (∀ a, InSpan N i T' (fun y => rO N i r (p y)) a → ∃ a', InSpan N i T' (fun y => rO N i r' (p y)) a' ∧ ∀ y, (Pm (p y) : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (a y).map (toK N i) = (a' y).map (toK N i) * (Pm (p y) : Matrix (Fin R.nV) (Fin R.nV) (KK N i))) ∧ (CharpolyCoeffsInSubalgebra N i T' (fun y => rO N i r (p y)) → CharpolyCoeffsInSubalgebra N i T' (fun y => rO N i r' (p y))) := by
  intro R H what₂ N i r r' Pm hPm X' p T'
  have key : ∀ (m : ℕ) (f : Fin m → X' → N.O i) (g : Fin m → GE N) (y : X'),
      (Pm (p y) : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) *
        ((∑ k, fun x' => f k x' • rO N i r (p x') (g k)) y).map (toK N i) =
      ((∑ k, fun x' => f k x' • rO N i r' (p x') (g k)) y).map (toK N i) *
        (Pm (p y) : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) := by
    intro m f g y
    rw [Finset.sum_apply, Finset.sum_apply]
    exact conj_sum _ _ _ _ _ fun k => hPm _ _
  have back : ∀ a', InSpan N i T' (fun y => rO N i r' (p y)) a' →
      ∃ a, InSpan N i T' (fun y => rO N i r (p y)) a ∧ ∀ y,
        (Pm (p y) : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (a y).map (toK N i) =
          (a' y).map (toK N i) * (Pm (p y) : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) := by
    rintro a' ⟨m, f, g, hf, rfl⟩
    exact ⟨_, ⟨m, f, g, hf, rfl⟩, key m f g⟩
  have hinj : Function.Injective (toK N i) := IsFractionRing.injective _ _
  have hU : ∀ x, IsUnit (Pm x : Matrix (Fin R.nV) (Fin R.nV) (KK N i)).det := fun x =>
    (Matrix.isUnit_iff_isUnit_det _).1 (Pm x).isUnit
  refine ⟨?_, ?_⟩
  · rintro a ⟨m, f, g, hf, rfl⟩
    exact ⟨_, ⟨m, f, g, hf, rfl⟩, key m f g⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun m a' ha' d => ?_, fun g Θ' hΘ' => ?_⟩
    · choose a ha hc using fun k => back (a' k) (ha' k)
      have := h1 m a ha d
      convert this using 2 with y
      rw [det_generic_eq (toK N i) hinj (fun k => a k y) (fun k => a' k y) _ (hU (p y))
        (fun k => hc k y)]
    · choose Θ hΘ hc using fun k l => back (Θ' k l) (hΘ' k l)
      have := h2 g Θ hΘ
      convert this using 2 with y
      exact (det_block_eq (toK N i) hinj (fun k l => Θ k l y) (fun k l => Θ' k l y) _ (hU (p y))
        (fun k l => hc k l y)).symm

end GlobalTheory.Proof.BlockDeterminant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaNextCoeffThetaMemStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_beta_next_coeff_theta_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (g : ↥(GK K)) (w : Ainf l), Per.σA (g : GQ l) (bk.ev bk.E) = bk.ev bk.E * w → ∀ (m k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β → ∀ (i n : ℕ), i + 1 ≤ m → ∀ γ : Matrix (Fin d) (Fin d) bk.S, (∀ p q, bk.E ^ i ∣ (β - (l : bk.S) ^ n • γ) p q) → ∃ δ : Matrix (Fin d) (Fin d) bk.S, (∀ p q, bk.E ^ (i + 1) ∣ (β - (l : bk.S) ^ n • γ - bk.E ^ i • δ) p q) ∧ ∀ p q, ∃ y : OC l, Per.θ l (bk.ev (δ p q)) * (Per.θ l w ^ i - 1) = (l : OC l) ^ n * y := by
  first | (exact @GlobalTheory.BKLim.beta_step) | (exact GlobalTheory.BKLim.beta_step) | (intros; apply GlobalTheory.BKLim.beta_step  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinClosedDiscNormMulMultiplicative
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.GaussMul

open Filter

theorem norm_sum_lt_of_ultra {E ι : Type} [SeminormedAddCommGroup E] [IsUltrametricDist E] (s : Finset ι)
    (f : ι → E) {C : ℝ} (hC : 0 < C) (h : ∀ i ∈ s, ‖f i‖ < C) : ‖∑ i ∈ s, f i‖ < C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hC
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem exists_eq_sup {f : ℕ → ℝ} {M : ℝ} (hM : 0 < M) (hle : ∀ n, f n ≤ M)
    (hsup : ∀ r : ℝ, 0 ≤ r → (∀ n, f n ≤ r) → M ≤ r) (ht : Tendsto f atTop (nhds 0)) : ∃ n, f n = M := by
  by_contra hne
  push_neg at hne
  have hlt : ∀ n, f n < M := fun n => lt_of_le_of_ne (hle n) (hne n)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds (half_pos hM)))
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image (Finset.range (N + 1)) f ⟨0, by simp⟩
  have h1 : M ≤ max (M / 2) (f k) := hsup _ ((half_pos hM).le.trans (le_max_left _ _)) fun n => by
    by_cases hn : n < N + 1
    · exact (hk n (Finset.mem_range.2 hn)).trans (le_max_right _ _)
    · exact (hN n (by omega)).le.trans (le_max_left _ _)
  exact absurd h1 (not_le.2 (max_lt (half_lt_self hM) (hlt k)))

theorem gauss {D : Type} [NormedRing D] [IsUltrametricDist D] (hm : ∀ x y : D, ‖x * y‖ = ‖x‖ * ‖y‖) {ρ : ℝ}
    (hρ : 0 < ρ) (p q : ℕ → D) {P Q : ℝ} (hP : 0 < P) (hQ : 0 < Q) (hp : ∀ n, ‖p n‖ * ρ ^ n ≤ P)
    (hq : ∀ n, ‖q n‖ * ρ ^ n ≤ Q) (hp0 : ∃ n, ‖p n‖ * ρ ^ n = P) (hq0 : ∃ n, ‖q n‖ * ρ ^ n = Q) :
    ∃ N, ‖∑ x ∈ Finset.HasAntidiagonal.antidiagonal N, p x.1 * q x.2‖ * ρ ^ N = P * Q := by
  classical
  set n₀ := Nat.find hp0
  set m₀ := Nat.find hq0
  have hn₀ : ‖p n₀‖ * ρ ^ n₀ = P := Nat.find_spec hp0
  have hm₀ : ‖q m₀‖ * ρ ^ m₀ = Q := Nat.find_spec hq0
  refine ⟨n₀ + m₀, ?_⟩
  have hρN : 0 < ρ ^ (n₀ + m₀) := pow_pos hρ _
  have hmem : (n₀, m₀) ∈ Finset.HasAntidiagonal.antidiagonal (n₀ + m₀) := by simp
  rw [← Finset.add_sum_erase _ _ hmem]
  have hdom : ‖p n₀ * q m₀‖ * ρ ^ (n₀ + m₀) = P * Q := by
    rw [hm, pow_add, ← hn₀, ← hm₀]; ring
  have hrest : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (n₀ + m₀)).erase (n₀, m₀), p x.1 * q x.2‖ < P * Q / ρ ^ (n₀ + m₀) := by
    refine norm_sum_lt_of_ultra _ _ (div_pos (mul_pos hP hQ) hρN) fun x hx => ?_
    rw [lt_div_iff₀ hρN]
    obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have e : ‖p x.1 * q x.2‖ * ρ ^ (n₀ + m₀) = (‖p x.1‖ * ρ ^ x.1) * (‖q x.2‖ * ρ ^ x.2) := by
      rw [hm, ← hx, pow_add]; ring
    rw [e]
    have h1 : 0 ≤ ‖p x.1‖ * ρ ^ x.1 := by positivity
    have h2 : 0 ≤ ‖q x.2‖ * ρ ^ x.2 := by positivity
    by_cases h : x.1 < n₀
    · have hlt : ‖p x.1‖ * ρ ^ x.1 < P := lt_of_le_of_ne (hp _) (Nat.find_min hp0 h)
      calc (‖p x.1‖ * ρ ^ x.1) * (‖q x.2‖ * ρ ^ x.2) ≤ (‖p x.1‖ * ρ ^ x.1) * Q :=
            mul_le_mul_of_nonneg_left (hq _) h1
        _ < P * Q := mul_lt_mul_of_pos_right hlt hQ
    · have h' : x.2 < m₀ := by
        by_contra h''
        apply hne
        ext <;> simp <;> omega
      have hlt : ‖q x.2‖ * ρ ^ x.2 < Q := lt_of_le_of_ne (hq _) (Nat.find_min hq0 h')
      calc (‖p x.1‖ * ρ ^ x.1) * (‖q x.2‖ * ρ ^ x.2) ≤ P * (‖q x.2‖ * ρ ^ x.2) :=
            mul_le_mul_of_nonneg_right (hp _) h2
        _ < P * Q := mul_lt_mul_of_pos_left hlt hP
  have hdom' : ‖p n₀ * q m₀‖ = P * Q / ρ ^ (n₀ + m₀) := by
    rw [eq_div_iff hρN.ne', hdom]
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hdom']; exact hrest.ne'), hdom',
    max_eq_left hrest.le, div_mul_cancel₀ _ hρN.ne']

end GlobalTheory.BSP.GaussMul

namespace GlobalTheory.BSP.GaussMul

theorem norm_mul_disc (l : ℕ) [hl : Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (x y : bk.DS ρ) : ‖x * y‖ = ‖x‖ * ‖y‖ := by
  obtain ⟨a, ha1, ha2, ha3, ha4⟩ := _root_.GlobalTheory.BSP.DiscSer.exists_coeff_disc l K bk ρ hρ0 hρ1
  haveI : IsUltrametricDist (Disc l (0 : Wq l bk.a) 1) := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l (Wq l bk.a) 0 1).1
  have hm0 := (_root_.GlobalTheory.BSP.disc_zero_one l K bk).1
  have hρ : (0 : ℝ) < ρ := NNReal.coe_pos.2 hρ0

  have step1 : ∀ s t : bk.S, ‖toDisc l (X : bk.S) ρ s * toDisc l (X : bk.S) ρ t‖ =
      ‖toDisc l (X : bk.S) ρ s‖ * ‖toDisc l (X : bk.S) ρ t‖ := by
    intro s t
    rcases eq_or_ne (toDisc l (X : bk.S) ρ s) 0 with hu | hu
    · simp [hu]
    rcases eq_or_ne (toDisc l (X : bk.S) ρ t) 0 with hv | hv
    · simp [hv]
    have hP : 0 < ‖toDisc l (X : bk.S) ρ s‖ := norm_pos_iff.2 hu
    have hQ : 0 < ‖toDisc l (X : bk.S) ρ t‖ := norm_pos_iff.2 hv
    obtain ⟨N, hN⟩ := gauss hm0 hρ (fun n => a n (toDisc l (X : bk.S) ρ s)) (fun n => a n (toDisc l (X : bk.S) ρ t))
      hP hQ (fun n => ha2 n _) (fun n => ha2 n _)
      (exists_eq_sup hP (fun n => ha2 n _) (ha3 _) (ha4 _)) (exists_eq_sup hQ (fun n => ha2 n _) (ha3 _) (ha4 _))
    have hconv : a N (toDisc l (X : bk.S) ρ s * toDisc l (X : bk.S) ρ t) =
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal N, a x.1 (toDisc l (X : bk.S) ρ s) * a x.2 (toDisc l (X : bk.S) ρ t) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_mul, ha1, coeff_mul, map_sum]
      exact Finset.sum_congr rfl fun x _ => by rw [map_mul, ha1, ha1]
    refine le_antisymm (norm_mul_le _ _) ?_
    rw [← hN, ← hconv]
    exact ha2 N _

  have hlm := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l bk.S (X : bk.S) ρ).2.1
  have hl0 : (0 : ℝ) < (l : ℝ) := Nat.cast_pos.2 hl.out.pos
  have hlpow : ∀ (n : ℕ) (z : bk.DS ρ), ‖z * ((l : ℕ) : bk.DS ρ) ^ n‖ = ‖z‖ / (l : ℝ) ^ n := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ, ← mul_assoc, mul_comm _ ((l : ℕ) : bk.DS ρ), hlm, ih, pow_succ, div_div]
  have hpre : ∀ p : PreDisc l (X : bk.S) ρ, ∃ (n : ℕ) (s : bk.S),
      ofPre l (X : bk.S) ρ p * ((l : ℕ) : bk.DS ρ) ^ n = toDisc l (X : bk.S) ρ s := by
    intro p
    obtain ⟨n, s, h⟩ := IsLocalization.Away.surj ((l : ℕ) : bk.S) p
    refine ⟨n, s, ?_⟩
    have h' := congrArg (ofPre l (X : bk.S) ρ) h
    rw [map_mul, map_pow, map_natCast, map_natCast] at h'
    exact h'
  have step2 : ∀ p q : PreDisc l (X : bk.S) ρ, ‖ofPre l (X : bk.S) ρ p * ofPre l (X : bk.S) ρ q‖ =
      ‖ofPre l (X : bk.S) ρ p‖ * ‖ofPre l (X : bk.S) ρ q‖ := by
    intro p q
    obtain ⟨n, s, hs⟩ := hpre p
    obtain ⟨m, t, ht⟩ := hpre q
    have e : ofPre l (X : bk.S) ρ p * ofPre l (X : bk.S) ρ q * ((l : ℕ) : bk.DS ρ) ^ (n + m) =
        toDisc l (X : bk.S) ρ s * toDisc l (X : bk.S) ρ t := by
      rw [← hs, ← ht, pow_add]; ring
    have h1 := hlpow (n + m) (ofPre l (X : bk.S) ρ p * ofPre l (X : bk.S) ρ q)
    rw [e, step1, ← hs, ← ht, hlpow, hlpow, pow_add, div_mul_div_comm] at h1
    exact ((div_left_inj' (by positivity)).1 h1).symm
  exact (denseRange_ofPre l (X : bk.S) ρ).induction_on₂ (p := fun x y : bk.DS ρ => ‖x * y‖ = ‖x‖ * ‖y‖)
    (isClosed_eq (continuous_norm.comp (continuous_fst.mul continuous_snd))
      ((continuous_norm.comp continuous_fst).mul (continuous_norm.comp continuous_snd))) step2 x y

theorem norm_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 →
    ∀ x y : bk.DS ρ, ‖x * y‖ = ‖x‖ * ‖y‖ :=
  fun l _ K bk ρ h0 h1 x y => norm_mul_disc l K bk ρ h0 h1 x y

end GlobalTheory.BSP.GaussMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinClosedDiscRestrictInjectiveStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_closedDisc_restrict_injective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ ρ' : ℝ≥0), 0 < ρ' → ρ' ≤ ρ → ρ < 1 → ∀ R : bk.DS ρ →+* bk.DS ρ', IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id bk.S) R → Function.Injective R := by
  first | exact @GlobalTheory.BSP.disc_restrict_injective | exact GlobalTheory.BSP.disc_restrict_injective | (intros; apply GlobalTheory.BSP.disc_restrict_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFrameIsCrOfLinkedTowerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinFrame_isCr_of_linked_tower : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val) (F₀ : Frame bk N d fun g => (ρ g).val) (r : ℕ), (∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r) → (∀ n, (F n).IsCr) → F₀.IsCr := by
  first | (exact @GlobalTheory.BKLim.CrLimit.isCr_of_link) | (exact GlobalTheory.BKLim.CrLimit.isCr_of_link) | (intros; apply GlobalTheory.BKLim.CrLimit.isCr_of_link  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinIsBetaSubOfLpowSmulStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_isBeta_sub_of_lpow_smul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (m k n : ℕ) (β γ : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β → 1 ≤ m → n ≤ k → (∀ p q, bk.E ^ m ∣ (β - (l : bk.S) ^ n • γ) p q) → F.IsBeta m (k - n) γ := by
  first | (exact @GlobalTheory.BKLim.BetaDiv.isBeta_div) | (exact GlobalTheory.BKLim.BetaDiv.isBeta_div) | (intros; apply GlobalTheory.BKLim.BetaDiv.isBeta_div  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinQuotientEisensteinCompactnessStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_quotient_eisenstein_compactness : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type) [Finite ι] (m : ℕ) (Q : ℕ → (ι → bk.S) → Prop), (∀ n x, Q (n + 1) x → Q n x) → (∀ n x y, Q n x → (∀ i, x i - y i ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m}) → Q n y) → (∀ n, ∃ x, Q n x) → ∃ x, ∀ n, Q n x := by
  first | (exact @GlobalTheory.BKLim.Cpt.compact) | (exact GlobalTheory.BKLim.Cpt.compact) | (intros; apply GlobalTheory.BKLim.Cpt.compact  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevInductionGrowBoundOfPresentationStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chebotarevInductionGrowBound_of_presentation : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), ThmS bkP → ∀ (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → Grow bkP i s := by
  first | exact @GlobalTheory.Growth.grow | exact GlobalTheory.Growth.grow | (intros; apply GlobalTheory.Growth.grow <;> assumption)
end

