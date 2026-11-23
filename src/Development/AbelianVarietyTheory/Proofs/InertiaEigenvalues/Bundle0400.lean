module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0377
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0003
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stdform
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseCondOfSplitPrimes
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem basecond_exists_above {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (OF E)) :
    ∃ P : HeightOneSpectrum (𝓞 E), below P = v := by
  have hinj : Function.Injective (algebraMap (OF E) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective (OF E) (𝓞 E)
  obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 E) v.asIdeal ⊥
    (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot, ← map_zero (algebraMap (OF E) (𝓞 E))] at hx
      rw [hinj hx]
      exact v.asIdeal.zero_mem)
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQv]
    exact Ideal.comap_bot_of_injective _ hinj
  refine ⟨⟨Q, hQ, hQne⟩, ?_⟩
  ext x
  simp [below, Ideal.under, ← hQv]

theorem basecond_natCast_mem_below {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    (n : OF E) ∈ (below P).asIdeal ↔ (n : 𝓞 E) ∈ P.asIdeal := by
  simp [below, Ideal.under, Ideal.mem_comap, map_natCast]

theorem isBaseCond_cond0 : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)), (∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ∀ P : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ P.asIdeal → Splits (below P)) → PlacesOk H q0 w0 → IsBaseCond (cond0 H w0) := by
  intro R H q0 w0 hspl hok
  have hprime : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p.Prime := fun p hp => (hok.splits p hp).1

  have hN0 : ((H.g 0 * H.g 1 * H.pde * H.pde' : ℕ) : OF H.E) ≠ 0 := by
    have h : H.g 0 * H.g 1 * H.pde * H.pde' ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_ <;>
        exact (hprime _ (by simp)).ne_zero
    exact_mod_cast h
  have hle : cond0 H w0 ≤ (below w0).asIdeal := by
    unfold cond0
    first
    | exact Ideal.mul_le_right
    | exact Ideal.mul_le_left
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rcases Ideal.mul_eq_bot.mp h with h1 | h1
    · rw [← Ideal.zero_eq_bot] at h1
      have h2 := pow_eq_zero_iff (two_ne_zero) |>.mp h1
      rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at h2
      exact hN0 h2
    · exact (below w0).ne_bot h1
  · intro h
    exact (below w0).isPrime.ne_top (top_le_iff.mp (h ▸ hle))
  · intro v hv

    obtain ⟨p, hp, hpv⟩ : ∃ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ((p : ℕ) : OF H.E) ∈ v.asIdeal := by
      have hvp : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
      rcases hvp.dvd_or_dvd hv with h | h
      · have h1 : ((H.g 0 * H.g 1 * H.pde * H.pde' : ℕ) : OF H.E) ∈ v.asIdeal :=
          (Ideal.span_singleton_le_iff_mem _).mp (Ideal.le_of_dvd (hvp.dvd_of_dvd_pow h))
        push_cast at h1
        rcases v.isPrime.mem_or_mem h1 with h1 | h1
        · rcases v.isPrime.mem_or_mem h1 with h1 | h1
          · rcases v.isPrime.mem_or_mem h1 with h1 | h1
            · exact ⟨H.g 0, by simp, h1⟩
            · exact ⟨H.g 1, by simp, h1⟩
          · exact ⟨H.pde, by simp, h1⟩
        · exact ⟨H.pde', by simp, h1⟩
      · have h1 : (below w0).asIdeal = v.asIdeal :=
          ((below w0).isMaximal).eq_of_le v.isPrime.ne_top (Ideal.le_of_dvd h)
        refine ⟨q0, by simp, ?_⟩
        rw [← h1, basecond_natCast_mem_below]
        exact hok.referencePlaceOverPrime
    obtain ⟨P, hPv⟩ := basecond_exists_above v
    have hpP : ((p : ℕ) : 𝓞 H.E) ∈ P.asIdeal := by
      rw [← basecond_natCast_mem_below, hPv]
      exact hpv
    obtain ⟨hpr, hp2, hdisc, hnorm⟩ := hok.splits p hp
    refine ⟨hPv ▸ hspl p hp P hpP, ?_, p, hpr, hp2, hpv, hdisc, hnorm⟩

    obtain ⟨e4, eb, e0⟩ := _root_.GlobalTheory.LamTie.expIn_cond0 R H q0 w0 hok P
    rw [← hPv]
    by_cases h4 : Over4 H P
    · rw [e4 h4]
    · by_cases hb : below P = below w0
      · rw [(eb hb).2]; norm_num
      · rw [e0 h4 hb]; norm_num

end GlobalTheory.LamTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsComplDescCompl
section
namespace GlobalTheory.RetractionComplement

open Formalism.MainNotions.N Matrix

section SlopeTestRemainingChoices

variable {k k' : Type} [Field k] [Field k'] [Algebra k k'] {n : ℕ}

theorem exists_retraction : ∃ l : k' →ₗ[k] k, ∀ c : k, l (algebraMap k k' c) = c := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k k')
    (LinearMap.ker_eq_bot.mpr (algebraMap k k').injective)
  exact ⟨g, fun c => by simpa using LinearMap.congr_fun hg c⟩

theorem form_mulVec (l : k' →ₗ[k] k) (A : Matrix (Fin n) (Fin n) k) (x : Fin n → k') :
    (fun i => l ((A.map (algebraMap k k')).mulVec x i)) = A.mulVec (fun i => l (x i)) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

theorem ext_mulVec (A : Matrix (Fin n) (Fin n) k) (v : Fin n → k) :
    (A.map (algebraMap k k')).mulVec (fun i => algebraMap k k' (v i))
      = fun i => algebraMap k k' (A.mulVec v i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

def extSub (k' : Type) [Field k'] [Algebra k k'] (W : Submodule k (Fin n → k)) :
    Submodule k' (Fin n → k') :=
  Submodule.span k' ((fun (v : Fin n → k) (i : Fin n) => algebraMap k k' (v i)) '' W)

theorem form_mem (l : k' →ₗ[k] k) (W : Submodule k (Fin n → k)) (x : Fin n → k')
    (hx : x ∈ extSub k' W) : (fun i => l (x i)) ∈ W := by
  have key : ∀ c : k', (fun i => l (c * x i)) ∈ W := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      intro c
      convert W.smul_mem (l c) hw using 1
      funext i
      rw [Pi.smul_apply, smul_eq_mul, mul_comm c, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
    | zero =>
      intro c
      convert W.zero_mem using 1
      funext i
      simp
    | add y z _ _ hy hz =>
      intro c
      convert W.add_mem (hy c) (hz c) using 1
      funext i
      simp [mul_add]
    | smul a y _ hy =>
      intro c
      convert hy (c * a) using 1
      funext i
      simp [mul_assoc]
  simpa using key 1

theorem extSub_stable (A : Matrix (Fin n) (Fin n) k) (W : Submodule k (Fin n → k))
    (hA : ∀ v ∈ W, A.mulVec v ∈ W) (x : Fin n → k') (hx : x ∈ extSub k' W) :
    (A.map (algebraMap k k')).mulVec x ∈ extSub k' W := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    rw [ext_mulVec]
    exact Submodule.subset_span ⟨_, hA w hw, rfl⟩
  | zero =>
    rw [Matrix.mulVec_zero]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem _ hy hz
  | smul a y _ hy =>
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ a hy

def descCompl (l : k' →ₗ[k] k) (W : Submodule k (Fin n → k)) (U : Submodule k' (Fin n → k')) :
    Submodule k (Fin n → k) where
  carrier := {v | ∃ x ∈ extSub k' W, ∃ u ∈ U, x + u = (fun i => algebraMap k k' (v i)) ∧
    (fun i => l (x i)) = 0}
  zero_mem' := ⟨0, Submodule.zero_mem _, 0, U.zero_mem, by funext i; simp, by funext i; simp⟩
  add_mem' := by
    rintro v w ⟨x, hx, u, hu, h1, h2⟩ ⟨x', hx', u', hu', h1', h2'⟩
    refine ⟨x + x', Submodule.add_mem _ hx hx', u + u', U.add_mem hu hu', ?_, ?_⟩
    · funext i
      have a := congrFun h1 i
      have b := congrFun h1' i
      simp only [Pi.add_apply, map_add (f := _)] at a b ⊢
      rw [← a, ← b]; ring
    · funext i
      have a := congrFun h2 i
      have b := congrFun h2' i
      simp only [Pi.add_apply, map_add (f := _), Pi.zero_apply] at a b ⊢
      rw [a, b, add_zero]
  smul_mem' := by
    rintro c v ⟨x, hx, u, hu, h1, h2⟩
    refine ⟨algebraMap k k' c • x, Submodule.smul_mem _ _ hx, algebraMap k k' c • u,
      U.smul_mem _ hu, ?_, ?_⟩
    · funext i
      have a := congrFun h1 i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_mul] at a ⊢
      rw [← a]; ring
    · funext i
      have a := congrFun h2 i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at a ⊢
      rw [← Algebra.smul_def, map_smul, a, smul_zero]

theorem isCompl_descCompl (l : k' →ₗ[k] k) (hl : ∀ c : k, l (algebraMap k k' c) = c)
    (W : Submodule k (Fin n → k)) (U : Submodule k' (Fin n → k'))
    (h : IsCompl (extSub k' W) U) : IsCompl W (descCompl l W U) := by
  have hmem : ∀ v ∈ W, (fun i => algebraMap k k' (v i)) ∈ extSub k' W :=
    fun v hv => Submodule.subset_span ⟨v, hv, rfl⟩
  have hback : ∀ v : Fin n → k, (fun i => l (algebraMap k k' (v i))) = v :=
    fun v => funext fun i => hl (v i)
  constructor
  · rw [Submodule.disjoint_def]
    rintro v hv ⟨x, hx, u, hu, h1, h2⟩
    have hu' : u ∈ extSub k' W := by
      have e : u = (fun i => algebraMap k k' (v i)) - x := by rw [← h1]; abel
      rw [e]
      exact Submodule.sub_mem _ (hmem v hv) hx
    have hu0 : u = 0 := (Submodule.disjoint_def.mp h.disjoint) u hu' hu
    rw [hu0, add_zero] at h1
    rw [h1, hback] at h2
    exact h2
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : (fun i => algebraMap k k' (v i)) ∈ extSub k' W ⊔ U := by
      rw [h.sup_eq_top]
      trivial
    obtain ⟨x, hx, u, hu, hxu⟩ := Submodule.mem_sup.mp hv
    obtain ⟨w, hw⟩ : ∃ w : Fin n → k, w = fun i => l (x i) := ⟨_, rfl⟩
    have hwW : w ∈ W := hw ▸ form_mem l W x hx
    have hd : v - w ∈ descCompl l W U := by
      refine ⟨x - fun i => algebraMap k k' (w i), Submodule.sub_mem _ hx (hmem w hwW), u, hu, ?_, ?_⟩
      · funext i
        have e := congrFun hxu i
        simp only [Pi.add_apply, Pi.sub_apply, map_sub] at e ⊢
        rw [← e]
        ring
      · funext i
        simp [hw, hl]
    simpa using Submodule.add_mem_sup hwW hd

theorem descCompl_stable (l : k' →ₗ[k] k) (A : Matrix (Fin n) (Fin n) k)
    (W : Submodule k (Fin n → k)) (U : Submodule k' (Fin n → k'))
    (hA : ∀ v ∈ W, A.mulVec v ∈ W)
    (hU : ∀ u ∈ U, (A.map (algebraMap k k')).mulVec u ∈ U) :
    ∀ v ∈ descCompl l W U, A.mulVec v ∈ descCompl l W U := by
  rintro v ⟨x, hx, u, hu, h1, h2⟩
  refine ⟨(A.map (algebraMap k k')).mulVec x, extSub_stable A W hA x hx,
    (A.map (algebraMap k k')).mulVec u, hU u hu, ?_, ?_⟩
  · rw [← Matrix.mulVec_add, h1, ext_mulVec]
  · rw [form_mulVec, h2, Matrix.mulVec_zero]

end SlopeTestRemainingChoices

theorem isSSRep_of_mapRep {Γ k k' : Type} [Group Γ] [Field k] [Field k'] {n : ℕ}
    (ι : k →+* k') (ρ : Γ →* GL (Fin n) k) (h : IsSSRep (mapRep ι ρ)) : IsSSRep ρ := by
  let _ : Algebra k k' := ι.toAlgebra
  have hcoe : ∀ g, ((mapRep ι ρ g : GL (Fin n) k') : Matrix (Fin n) (Fin n) k') =
      (ρ g : Matrix (Fin n) (Fin n) k).map (algebraMap k k') := fun _ => rfl
  obtain ⟨l, hl⟩ := exists_retraction (k := k) (k' := k')
  intro W hW
  have hWe : IsInv (mapRep ι ρ) (extSub k' W) := fun g x hx => by
    rw [hcoe]
    exact extSub_stable _ W (hW g) x hx
  obtain ⟨U, hU, hc⟩ := h _ hWe
  refine ⟨descCompl l W U, fun g => ?_, isCompl_descCompl l hl W U hc⟩
  exact descCompl_stable l _ W U (hW g) fun u hu => by
    rw [← hcoe]
    exact hU g u hu

end GlobalTheory.RetractionComplement
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeLocalizedOfTorsionBoundedStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemilinearBaseChange_localized_of_torsion_bounded : ∀ (A : Type) [CommRing A] (φ : A →+* A) (t : A) (N : Type) [AddCommGroup N] [Module A N] (P : Type) [AddCommGroup P] [Module A P] (u : N →ₛₗ[φ] P), SemiBC u → ∀ (L : P →ₗ[A] N) (n a : ℕ), (∀ y, L y = 0 → t ^ n • y = 0) → (∀ x, ∃ y, L y = t ^ n • x) → ∀ Φ : N →ₛₗ[(algebraMap A (Localization.Away t)).comp φ] LocalizedModule (Submonoid.powers t) N, (∀ x, IsFrac t (Φ x) (L (u x)) a) → SemiBC Φ := by
  first | exact @GlobalTheory.BSP.semiBC_localized | exact GlobalTheory.BSP.semiBC_localized | (intros; apply GlobalTheory.BSP.semiBC_localized <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfTwoMem
section
noncomputable section

namespace GlobalTheory.BaseChangeExistsCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Matrix

section Definite

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem emb_hD (S : HSpace E) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) (x : S.V) :
    τ (S.hD x x) = star (fun a => τ (S.frame.repr x a)) ⬝ᵥ
      (S.gram.map τ *ᵥ fun a => τ (S.frame.repr x a)) := by
  rw [HSpace.hD, hT_expand]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hτ, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, Matrix.map_apply,
    mul_assoc]
  rfl

theorem denseRange_emb [_root_.NumberField.IsTotallyComplex E] (τ : E →+* ℂ) : DenseRange τ := by
  rcases Complex.subfield_eq_of_closed (Subfield.isClosed_topologicalClosure τ.fieldRange) with h | h
  · exfalso
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx : τ x ∈ τ.fieldRange.topologicalClosure :=
      Subfield.le_topologicalClosure _ ⟨x, rfl⟩
    rw [h] at hx
    obtain ⟨r, hr⟩ := hx
    rw [ComplexEmbedding.conjugate_coe_eq, ← hr]
    simp
  · have : closure (Set.range τ) = Set.univ := congrArg (fun K : Subfield ℂ => (K : Set ℂ)) h
    exact dense_iff_closure_eq.2 this

theorem closed_of_coords [_root_.NumberField.IsTotallyComplex E] (S : HSpace E) (τ : E →+* ℂ) {C : Set (Fin S.rank → ℂ)}
    (hC : IsClosed C) (h : ∀ x : S.V, (fun a => τ (S.frame.repr x a)) ∈ C) (y : Fin S.rank → ℂ) : y ∈ C := by
  have hd : DenseRange (Pi.map fun (_ : Fin S.rank) => (τ : E → ℂ)) :=
    DenseRange.piMap fun _ => denseRange_emb τ
  refine hd.induction_on y hC fun v => ?_
  have := h (S.frame.equivFun.symm v)
  have e : (fun a => τ (S.frame.repr (S.frame.equivFun.symm v) a)) =
      Pi.map (fun (_ : Fin S.rank) => (τ : E → ℂ)) v := by
    funext a
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rfl
  rwa [e] at this

theorem coords_ne_zero (S : HSpace E) (τ : E →+* ℂ) {x : S.V} (hx : x ≠ 0) :
    (fun a => τ (S.frame.repr x a)) ≠ 0 := by
  intro h
  apply hx
  rw [← S.frame.repr.map_eq_zero_iff]
  ext a
  simpa using congrFun h a

theorem continuous_quad {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun y : Fin n → ℂ => (star y ⬝ᵥ (M *ᵥ y)).re := by
  simp only [dotProduct, mulVec, Pi.star_apply]
  fun_prop

theorem sig_pos_iff [_root_.NumberField.IsTotallyComplex E] (S : HSpace E) (hS : S.SigOK) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) :
    S.sig τ = (S.rank, 0) ↔ ∀ x : S.V, x ≠ 0 → 0 < (τ (S.hD x x)).re := by
  constructor
  · intro h x hx
    have hs := hS τ
    rw [h] at hs
    have := Formalism.UG.P.stdform_sig_pos _ hs _ (coords_ne_zero S τ hx)
    rwa [Formalism.UG.P.stdform_Q_dot, ← emb_hD S τ hτ] at this
  · intro h
    have hall : ∀ y : Fin S.rank → ℂ, 0 ≤ (star y ⬝ᵥ (S.gram.map τ *ᵥ y)).re := fun y =>
      closed_of_coords S τ (isClosed_le continuous_const (continuous_quad (S.gram.map τ))) (fun x => by
        show (0 : ℝ) ≤ _
        rw [← emb_hD S τ hτ]
        rcases eq_or_ne x 0 with rfl | hx
        · simp [HSpace.hD]
        · exact (h x hx).le) y
    obtain ⟨-, Q, hQ⟩ := Formalism.UG.P.sig_data _ _ _ (hS τ)
    have hsum := sig_sum S hS τ
    have hq : (S.sig τ).2 = 0 := by
      by_contra hq
      have h1 := hall (Q *ᵥ Pi.single (Sum.inr ⟨0, Nat.pos_of_ne_zero hq⟩) 1)
      rw [Formalism.UG.P.sig_quad _ Q hQ] at h1
      simp [Pi.single_apply] at h1
      linarith
    exact Prod.ext (by simp only; omega) hq

theorem sig_neg_iff [_root_.NumberField.IsTotallyComplex E] (S : HSpace E) (hS : S.SigOK) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) :
    S.sig τ = (0, S.rank) ↔ ∀ x : S.V, x ≠ 0 → (τ (S.hD x x)).re < 0 := by
  constructor
  · intro h x hx
    have hs := hS τ
    rw [h] at hs
    have := Formalism.UG.P.stdform_sig_neg _ hs _ (coords_ne_zero S τ hx)
    rwa [Formalism.UG.P.stdform_Q_dot, ← emb_hD S τ hτ] at this
  · intro h
    have hall : ∀ y : Fin S.rank → ℂ, (star y ⬝ᵥ (S.gram.map τ *ᵥ y)).re ≤ 0 := fun y =>
      closed_of_coords S τ (isClosed_le (continuous_quad (S.gram.map τ)) continuous_const) (fun x => by
        show _ ≤ (0 : ℝ)
        rw [← emb_hD S τ hτ]
        rcases eq_or_ne x 0 with rfl | hx
        · simp [HSpace.hD]
        · exact (h x hx).le) y
    obtain ⟨-, Q, hQ⟩ := Formalism.UG.P.sig_data _ _ _ (hS τ)
    have hsum := sig_sum S hS τ
    have hp : (S.sig τ).1 = 0 := by
      by_contra hp
      have h1 := hall (Q *ᵥ Pi.single (Sum.inl ⟨0, Nat.pos_of_ne_zero hp⟩) 1)
      rw [Formalism.UG.P.sig_quad _ Q hQ] at h1
      simp [Pi.single_apply] at h1
      linarith
    exact Prod.ext hp (by simp only; omega)

end Definite

theorem unram_of_cm (D : D7) (hc : @CMData D.host.F D.host.E _ _ _ _ D.host.cmStar _) (w : PlE D.host) :
    Algebra.IsUnramifiedAt (𝓞 D.host.F) w.asIdeal := by
  letI := D.host.cmStar
  haveI := D.host.isCMField_hostE
  have hU : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) :=
    Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
      obtain ⟨θ, t, ht, hθ⟩ := hc.cmUnram.2.2 P hP
      refine ⟨θ, ?_⟩
      have : RingOfIntegers.mapRingEquiv
          (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
        RingOfIntegers.ext ht.symm
      rwa [this]
  exact Algebra.unramified_iff_forall.1 hU ⟨w.asIdeal, w.isPrime⟩

section Concl

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

end Concl

end GlobalTheory.BaseChangeExistsCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitBdRPlusMatrixOfCongrOneStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_bdRPlus_matrix_of_congr_one : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S) (B : Matrix (Fin d) (Fin d) (Per.BdRp l)), (∀ i j, bk.E ∣ (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) i j) → (∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l 1) → IsUnit B := by
  first | (exact @GlobalTheory.BKLim.UnitFil.isUnit_of_congr_one) | (exact GlobalTheory.BKLim.UnitFil.isUnit_of_congr_one) | (intros; apply GlobalTheory.BKLim.UnitFil.isUnit_of_congr_one  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabCompat
section
open GlobalTheory.LiftLeaf GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.LabelCompat

theorem labCompat : ∀ (D : D7) (i : D.nd.Loc), LabCompat D.nd D.naut i := by
  intro D i σ Sig hσ
  have key : ∀ k, D.nd.lab k σ = fun v =>
      D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v)) := by
    intro k
    funext v
    rw [D.naut.lab_loc i k σ v, hσ.2.2 _ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v)]
  unfold NData.goodRow goodSig
  refine forall_congr' fun k => ?_
  rw [key k]

end GlobalTheory.LabelCompat
end

