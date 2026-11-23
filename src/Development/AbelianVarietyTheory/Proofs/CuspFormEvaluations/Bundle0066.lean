module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.H2XNIffH2
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

section General

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (n : SecNorm B) (X : PJ D B P j) (E : PtExt X)
  (hM : IntAtExt X E)

abbrev xN : PJ D n.base P j := PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 (xplus X E hM)

def globalFamilyDataBaseChange {ka wL wF : WeightFamilies.Wt D j} (G : EtaleWeightGaps.GlobalFamilyData X ka wL wF) : EtaleWeightGaps.GlobalFamilyData (xN n X E hM) ka wL wF where
  N := G.N
  w := G.w
  del := G.del
  th' := G.th'
  rz := G.rz
  alz := G.alz
  th0 := G.th0
  zc := G.zc
  rq := G.rq
  th := G.th
  iet := G.iet
  et := G.et
  mx := G.mx

end General

end GlobalTheory.RunIn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HalfLevelGeneratorNorm
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem half_level_generator_norm :
    ∀ (D : D7) (T : Top D) (_h : LawsP T) (_EX : ErrX D), ∃ α : 𝓞 D.host.E, α * T.Q.H.bar α = (T.Q.l.M : 𝓞 D.host.E) ∧ T.Q.l.Mb = Ideal.span {T.Q.H.bar α} := by
  intro D T h _EX
  have hM : LawsM T.toCore := h.toLawsCore.toLawsM

  have hbb : ∀ x : 𝓞 D.host.E, T.Q.H.bar (T.Q.H.bar x) = x := by
    intro x
    rw [bar_core T.toCore, bar_core T.toCore, barE_barE]

  have hn : ∀ i, piOf T.toCore _EX i * T.Q.H.bar (piOf T.toCore _EX i) = (D.host.g i : 𝓞 D.host.E) := by
    intro i
    rw [bar_core T.toCore]
    exact piOf_mul_barE T.toCore _EX i
  set π₀ := piOf T.toCore _EX 0
  set π₁ := piOf T.toCore _EX 1
  refine ⟨T.Q.H.bar (π₀ * π₁), ?_, ?_⟩
  · rw [hbb, map_mul, level_M T.toCore hM]
    have h0 := hn 0
    have h1 := hn 1
    push_cast
    rw [← h0, ← h1]
    ring
  · rw [hbb, Mb_eq T.toCore hM, ← span_piOf T.toCore hM _EX 0, ← span_piOf T.toCore hM _EX 1,
      Ideal.span_singleton_mul_span_singleton]

end GlobalTheory.RunIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IndepSpanRankTransferLargeFieldComplex
section
-- Use the fraction-ring instances directly so repeated maps can be matched by `simp` and `rw`.
set_option backward.inferInstanceAs.wrap false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory.ReadingTransfer

theorem exists_coeffs {K A s μ : Type} [Field K] [CommRing A] [Algebra K A] [Fintype μ] (w : μ → A)
    (p : MvPolynomial s A) (hp : ∀ m, p.coeff m ∈ Submodule.span K (Set.range w)) :
    ∃ c : μ → MvPolynomial s K, p = ∑ k, MvPolynomial.map (algebraMap K A) (c k) * MvPolynomial.C (w k) := by
  classical
  choose f hf using fun m => (Submodule.mem_span_range_iff_exists_fun K).1 (hp m)
  refine ⟨fun k => ∑ m ∈ p.support, MvPolynomial.monomial m (f m k), ?_⟩
  ext m
  have hcf : ∀ k, (∑ m' ∈ p.support, MvPolynomial.monomial m' (f m' k)).coeff m =
      if m ∈ p.support then f m k else 0 := by
    intro k
    rw [MvPolynomial.coeff_sum]
    simp [MvPolynomial.coeff_monomial]
  rw [MvPolynomial.coeff_sum]
  simp only [mul_comm _ (MvPolynomial.C _), MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, hcf]
  by_cases hm : m ∈ p.support
  · rw [← hf m]
    simp only [hm, ↓reduceIte, Algebra.smul_def, Algebra.commutes]
  · simp only [hm, ↓reduceIte, map_zero, mul_zero, Finset.sum_const_zero]
    simpa using hm

theorem eval_comb {K A s μ F M : Type} [Field K] [CommRing A] [Algebra K A] [Fintype μ] [Field F] [CommRing M]
    [Algebra F M] (κ : K →+* F) (e : A →+* M) (he : ∀ (a : K) (x : A), e (a • x) = κ a • e x) (τ : s → F)
    (τ' : s → M) (hτ : ∀ i, τ' i = algebraMap F M (τ i)) (w : μ → A) (c : μ → MvPolynomial s K) :
    MvPolynomial.eval₂Hom e τ' (∑ k, MvPolynomial.map (algebraMap K A) (c k) * MvPolynomial.C (w k)) =
      Fintype.linearCombination F (fun k => e (w k)) (fun k => MvPolynomial.eval₂Hom κ τ (c k)) := by
  have hcomp : (algebraMap F M).comp κ = e.comp (algebraMap K A) := by
    ext a
    rw [RingHom.comp_apply, RingHom.comp_apply, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, he, map_one]
  obtain rfl : τ' = fun i => algebraMap F M (τ i) := funext hτ
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, MvPolynomial.eval₂_map,
    Fintype.linearCombination_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def, MvPolynomial.eval₂_comp_left, hcomp] <;> rfl

theorem inj_transfer {F V W ι : Type} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (L : V →ₗ[F] W) (hL : Function.Injective L) (v : ι → V) :
    (LinearIndependent F (fun i => L (v i)) ↔ LinearIndependent F v) ∧
    (∀ x, L x ∈ Submodule.span F (Set.range fun i => L (v i)) ↔ x ∈ Submodule.span F (Set.range v)) ∧
    Module.finrank F (Submodule.span F (Set.range fun i => L (v i))) =
      Module.finrank F (Submodule.span F (Set.range v)) := by
  have hspan : Submodule.span F (Set.range fun i => L (v i)) = (Submodule.span F (Set.range v)).map L := by
    rw [Submodule.map_span, ← Set.range_comp] <;> rfl
  refine ⟨L.linearIndependent_iff (LinearMap.ker_eq_bot.mpr hL), fun x => ?_, ?_⟩
  · rw [hspan]
    exact ⟨fun ⟨y, hy, hxy⟩ => hL hxy ▸ hy, fun hx => Submodule.mem_map_of_mem hx⟩
  · rw [hspan]
    exact (Submodule.equivMapOfInjective L hL _).finrank_eq.symm

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

noncomputable def kap (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) : B.KO →+* Kp X la N :=
  (algebraMap (X.Kl la) (Kp X la N)).comp (algebraMap B.KO (X.Kl la))

theorem emb_smul' (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (a : B.KO) (F : X.Forms) :
    emb X la N (a • F) = kap X la N a • emb X la N F := by
  rw [Formalism.MainNotions.Gaps.EtaleWeightGaps.emb_smul]
  exact (algebraMap_smul (Kp X la N) (algebraMap B.KO (X.Kl la) a) (emb X la N F)).symm

theorem emb_indep (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) {μ : Type} (w : μ → X.Forms)
    (hw : LinearIndependent B.KO w) : LinearIndependent (Kp X la N) fun k => emb X la N (w k) := by
  classical
  have hs := hw.linearIndepOn_id
  let b3 := Algebra.TensorProduct.basis (Kp X la N) (Algebra.TensorProduct.basis (X.Kl la) (Module.Basis.extend hs))
  let idx : μ → hs.extend (Set.subset_univ _) := fun k => ⟨w k, hs.subset_extend _ (Set.mem_range_self k)⟩
  have hidx : Function.Injective idx := fun k l h => hw.injective (congrArg Subtype.val h)
  have e : (fun k => emb X la N (w k)) = ⇑b3 ∘ idx := by
    funext k
    rw [Formalism.MainNotions.Gaps.EtaleWeightGaps.emb_apply]
    simp only [b3, idx, Function.comp_apply, Algebra.TensorProduct.basis_apply, Module.Basis.extend_apply_self] <;> rfl
  rw [e]
  exact b3.linearIndependent.comp idx hidx

theorem eval_injective (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) :
    Function.Injective (MvPolynomial.eval₂Hom (kap X la N)
      (fun p : Idx D j N => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p))) := by
  classical
  let f : Op X la N →+* Kp X la N :=
    @algebraMap (Op X la N) (Kp X la N) _
      _
      _
  have key : ∀ Q : MvPolynomial (Idx D j N) (X.Ol la),
      MvPolynomial.aeval (f ∘ Tv X la N) Q =
        f (algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Pol X la N) (Op X la N) Q) := by
    intro Q
    have heval : MvPolynomial.eval₂Hom (algebraMap (X.Ol la) (Kp X la N)) (f ∘ Tv X la N) =
        f.comp (algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Pol X la N) (Op X la N)) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, ← MvPolynomial.algebraMap_eq,
          ← IsScalarTower.algebraMap_apply (X.Ol la)
            (Formalism.MainNotions.Gaps.EtaleWeightGaps.Pol X la N) (Op X la N)] <;> rfl
      · intro p
        rw [MvPolynomial.eval₂Hom_X']
        rfl
    exact DFunLike.congr_fun heval Q
  have hinj : Function.Injective fun Q : Formalism.MainNotions.Gaps.EtaleWeightGaps.Pol X la N =>
      f (algebraMap (Formalism.MainNotions.Gaps.EtaleWeightGaps.Pol X la N) (Op X la N) Q) :=
    (IsFractionRing.injective (Op X la N) (Kp X la N)).comp
      (IsLocalization.injective (M := (Formalism.MainNotions.Gaps.EtaleWeightGaps.gI X la N).primeCompl) (S := Op X la N)
        (Formalism.MainNotions.Gaps.EtaleWeightGaps.gI X la N).primeCompl_le_nonZeroDivisors)
  have hOl : AlgebraicIndependent (X.Ol la) (f ∘ Tv X la N) :=
    algebraicIndependent_iff_injective_aeval.2 fun Q₁ Q₂ h => hinj (by simpa only [key] using h)
  haveI : Algebra.IsAlgebraic (X.Ol la) (X.Kl la) :=
    IsLocalization.isAlgebraic (S := X.Kl la) (M := nonZeroDivisors (X.Ol la))
  have hKl := algebraicIndependent_iff_injective_aeval.1 (hOl.extendScalars (X.Kl la))
  have hmap : Function.Injective (MvPolynomial.map (σ := Idx D j N) (algebraMap B.KO (X.Kl la))) :=
    MvPolynomial.map_injective _ (algebraMap B.KO (X.Kl la)).injective
  have e : ⇑(MvPolynomial.eval₂Hom (kap X la N)
        (fun p : Idx D j N => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p))) =
      ⇑(MvPolynomial.aeval (R := X.Kl la)
        fun p : Idx D j N => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p)) ∘
        MvPolynomial.map (algebraMap B.KO (X.Kl la)) := by
    funext Q
    simp only [Function.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.aeval_def,
      MvPolynomial.eval₂_map] <;> rfl
  rw [e]
  exact hKl.comp hmap

end GlobalTheory.ReadingTransfer

namespace GlobalTheory

open ReadingTransfer

theorem reading_transfer :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (R : Rdg X) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (t : Idx D j N → ℂ), R.Generic t → ∀ (u : WeightFamilies.Wt D j) (ι : Type) [Fintype ι] (p : ι → MvPolynomial (Idx D j N) X.Forms), (∀ i, OfWt X u (p i)) → (LinearIndependent (Kp X la N) (fun i => toRp X la N (p i)) ↔ LinearIndependent ℂ (fun i => R.toFn t (p i))) ∧ (∀ q, OfWt X u q → (toRp X la N q ∈ Submodule.span (Kp X la N) (Set.range fun i => toRp X la N (p i)) ↔ R.toFn t q ∈ Submodule.span ℂ (Set.range fun i => R.toFn t (p i)))) ∧ Module.finrank (Kp X la N) (Submodule.span (Kp X la N) (Set.range fun i => toRp X la N (p i))) = Module.finrank ℂ (Submodule.span ℂ (Set.range fun i => R.toFn t (p i))) := by
  intro D B P j X R la N t hgen u ι _ p hp
  classical
  let b := Module.finBasis B.KO (B.Cusp j u)
  let v : Fin (Module.finrank B.KO (B.Cusp j u)) → X.Forms := fun k => X.inc u (b k)
  have hv : LinearIndependent B.KO v :=
    b.linearIndependent.map' (X.inc u) (LinearMap.ker_eq_bot.mpr (X.inc_inj u))
  have hspan : LinearMap.range (X.inc u) = Submodule.span B.KO (Set.range v) := by
    rw [LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span, ← Set.range_comp] <;> rfl
  have hcoef : ∀ q : MvPolynomial (Idx D j N) X.Forms, OfWt X u q →
      ∀ m, q.coeff m ∈ Submodule.span B.KO (Set.range v) := fun q hq m => hspan ▸ hq m
  let φ : MvPolynomial (Idx D j N) B.KO →+* Kp X la N :=
    MvPolynomial.eval₂Hom (kap X la N) (fun p => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p))
  let ψ : MvPolynomial (Idx D j N) B.KO →+* ℂ := MvPolynomial.eval₂Hom R.σ t
  have hφ : Function.Injective φ := eval_injective X la N
  have hψ : Function.Injective ψ := (injective_iff_map_eq_zero ψ).2 fun Q hQ => by
    by_contra h
    exact hgen Q h hQ
  let LK := Fintype.linearCombination (Kp X la N) (fun k => emb X la N (v k))
  let LC := Fintype.linearCombination ℂ (fun k => R.ev (v k))
  have hLK : Function.Injective LK :=
    linearIndependent_iff_injective_fintypeLinearCombination.1 (emb_indep X la N v hv)
  have hLC : Function.Injective LC :=
    linearIndependent_iff_injective_fintypeLinearCombination.1 (R.indep u _ b b.linearIndependent)
  have hK : ∀ (q : MvPolynomial (Idx D j N) X.Forms) (c : Fin (Module.finrank B.KO (B.Cusp j u)) → MvPolynomial (Idx D j N) B.KO),
      q = ∑ k, MvPolynomial.map (algebraMap B.KO X.Forms) (c k) * MvPolynomial.C (v k) →
        toRp X la N q = LK fun k => φ (c k) := by
    rintro q c rfl
    exact eval_comb (kap X la N) (emb X la N) (emb_smul' X la N)
      (fun p => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p))
      (fun p => algebraMap (Op X la N) (Rp X la N) (Tv X la N p))
      (fun p => IsScalarTower.algebraMap_apply (Op X la N) (Kp X la N) (Rp X la N) _) v c
  have hC : ∀ (q : MvPolynomial (Idx D j N) X.Forms) (c : Fin (Module.finrank B.KO (B.Cusp j u)) → MvPolynomial (Idx D j N) B.KO),
      q = ∑ k, MvPolynomial.map (algebraMap B.KO X.Forms) (c k) * MvPolynomial.C (v k) →
        R.toFn t q = LC fun k => ψ (c k) := by
    rintro q c rfl
    exact eval_comb R.σ R.ev R.ev_smul t (fun p _ => t p) (fun p => rfl) v c
  choose c hc using fun i => exists_coeffs v (p i) (hcoef _ (hp i))
  have eK : (fun i => toRp X la N (p i)) = fun i => LK fun k => φ (c i k) := funext fun i => hK _ _ (hc i)
  have eC : (fun i => R.toFn t (p i)) = fun i => LC fun k => ψ (c i k) := funext fun i => hC _ _ (hc i)
  obtain ⟨iK, mK, rK⟩ := inj_transfer LK hLK fun i k => φ (c i k)
  obtain ⟨iC, mC, rC⟩ := inj_transfer LC hLC fun i k => ψ (c i k)
  obtain ⟨iA, mA, rA⟩ := rank_indep_mem_embedding_invariant _ _ _ φ ψ hφ hψ ι _ c
  refine ⟨?_, ?_, ?_⟩
  · rw [eK, eC, iK, iC]
    exact iA
  · intro q hq
    obtain ⟨d, hd⟩ := exists_coeffs v q (hcoef _ hq)
    rw [eK, eC, hK _ _ hd, hC _ _ hd, mK, mC]
    exact mA d
  · rw [eK, eC, rK, rC]
    exact rA

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeExpOfLogLe
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.LogSupMultiple

theorem le_exp_of_log_le {x b : ℝ} (h : Real.log x ≤ b) (hx : 0 ≤ x) : x ≤ Real.exp b := by
  rcases hx.eq_or_lt with rfl | hpos
  · exact (Real.exp_pos b).le
  · exact (Real.log_le_iff_le_exp hpos).1 h

theorem log_le_of_le_exp {x b : ℝ} (h : x ≤ Real.exp b) (hx : 0 ≤ x) (hb : 0 ≤ b) : Real.log x ≤ b := by
  rcases hx.eq_or_lt with rfl | hpos
  · simpa using hb
  · exact (Real.log_le_iff_le_exp hpos).2 h

theorem supN_sum_le {D : D7} (B : WeightFamilies.Prov D) (j : ℕ) (w : WeightFamilies.Wt D j) (σ : B.KO →+* ℂ) {ι : Type}
    (s : Finset ι) (F : ι → B.Cusp j w) :
    B.supN j w σ (∑ i ∈ s, F i) ≤ ∑ i ∈ s, B.supN j w σ (F i) :=
    Finset.le_sum_of_subadditive (B.supN j w σ) (le_of_eq ((B.supN_eq_zero j w σ 0).2 rfl))
      (B.supN_add j w σ) s F

theorem log_supN_bounds : ∀ (D : D7) (B : WeightFamilies.Prov D) (j : ℕ) (w : WeightFamilies.Wt D j), (∀ (σ : B.KO →+* ℂ) (s : B.KO) (F : B.Cusp j w) (a b : ℝ), 0 ≤ a + b → Real.log ‖σ s‖ ≤ a → Real.log (B.supN j w σ F) ≤ b → 0 ≤ b → 0 ≤ a → Real.log (B.supN j w σ (s • F)) ≤ a + b) ∧ (∀ (σ : B.KO →+* ℂ) (N : ℕ) (c : Fin N → ℕ) (F : Fin N → B.Cusp j w) (b : ℝ), 0 ≤ b → (∀ i, c i ≤ N) → (∀ i, Real.log (B.supN j w σ (F i)) ≤ b) → Real.log (B.supN j w σ (∑ i, (c i : B.KO) • F i)) ≤ 2 * Real.log N + b) ∧ ∀ b : ℝ, (∑ _σ : B.KO →+* ℂ, b) / (Fintype.card (B.KO →+* ℂ) : ℝ) = b := by
  intro D B j w
  refine ⟨?_, ?_, ?_⟩
  ·
    intro σ s F a b _ hs hF hb ha
    rw [B.supN_smul]
    have hF0 := B.supN_nonneg j w σ F
    have h1 : ‖σ s‖ ≤ Real.exp a := le_exp_of_log_le hs (norm_nonneg _)
    have h2 : B.supN j w σ F ≤ Real.exp b := le_exp_of_log_le hF hF0
    refine log_le_of_le_exp ?_ (mul_nonneg (norm_nonneg _) hF0) (add_nonneg ha hb)
    rw [Real.exp_add]
    exact mul_le_mul h1 h2 hF0 (Real.exp_pos a).le
  ·
    intro σ N c F b hb hc hF
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [Fin.sum_univ_zero, (B.supN_eq_zero j w σ 0).2 rfl]
      simpa using hb
    · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hNpos : (0 : ℝ) < N := by linarith
      have hsum : B.supN j w σ (∑ i, (c i : B.KO) • F i) ≤ (N : ℝ) * ((N : ℝ) * Real.exp b) :=
        calc B.supN j w σ (∑ i, (c i : B.KO) • F i)
            ≤ ∑ i, B.supN j w σ ((c i : B.KO) • F i) := supN_sum_le B j w σ _ _
          _ ≤ ∑ _i : Fin N, (N : ℝ) * Real.exp b := by
            apply Finset.sum_le_sum
            intro i _
            rw [B.supN_smul, map_natCast, Complex.norm_natCast]
            exact mul_le_mul (by exact_mod_cast hc i) (le_exp_of_log_le (hF i) (B.supN_nonneg _ _ _ _))
              (B.supN_nonneg _ _ _ _) hNpos.le
          _ = (N : ℝ) * ((N : ℝ) * Real.exp b) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hexp : Real.exp (2 * Real.log N + b) = (N : ℝ) * ((N : ℝ) * Real.exp b) := by
        rw [Real.exp_add, two_mul, Real.exp_add, Real.exp_log hNpos]
        ring
      refine log_le_of_le_exp ?_ (B.supN_nonneg _ _ _ _) ?_
      · rw [hexp]
        exact hsum
      · have := Real.log_nonneg hN1
        linarith
  ·
    intro b
    have hcard : (Fintype.card (B.KO →+* ℂ) : ℝ) ≠ 0 := by
      have : 0 < Fintype.card (B.KO →+* ℂ) := Fintype.card_pos
      exact_mod_cast this.ne'
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_div_cancel_left₀ b hcard

end GlobalTheory.LogSupMultiple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogLeOfLePowMulPow
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem log_le_of_le_pow_mul_pow {N g₀ g₁ d X m : ℕ} {a c P : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hP : 0 ≤ P)
    (h₀ : Real.log g₀ ≤ a) (h₁ : Real.log g₁ ≤ a) (hd : Real.log d ≤ P) (hX : Real.log X ≤ c)
    (hN : N ≤ (g₀ * g₁) ^ m * (d * X ^ m)) : Real.log N ≤ m * (2 * a + c) + P := by
  rcases Nat.eq_zero_or_pos N with rfl | hpos
  · simp only [Nat.cast_zero, Real.log_zero]; positivity
  have key : ∀ (x : ℕ) (t : ℝ), Real.log x ≤ t → (x : ℝ) ≤ Real.exp t := fun x t h =>
    (Real.le_exp_log _).trans (Real.exp_le_exp.2 h)
  have e₀ := key _ _ h₀
  have e₁ := key _ _ h₁
  have e₂ := key _ _ hd
  have e₃ := key _ _ hX
  have hN' : (N : ℝ) ≤ ((g₀ : ℝ) * g₁) ^ m * (d * (X : ℝ) ^ m) := by exact_mod_cast hN
  rw [Real.log_le_iff_le_exp (by exact_mod_cast hpos)]
  calc (N : ℝ) ≤ ((g₀ : ℝ) * g₁) ^ m * (d * (X : ℝ) ^ m) := hN'
    _ ≤ (Real.exp a * Real.exp a) ^ m * (Real.exp P * Real.exp c ^ m) := by gcongr
    _ = Real.exp (m * (2 * a + c) + P) := by
      rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1; ring

theorem frn_le_size_sub_one {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) :
    ((D.R.f * D.R.r * w.n : ℕ) : ℝ) ≤ w.size - 1 := by
  unfold WeightFamilies.Wt.size
  have h1 : (0 : ℝ) ≤ ∑ τ, (∑ i, (w.aP τ i : ℝ) + ∑ i, (w.aM τ i : ℝ)) := by positivity
  have h2 : (1 : ℝ) ≤ ((max (D.R.sigW j).2 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
  have h3 : (D.R.f : ℝ) * 1 * D.R.r * w.n ≤ D.R.f * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * D.R.r * w.n := by
    gcongr
  rw [Nat.cast_mul, Nat.cast_mul]
  linarith

theorem log_count_le_mul_size : ∀ (D : D7) (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j) (N : ℕ) (Prw : ℝ), 2 ≤ large₂.sc.L → 0 < w.n → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → OPO large₂ B → 38 * large₂.sc.L + PO D large₂ ≤ Prw → N ≤ (D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r * w.n) * (Module.finrank ℚ B.KO * (1 + WeightAlgebra.DF w) ^ (D.R.f * D.R.r * w.n)) → Real.log N ≤ Prw * (w.size - 1) := by
  intro D B large₂ j w N Prw hL hn hp hO hPrw hN
  have hP : 0 ≤ PO D large₂ := by
    unfold PO
    have : 0 ≤ large₂.sc.L := by linarith
    positivity
  have hX : Real.log ((1 + WeightAlgebra.DF w : ℕ) : ℝ) ≤ 2 * large₂.sc.L := by
    rw [Nat.cast_add, Nat.cast_one]; exact hp.2.2.2.2.2.2.2.1
  have h := log_le_of_le_pow_mul_pow (by linarith) (by linarith) hP (hp.1 0) (hp.1 1) hO.1 hX hN
  have hs := frn_le_size_sub_one w
  have hf : 0 < D.R.f := by
    have := D.R.two_le_m
    have := D.R.m_le_f
    unfold Ranks.f Ranks.n
    omega
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hm : (1 : ℝ) ≤ ((D.R.f * D.R.r * w.n : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos hf hr) hn
  generalize ((D.R.f * D.R.r * w.n : ℕ) : ℝ) = m at h hs hm
  generalize w.size - 1 = s at hs ⊢
  have hs0 : 0 ≤ s := by linarith
  calc Real.log N ≤ m * (2 * (9 * large₂.sc.L + 1) + 2 * large₂.sc.L) + PO D large₂ := h
    _ ≤ s * (38 * large₂.sc.L) + PO D large₂ * s := by
      have a1 : m * (2 * (9 * large₂.sc.L + 1) + 2 * large₂.sc.L) ≤ s * (38 * large₂.sc.L) :=
        mul_le_mul hs (by linarith) (by linarith) hs0
      have a2 : PO D large₂ ≤ PO D large₂ * s := le_mul_of_one_le_right hP (hm.trans hs)
      linarith
    _ = (38 * large₂.sc.L + PO D large₂) * s := by ring
    _ ≤ Prw * s := mul_le_mul_of_nonneg_right hPrw hs0

end GlobalTheory.RunIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PageRowsOfLe
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory

theorem pageRows_of_le : ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (ka w : WeightFamilies.Wt D j), 0 ≤ large₂.sc.L → WeightAlgebra.DF w ≤ WeightAlgebra.DF ka → w.n ≤ ka.n → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w := by
  intro D large₂ j ka w hL hd hn h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, ?_⟩
  · refine le_trans (Real.log_le_log (by positivity) ?_) h8
    have : ((WeightAlgebra.DF w : ℕ) : ℝ) ≤ ((WeightAlgebra.DF ka : ℕ) : ℝ) := by exact_mod_cast hd
    linarith
  · rcases Nat.eq_zero_or_pos w.n with h0 | h0
    · rw [h0]; simpa using hL
    · exact le_trans (Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hn)) h9

end GlobalTheory
end

