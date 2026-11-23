module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0233
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0967
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PsiCondAll
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0389
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFockIntertwinerAdjointExchangedPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EvalAtJetMap
section
open GlobalTheory.KJInf Formalism.L2.Forms Formalism.BasicNotions MvPolynomial

noncomputable section
namespace GlobalTheory.KJInf.ClsVal
variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem evalAt_jetLin (y' : ι → Matrix (Fin b) (Fin b) ℂ) (Λ : FP ι a b →ₗ[ℂ] ℂ)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) ℂ) :
    evalAt y' (Formalism.L2.Ker.jetLin (fun m => Λ (monomial m 1)) Q) =
      Λ (aeval (Sum.elim (fun x : ι × Fin b × Fin b => (C (y' x.1 x.2.1 x.2.2) : FP ι a b)) X) Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial m c =>
    have hm : (monomial m c : MvPolynomial ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) ℂ) = c • monomial m 1 := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    have h1 : Formalism.L2.Ker.jetLin (fun m => Λ (monomial m 1)) (monomial m c) =
        c • monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
          (Λ (monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) 1)) := by
      rw [hm, map_smul]
      congr 1
      unfold Formalism.L2.Ker.jetLin
      have := (basisMonomials ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) ℂ).constr_basis ℂ
        (fun m : ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) →₀ ℕ => (monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
          (Λ (monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) 1)) : MvPolynomial (ι × Fin b × Fin b) ℂ)) m
      simpa using this
    rw [h1, evalAt, smul_eval, eval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (by simp),
      Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
    have h2 : (∏ i : ι × Fin b × Fin a, (X i : FP ι a b) ^ m (Sum.inr i)) =
        monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
      rfl
    simp only [Sum.elim_inl, Sum.elim_inr, h2, ← map_pow, ← map_prod, algebraMap_eq]
    rw [show ∀ (u v : ℂ) (q : FP ι a b), C u * (C v * q) = (u * v) • q from fun u v q => by rw [smul_eq_C_mul, C_mul, mul_assoc], map_smul, smul_eq_mul]
    simp only [Finsupp.comapDomain_apply]
    ring
  | add p q hp hq => rw [map_add (f := _), evalAt, map_add (f := _), ← evalAt, ← evalAt, hp, hq, map_add (f := _), map_add (f := _)]

theorem evalAt_jetMap (hab : a ≤ b) (y' : ι → Matrix (Fin b) (Fin b) ℂ) (Λ : FP ι a b →ₗ[ℂ] ℂ) (k : ι → ℕ) (P : PY ι a) :
    evalAt y' (Formalism.L2.Ker.jetMap (fun m => Λ (monomial m 1)) k P) =
      Λ (subY hab y' (P * ∏ τ, Formalism.L2.Ker.frDet ℂ a τ ^ k τ)) := by
  rw [subY_eq_subD]
  exact evalAt_jetLin y' Λ _

theorem cSpan_eq_VV' {m : ℕ} (lam : ι → DomWeight m) : CSpan lam = Formalism.L2.DIV.VV ℂ lam := by
  unfold CSpan Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, Formalism.L2.Col.nablaSq_eq_delSq]
  rfl

end GlobalTheory.KJInf.ClsVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicUnitaryConjSelfDualMajorantLevels
section
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EisCont.LevelConj

section Glue

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)


omit [NumberField E] in
theorem exists_proj_eq (x : ∀ v, GLoc σ J v) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ g : GAd σ J, (∀ v ∈ S, proj σ J v g = x v) ∧ (∀ v ∉ S, proj σ J v g = 1) ∧ ∀ w, projArch σ J w g = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, fun v _ => map_one _, fun w => map_one _⟩
  | insert u S hu ih =>
    obtain ⟨g, h1, h2, h3⟩ := ih
    refine ⟨emb σ J u (x u) * g, fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩
    · rw [map_mul]
      by_cases e : v = u
      · subst e
        rw [proj_emb_self, h2 v hu, mul_one]
      · rw [proj_emb_ne σ J e, one_mul, h1 v ((Finset.mem_insert.1 hv).resolve_left e)]
    · rw [Finset.mem_insert, not_or] at hv
      rw [map_mul, proj_emb_ne σ J hv.1, one_mul, h2 v hv.2]
    · rw [map_mul, projArch_emb, one_mul, h3]


omit [NumberField E] in
theorem exists_projArch_eq (x : ∀ w, GArch σ J w) (S : Finset (InfinitePlace F)) :
    ∃ g : GAd σ J, (∀ w ∈ S, projArch σ J w g = x w) ∧ (∀ w ∉ S, projArch σ J w g = 1) ∧ ∀ v, proj σ J v g = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, fun v _ => map_one _, fun w => map_one _⟩
  | insert u S hu ih =>
    obtain ⟨g, h1, h2, h3⟩ := ih
    refine ⟨embArch σ J u (x u) * g, fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩
    · rw [map_mul]
      by_cases e : v = u
      · subst e
        rw [projArch_embArch_self, h2 v hu, mul_one]
      · rw [projArch_embArch_ne σ J e, one_mul, h1 v ((Finset.mem_insert.1 hv).resolve_left e)]
    · rw [Finset.mem_insert, not_or] at hv
      rw [map_mul, projArch_embArch_ne σ J hv.1, one_mul, h2 v hv.2]
    · rw [map_mul, proj_embArch, one_mul, h3]

private theorem eventually_latLoc_eq_std_of_selfDual {L : Submodule (𝓞 E) (Fin n → E)}
    (hJ : J.det ≠ 0) (hL : Submodule.IsLattice E L) (hdual : ∀ v, IsSelfDualAt σ J L v) :
    ∀ᶠ v in cofinite, latLoc F L v = latLoc F (stdLattice E n) v := by
  have hstd : Submodule.IsFullLattice E (stdLattice E n) := isLattice_stdLattice
  filter_upwards [eventually_latLoc_le (F := F) hL.fg hstd.span_eq_top,
    AdelicU.SelfDual.eventually_isSelfDualAt (σ := σ) hJ hstd] with v hle hv
  apply le_antisymm hle
  intro y hy
  rw [hdual v]
  rw [hv] at hy
  exact fun x hx => hy x (hle hx)

omit [NumberField E] in
theorem exists_conj_of_local {L L' : Submodule (𝓞 E) (Fin n → E)}
    (hlat : ∀ᶠ v in cofinite, latLoc F L v = latLoc F L' v)
    (a a' : GL (Fin n) (AF F ⊗[F] E))
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ g : GLoc σ J v, ∀ k : GLoc σ J v,
      k ∈ stabLoc σ J L' v ↔ g⁻¹ * k * g ∈ stabLoc σ J L v)
    (hi : ∀ w : InfinitePlace F, ∃ g : GArch σ J w, ∀ k : GArch σ J w,
      k ∈ stabArch σ J w (Formalism.UG.bc (compInf F E w) a') ↔
        g⁻¹ * k * g ∈ stabArch σ J w (Formalism.UG.bc (compInf F E w) a)) :
    ∃ g : GAd σ J, ∀ k : GAd σ J, k ∈ levelAll σ J L' a' ↔ g⁻¹ * k * g ∈ levelAll σ J L a := by
  choose x hx using hf
  choose y hy using hi
  have hS := Filter.eventually_cofinite.1 hlat
  obtain ⟨g, g1, g2, g3⟩ := exists_proj_eq σ J x hS.toFinset
  obtain ⟨h, h1, -, h3⟩ := exists_projArch_eq σ J y Finset.univ
  refine ⟨g * h, fun k => ?_⟩
  rw [mem_levelAll, mem_levelAll]
  refine and_congr (forall_congr' fun v => ?_) (forall_congr' fun w => ?_)
  · rw [map_mul, map_mul, map_inv, map_mul, h3, mul_one]
    by_cases hv : v ∈ hS.toFinset
    · rw [g1 v hv]
      exact hx v _
    · have e : latLoc F L v = latLoc F L' v := by simpa using hv
      rw [g2 v hv, inv_one, one_mul, mul_one, mem_stabLoc, mem_stabLoc, e]
  · rw [map_mul, map_mul, map_inv, map_mul, g3, one_mul, h1 w (Finset.mem_univ w)]
    exact hy w _

end Glue

theorem exists_conj : ∀ (D : D7) (T : HSp D) (L L' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (a a' : GL (Fin T.rank) (AE D)), IsLevel T L a → IsLevel T L' a' → ∃ g : GA D T, ∀ k : GA D T, k ∈ lev T L' a' ↔ g⁻¹ * k * g ∈ lev T L a := by
  intro D T L L' a a' h h'
  have hc := isCMExt_host D
  have hJ := isHermND_gram T
  have hf := fun v => GlobalTheory.T.exists_conj_stabilizers_selfDual_lattices_unramified D.host.F D.host.E D.sp.cm.sig hc (GlobalTheory.HeckeAdjoint.unramified_host D) T.rank T.gram
    hJ L L' h.lat h'.lat v (h.dual v) (h'.dual v)
  have hi := fun w => _root_.GlobalTheory.MajorantConj.stabArch_conj D.host.F D.host.E D.sp.cm.sig hc T.rank T.gram hJ a a' h.maj h'.maj w
  have hlat : ∀ᶠ v in cofinite, latLoc D.host.F L v = latLoc D.host.F L' v := by
    filter_upwards [eventually_latLoc_eq_std_of_selfDual D.sp.cm.sig T.gram hJ.2 h.lat h.dual,
      eventually_latLoc_eq_std_of_selfDual D.sp.cm.sig T.gram hJ.2 h'.lat h'.dual] with v hv hv'
    exact hv.trans hv'.symm
  obtain ⟨g, hg⟩ := exists_conj_of_local D.sp.cm.sig T.gram hlat a a' hf hi
  exact ⟨g, fun k => hg k⟩

end GlobalTheory.EisCont.LevelConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdditiveCharNeOneAtEachPrime
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FiniteCharNontrivial

theorem trace_eq_tau (I : AutInst) (x : I.E) :
    Algebra.trace ℚ I.E x = Algebra.trace ℚ I.F (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed x) := by
  have h1 : Algebra.trace ℚ I.E (star x) = Algebra.trace ℚ I.E x :=
    Algebra.trace_eq_of_algEquiv ((starRingAut : I.E ≃+* I.E).equivRatAlgEquiv _ _) x
  have h2 : Algebra.trace ℚ I.E (algebraMap I.F I.E (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed x)) =
      2 * Algebra.trace ℚ I.F (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed x) := by
    rw [← Algebra.trace_trace (S := I.F), Algebra.trace_algebraMap, I.cm.deg2, map_nsmul, nsmul_eq_mul]
    norm_num
  rw [PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply, map_add (f := _), h1] at h2
  linarith

theorem exists_away {E : Type} [Field E] [NumberField E] (g : 𝓞 E) (hg : g ≠ 0)
    (Q : HeightOneSpectrum (𝓞 E)) :
    ∃ j : 𝓞 E, j ∉ Q.asIdeal ∧ ∀ Q' : HeightOneSpectrum (𝓞 E), g ∈ Q'.asIdeal → Q' ≠ Q → j ∈ Q'.asIdeal := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 E) | v.asIdeal ∣ Ideal.span {g}}.Finite :=
    Ideal.finite_factors (by simpa using hg)
  have hch : ∀ v : HeightOneSpectrum (𝓞 E), ∃ a : 𝓞 E, a ∉ Q.asIdeal ∧ (v ≠ Q → a ∈ v.asIdeal) := by
    intro v
    by_cases hv : v = Q
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 Q.isPrime.ne_top, fun h => (h hv).elim⟩
    · have hn : ¬ v.asIdeal ≤ Q.asIdeal := fun hle =>
        hv (HeightOneSpectrum.ext (v.isMaximal.eq_of_le Q.isPrime.ne_top hle))
      obtain ⟨a, ha, ha'⟩ := SetLike.not_le_iff_exists.1 hn
      exact ⟨a, ha', fun _ => ha⟩
  choose a ha ha' using hch
  refine ⟨∏ v ∈ hfin.toFinset, a v, ?_, ?_⟩
  · have := Q.isPrime
    intro h
    obtain ⟨v, -, hv⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact ha v hv
  · intro Q' hQ' hne
    have hm : Q' ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
      exact hQ'
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem a hm) (ha' Q' hne)

theorem core (I : AutInst) (psiEf : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F → ℂ)
    (hrat : ∀ x : I.E, psiEf (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) * psiEinf I x = 1)
    (g : ℕ) (hg : g ≠ 0) (Q : HeightOneSpectrum (𝓞 I.E)) (hgQ : ((g : ℕ) : 𝓞 I.E) ∈ Q.asIdeal)
    (hun : Algebra.IsUnramifiedAt ℤ Q.asIdeal) (j : 𝓞 I.E) (hj : j ∉ Q.asIdeal) :
    ∃ z : 𝓞 I.E, psiEf (divN I g (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)
      (algebraMap (𝓞 I.E) I.E (j * z)))) ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hgE : (g : I.E) ≠ 0 := Nat.cast_ne_zero.2 hg
  have htr : ∀ z : 𝓞 I.E, ∃ n : ℤ, Algebra.trace ℚ I.E
      ((g : I.E)⁻¹ * algebraMap (𝓞 I.E) I.E j * algebraMap (𝓞 I.E) I.E z) = n := by
    intro z
    have e : divN I g (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (algebraMap (𝓞 I.E) I.E (j * z))) =
        Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)
          ((g : I.E)⁻¹ * algebraMap (𝓞 I.E) I.E j * algebraMap (𝓞 I.E) I.E z) := by
      have e1 : algebraMap I.F (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) ((g : I.F)⁻¹) =
          Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) ((g : I.E)⁻¹) := by
        rw [Algebra.TensorProduct.algebraMap_apply, map_inv₀, map_natCast]
        rfl
      rw [divN, e1, ← RingHom.map_mul, RingHom.map_mul (algebraMap (𝓞 I.E) I.E), mul_assoc]
    have h1 := hcon z
    rw [e] at h1
    have h2 := hrat ((g : I.E)⁻¹ * algebraMap (𝓞 I.E) I.E j * algebraMap (𝓞 I.E) I.E z)
    rw [h1, one_mul] at h2
    rw [trace_eq_tau]
    exact PsiCondAllPf.trace_of_psi I _ h2
  obtain ⟨d, hd, hdQ⟩ := PsiCondAllPf.exists_diff_not_mem Q hun
  obtain ⟨c, hc⟩ := PsiCondAllPf.mul_diff_int _ htr d hd
  have hcg : (g : 𝓞 I.E) * c = j * d := by
    apply RingOfIntegers.coe_injective
    rw [RingHom.map_mul, RingHom.map_mul, hc, map_natCast]
    field_simp
  have hm : j * d ∈ Q.asIdeal := hcg ▸ Ideal.mul_mem_right _ _ hgQ
  rcases Q.isPrime.mem_or_mem hm with h | h
  exacts [hj h, hdQ h]

theorem exists_psi_ne_one : ∀ (D : D7) (psiEf : (instOf D).E ⊗[(instOf D).F] Formalism.MainNotions.S.Af (instOf D).F → ℂ), (∀ x y, psiEf (x + y) = psiEf x * psiEf y) → (∀ x ∈ IntAf (instOf D).F (instOf D).E, psiEf x = 1) → (∀ x : (instOf D).E, psiEf (Formalism.UG.inclE (F := (instOf D).F) (Formalism.MainNotions.S.Af (instOf D).F) x) * psiEinf (instOf D) x = 1) → ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ Q' : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q'.asIdeal → Q' ≠ Q → resS D.host.F Q' s = 0) ∧ psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1) ≠ 1 := by
  intro D psiEf _ _ hrat Q hQ
  have hg : D.host.g 0 * D.host.g 1 ≠ 0 := mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := by
    have hQ' := hQ
    rw [Nat.cast_mul] at hQ'
    rcases Q.isPrime.mem_or_mem hQ' with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]
  have hun : Algebra.IsUnramifiedAt ℤ Q.asIdeal :=
    PsiCondAllPf.unram_of (D.host.g i) (D.host.g_prime i) Q hi
      (Formalism.L2.SG.Pf.TypedLoc.tower_ef D.host.E D.host.E (D.host.g_prime i) (D.nd.g_split i) Q hi).1
  obtain ⟨j, hj, hj'⟩ := exists_away ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) (Nat.cast_ne_zero.2 hg) Q
  obtain ⟨z, hz⟩ := core (instOf D) psiEf hrat _ hg Q hQ hun j hj
  let z' : 𝓞 D.host.E := z
  refine ⟨oToS D.host.F D.host.E (j * z'), fun Q' h1 h2 => ?_, hz⟩
  rw [resS_oToS, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ (hj' Q' h1 h2)

end GlobalTheory.FiniteCharNontrivial
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralAdelePrescribedResiduesAndConj
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ConjResidueSurj
open GlobalTheory.IdemSupport

theorem sigInt_oToS {D : D7} (a : 𝓞 D.host.E) :
    sigInt (instOf D) (oToS D.host.F D.host.E a) = oToS D.host.F D.host.E (cO D a) :=
  Subtype.ext (Formalism.L2.SG.Pf.unitaryCongruence.sigA_inclE (instOf D) (a : D.host.E))

theorem exists_res_and_conj (D : D7) (Pg : Finset (Pl D.host.E))
    (h : ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP')
    (u u' : ∀ PP : Pl D.host.E, kP PP) :
    ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ PP ∈ Pg,
      resS D.host.F PP s = u PP ∧ resS D.host.F PP (sigInt (instOf D) s) = u' PP := by
  classical
  choose a ha using fun PP : Pl D.host.E => Ideal.Quotient.mk_surjective (I := PP.asIdeal) (u PP)
  choose a' ha' using fun PP : Pl D.host.E => Ideal.Quotient.mk_surjective (I := PP.asIdeal) (u' PP)
  have hout : ∀ PP ∈ Pg, cP PP ∉ Pg := fun PP hPP h' =>
    h PP hPP _ h' ((isConjPl_iff _ _).2 rfl)
  let T : Finset (Pl D.host.E) := Pg ∪ Pg.image cP
  let x : Pl D.host.E → 𝓞 D.host.E := fun Q => if Q ∈ Pg then a Q else cO D (a' (cP Q))
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun Q : Pl D.host.E => Q.asIdeal) (fun _ => 1) (fun Q _ => Q.prime)
    (fun Q _ Q' _ hne e => hne (HeightOneSpectrum.ext e)) (fun Q => x Q.1)
  refine ⟨oToS D.host.F D.host.E y, fun PP hPP => ⟨?_, ?_⟩⟩
  · have h1 := hy PP (Finset.mem_union_left _ hPP)
    rw [pow_one] at h1
    have h2 : x PP = a PP := if_pos hPP
    rw [resS_oToS, ← ha PP, ← h2]
    exact Ideal.Quotient.eq.2 h1
  · have h1 := hy (cP PP) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hPP))
    rw [pow_one] at h1
    have h2 : x (cP PP) = cO D (a' PP) := by
      have : x (cP PP) = cO D (a' (cP (cP PP))) := if_neg (hout PP hPP)
      rw [this, GlobalTheory.StdFrames.cP_cP]
    have h3 : y - cO D (a' PP) ∈ (cP PP).asIdeal := h2 ▸ h1
    rw [mem_cP, map_sub, cO_cO] at h3
    rw [sigInt_oToS, resS_oToS, ← ha' PP]
    exact Ideal.Quotient.eq.2 h3

end GlobalTheory.ConjResidueSurj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealThetaIntertwinerExchangedPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt

theorem itPairUp : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (k : Fin D.R.m) (V W : HSp D)
    (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ),
    S = parB (Ptw D) k → S' = parB (Ptw D) (k + 1) → IsInfFam θ → ChainPar D k →
    ∃ It : PolF D V.rank W.rank →ₗ[ℂ] SmT M →ₗ[ℂ] SmT M', ∀ (ω : (GA D W × GA D V →* Module.End ℂ (WO W V → ℂ)))
      (f : WO W V → ℂ), IsWeilExp ψ W V (expT D k) (expS D k) ω → IsVacVec ψ θ M' M f →
        IsItW θ M' M ω (ptOf ψ θ M' M f) It := by
  intro hDS hHC D k V W S S' M M' θ ψ hS hS' hθ hP
  subst hS hS'
  obtain ⟨X, hX, h1, h2, -⟩ := _root_.GlobalTheory.RealPlaceTheta.exists_record_theta_all hDS hHC
  have hB := _root_.GlobalTheory.CoverModel.modelsAreCoverSeries_all hDS hHC D
  have key : ∀ τ, (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ (expS D k τ) (expT D k τ) A := fun τ => by
    obtain ⟨al, be, ga, de, hd, -, e1, e2⟩ := hP τ
    exact exists_locIt hX h1 h2 hB M M' τ hd (congrArg dualPar e1) (congrArg dualPar e2)
  choose hr A hA using key
  have hA' : ∀ τ, ∃ A', LocIt M' M τ (expT D k τ) (expS D k τ) A' := fun τ =>
    _root_.GlobalTheory.AdjLocIt.adj_locIt D V W _ _ M M' τ _ _ (A τ) (hA τ)
  choose A' hA' using hA'
  obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D W V _ _ M' M (expT D k) (expS D k) A' GlobalTheory.ContrObj.contraction.2
    (_root_.GlobalTheory.Chain.RealIt.GlueProof.glueLaw D _ _) hA'
  refine ⟨It, fun ω f ⟨χS, χT, hω, he⟩ hf => ?_⟩
  have hv := fun τ => _root_.GlobalTheory.VacuumCharacter.vacChar D W V _ _ M' M θ ψ χS χT ω f τ _ _ hθ hω (he τ).1 (he τ).2 hf
  exact isItW_of_globIt hθ hI (fun τ => ⟨(hr τ).2, (hr τ).1⟩)
    (_root_.GlobalTheory.VacuumFockLaws.vacuumFock_onObjects D W V _ _ M' M ψ θ hω.std hθ f hf).2.2.2.2 (fun τ => (hv τ).2.1) fun τ => (hv τ).2.2

end GlobalTheory.Chain.RealIt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroTargetTensorRowProductStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendByZero_target_tensor_row_product : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ → ∀ (Ψ : Matrix n' n k → ℂ) (b : (n → k) → ℂ), extFun β α₀ (tensRow Ψ b) = o.boxT T (extFun β α Ψ) (GlobalTheory.FinPl.ExtZero.rowFun β ζ b) := by
  exact @GlobalTheory.FinPl.ExtZero.extFun_tensRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabiliserFinitePlace
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
namespace GlobalTheory.Core.Rk.IwFin

theorem iwasawa_fin : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r), (∀ v : FinPl D, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) → ∀ (v : FinPl D) (y : Gv T v), ∃ q k : Gv T v, emb D.sp.cm.sig T.gram v q ∈ stab d ∧ k ∈ stabLoc D.sp.cm.sig T.gram (frameLat T) v ∧ y = q * k := by
  intro D T T₀ r d _h2 v y
  by_cases hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v
  · exact GlobalTheory.T.iwasawa_isotropic_stabiliser_split_place D T T₀ r d v hv y
  · exact GlobalTheory.T.iwasawa_isotropicStabilizer_inertPlace D T T₀ r d v hv y

end GlobalTheory.Core.Rk.IwFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePrimesProductNotMemSqPlace
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePrimeUnif

theorem mul_not_mem_sq {R : Type*} [CommRing R] [IsDedekindDomain R] (Q : HeightOneSpectrum R) {a b : R}
    (hab : IsCoprime a b) (ha : a ∈ Q.asIdeal → a ∉ Q.asIdeal ^ 2) (hb : b ∈ Q.asIdeal → b ∉ Q.asIdeal ^ 2) :
    a * b ∉ Q.asIdeal ^ 2 := by
  intro h
  have := Q.isPrime
  have hle : Q.asIdeal ^ 2 ≤ Q.asIdeal := Ideal.pow_le_self two_ne_zero
  rcases Ideal.IsPrime.mul_mem_pow Q.asIdeal h with h1 | h1
  · rcases Ideal.IsPrime.mul_mem_pow Q.asIdeal (mul_comm a b ▸ h) with h2 | h2
    · obtain ⟨u, v, huv⟩ := hab
      exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (huv ▸ Q.asIdeal.add_mem (Q.asIdeal.mul_mem_left u h1) (Q.asIdeal.mul_mem_left v h2)))
    · exact ha h1 h2
  · exact hb (hle h1) h1

theorem prod_not_mem_sq : ∀ (D : D7) (Q : Pl D.host.E), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal ^ 2 := by
  intro D Q _
  have key : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal →
      ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal ^ 2 := fun k hk =>
    (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) Q hk).2.1
  have hc : Nat.Coprime (D.host.g 0) (D.host.g 1) :=
    (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne
  rw [Nat.cast_mul]
  exact mul_not_mem_sq Q (Nat.Coprime.cast hc) (key 0) (key 1)

end GlobalTheory.TypePrimeUnif
end

