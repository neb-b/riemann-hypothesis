module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
public import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0172
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1305
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormSolutionFields
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.NormAssemble

open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

theorem cT_aeval {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (p : K[X]) :
    cT σ (aeval M p) = aeval (cT σ M) (p.map σ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), Polynomial.map_add (f := _), map_add (f := _), ← hp, ← hq]
    ext i j; simp [cT]
  | monomial k a =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mul_assoc, one_mul]
    have hp : ((M ^ k).map σ)ᵀ = ((M.map σ)ᵀ) ^ k := by
      rw [← Matrix.transpose_pow, ← RingHom.mapMatrix_apply, map_pow, RingHom.mapMatrix_apply]
    simp only [cT, Matrix.map_smul', hp]
    ext i j; simp [Matrix.transpose_smul]
    left; rw [← hp]; rfl

def toFld {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Q : SelfRecip E r) : E[X] →+* Fld Q :=
  AdjoinRoot.mk Q.1

def sr {E : Type} [Field E] [NumberField E] [IsCMField E] (Q : E[X]) (h : IsSelfRecip E Q.natDegree Q) :
    SelfRecip E Q.natDegree := ⟨Q, h⟩

theorem exists_norm_of_factors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → (∀ Q : E[X], Q.Monic → Irreducible Q → Q ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.IsSelfRecip E Q.natDegree Q) → ∀ m : E[X], (∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → ∃ y : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, y * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q y = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q)) → ∃ c : Matrix (Fin n) (Fin n) E, c * γ.val = γ.val * c ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom c * c = aeval γ.val m := by
  intro E _ _ _ n γ hγ hP hself m hy
  set σ : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom with hσ
  set P := γ.val.charpoly with hPdef
  have hPsep : P.Separable := hP.2.2.1
  have hP0 : P ≠ 0 := hP.1.ne_zero
  have hXP : IsCoprime X P := by
    rw [Polynomial.irreducible_X.coprime_iff_not_dvd]
    intro hX
    exact (hself X monic_X irreducible_X hX).2.2.2.1 (by simp)
  obtain ⟨a, b, hab⟩ := hXP
  have hCH : aeval γ.val P = 0 := Matrix.aeval_self_charpoly _
  have haγ : aeval γ.val a * γ.val = 1 := by
    have := congrArg (aeval γ.val) hab
    simpa [hCH] using this
  have hu : cT σ γ.val * γ.val = 1 := by
    have : cT σ γ.val * 1 * γ.val = 1 := hγ
    simpa using this
  have h1 : γ.val * (γ⁻¹).val = 1 := Units.mul_inv γ
  have hcTa : cT σ γ.val = aeval γ.val a := by
    calc cT σ γ.val = cT σ γ.val * γ.val * (γ⁻¹).val := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
      _ = aeval γ.val a * γ.val * (γ⁻¹).val := by rw [hu, haγ]
      _ = aeval γ.val a := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  set S := (UniqueFactorizationMonoid.normalizedFactors P).toFinset with hS
  have hmem : ∀ Q ∈ S, Q.Monic ∧ Irreducible Q ∧ Q ∣ P := by
    intro Q hQ
    rw [hS, Multiset.mem_toFinset] at hQ
    have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor Q hQ
    refine ⟨?_, hirr, UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQ⟩
    have hn := UniqueFactorizationMonoid.normalize_normalized_factor Q hQ
    rw [← hn]; exact Polynomial.monic_normalize hirr.ne_zero
  have hcopS : (S : Set E[X]).Pairwise (Function.onFun IsCoprime fun Q : E[X] => Q) := by
    intro Q hQ Q' hQ' hne
    simp only [Function.onFun]
    rw [(hmem Q hQ).2.1.coprime_iff_not_dvd]
    intro hd
    exact hne (eq_of_monic_of_associated (hmem Q hQ).1 (hmem Q' hQ').1
      ((hmem Q hQ).2.1.associated_of_dvd (hmem Q' hQ').2.1 hd))
  have hsr : ∀ Q : S, IsSelfRecip E Q.1.natDegree Q.1 := fun Q =>
    hself Q.1 (hmem Q.1 Q.2).1 (hmem Q.1 Q.2).2.1 (hmem Q.1 Q.2).2.2
  have hloc : ∀ Q : S, ∃ fQ : E[X], toFld (sr Q.1 (hsr Q)) fQ *
      invol (sr Q.1 (hsr Q)) (toFld _ fQ) = toFld _ m := by
    intro Q
    obtain ⟨y, hy'⟩ := hy _ (sr Q.1 (hsr Q)) (hmem Q.1 Q.2).2.2
    obtain ⟨fQ, rfl⟩ := AdjoinRoot.mk_surjective y
    exact ⟨fQ, hy'⟩
  choose fQ hfQ using hloc
  have hcop : Pairwise (Function.onFun IsCoprime fun Q : S => Ideal.span {Q.1}) := by
    intro Q Q' hne
    simp only [Function.onFun]
    rw [Ideal.isCoprime_span_singleton_iff]
    exact hcopS Q.2 Q'.2 (fun h => hne (Subtype.ext h))
  obtain ⟨q, hq⟩ := Ideal.quotientInfToPiQuotient_surj hcop
    (fun Q => Ideal.Quotient.mk (Ideal.span {Q.1}) (fQ Q))
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hf : ∀ Q : S, AdjoinRoot.mk Q.1 f = AdjoinRoot.mk Q.1 (fQ Q) := by
    intro Q
    have := congrFun hq Q
    rw [Ideal.quotientInfToPiQuotient_mk] at this
    exact this
  set g := (f.map σ).comp a * f - m with hg
  have hdiv : ∀ Q ∈ S, Q ∣ g := by
    intro Q hQ
    let Q' : SelfRecip E Q.natDegree := sr Q (hsr ⟨Q, hQ⟩)
    have hQP := (hmem Q hQ).2.2
    have ha : toFld Q' a = (alpha Q')⁻¹ := by
      have := congrArg (toFld Q') hab
      rw [map_add (f := _), map_mul, map_mul, map_one] at this
      have hX : toFld Q' X = alpha Q' := AdjoinRoot.mk_X
      have hPz : toFld Q' P = 0 := AdjoinRoot.mk_eq_zero.2 hQP
      rw [hX, hPz, mul_zero, add_zero] at this
      exact eq_inv_of_mul_eq_one_left this
    have hc : toFld Q' ((f.map σ).comp a) = invol Q' (toFld Q' f) := by
      change AdjoinRoot.mk Q'.1 ((f.map σ).comp a) = AdjoinRoot.lift _ _ (eval₂_conj_inv_root Q') (AdjoinRoot.mk Q'.1 f)
      rw [← AdjoinRoot.aeval_eq, aeval_comp, AdjoinRoot.aeval_eq, AdjoinRoot.lift_mk, aeval_def, eval₂_map]
      change eval₂ _ (toFld Q' a) f = _
      rw [ha]; rfl
    have hfQ' : toFld Q' (fQ ⟨Q, hQ⟩) * invol Q' (toFld Q' (fQ ⟨Q, hQ⟩)) = toFld Q' m := hfQ ⟨Q, hQ⟩
    have hf' : toFld Q' f = toFld Q' (fQ ⟨Q, hQ⟩) := hf ⟨Q, hQ⟩
    have : toFld Q' g = 0 := by
      rw [hg, map_sub, map_mul, hc, hf', mul_comm, hfQ', sub_self]
    exact AdjoinRoot.mk_eq_zero.1 this
  have hprod : (∏ Q ∈ S, Q) ∣ g := Finset.prod_dvd_of_coprime hcopS hdiv
  have hassoc : Associated (∏ Q ∈ S, Q) P := by
    have hnd := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP0).1 hPsep.squarefree
    rw [Finset.prod_eq_multiset_prod, hS, Multiset.toFinset_val, hnd.dedup, Multiset.map_id']
    exact UniqueFactorizationMonoid.prod_normalizedFactors hP0
  have hPg : P ∣ g := hassoc.symm.dvd.trans hprod
  obtain ⟨k, hk⟩ := hPg
  have hg0 : aeval γ.val g = 0 := by rw [hk, map_mul, hCH, zero_mul]
  refine ⟨aeval γ.val f, ?_, ?_⟩
  · rw [show γ.val * aeval γ.val f = aeval γ.val (X * f) by simp,
      show aeval γ.val f * γ.val = aeval γ.val (f * X) by simp, mul_comm]
  · rw [cT_aeval, hcTa, ← aeval_comp, ← map_mul]
    rw [hg, map_sub] at hg0
    exact sub_eq_zero.1 hg0

end GlobalTheory.NormAssemble
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOddPrimeGtTwoBounds
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.AlgCharUnr

theorem phase_prod_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] {q : ℕ} (hq : q.Prime) (hq2 : 2 < q)
    (ht : ¬ q ∣ Nat.card (Units.torsion E)) (u : (𝓞 E)ˣ) (hu : (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)})
    (m : InfinitePlace E → ℤ) (w0 : ℤ) (hm : ∀ w, ∃ a, m w = 2 * a - w0) :
    ∏ w : InfinitePlace E, (w.embedding ((u : 𝓞 E) : E) / ((‖w.embedding ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) ^ m w = 1 := by
  have hr := _root_.GlobalTheory.UnitReal.unit_real_of_congr_one E q hq ht u hu
  have hs := GlobalTheory.T.prod_arg_real_unit_eq_one' E q hq hq2 u hu hr
  have hsq : ∀ w : InfinitePlace E,
      (w.embedding ((u : 𝓞 E) : E) / ((‖w.embedding ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) ^ m w =
      ((w.embedding ((u : 𝓞 E) : E) / ((‖w.embedding ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) ^ w0)⁻¹ := fun w => by
    set z := w.embedding ((u : 𝓞 E) : E) with hz
    have h0 : z ≠ 0 := by rw [hz, map_ne_zero]; exact Units.coe_ne_zero u
    have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
    have hzr : starRingEnd ℂ z = z := hr _
    have h2 : (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 : ℤ) = 1 := by
      rw [zpow_two, div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hn hn)]
      have e : ((‖z‖ : ℝ) : ℂ) * ((‖z‖ : ℝ) : ℂ) = z * starRingEnd ℂ z := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
      rw [e, hzr]
    obtain ⟨a, ha⟩ := hm w
    have hne : z / ((‖z‖ : ℝ) : ℂ) ≠ 0 := div_ne_zero h0 hn
    rw [ha, sub_eq_add_neg, zpow_add₀ hne, zpow_mul, h2, one_zpow, one_mul, zpow_neg]
  rw [Finset.prod_congr rfl fun w _ => hsq w, Finset.prod_inv_distrib, Finset.prod_zpow, hs, one_zpow, inv_one]

theorem exists_odd_prime_gt_two_bounds (l t : ℕ) : ∃ q : ℕ, q.Prime ∧ 2 < q ∧ l < q ∧ t < q := by
  obtain ⟨q, hq, hp⟩ := Nat.exists_infinite_primes (max (max 3 (l + 1)) (t + 1))
  exact ⟨q, hp, by omega, by omega, by omega⟩

theorem exists_algChar_unr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ), l.Prime → ∀ (n : (E →+* ℂ) → ℤ) (w0 : ℤ), (∀ φ, n φ + n (NumberField.ComplexEmbedding.conjugate φ) = w0) → ∃ χ : HChar E, IsAlgPos χ n ∧ ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → χ.UnrAt w := by
  intro E _ _ _ l hl n w0 hn
  classical
  obtain ⟨q, hq, hq2, hlq, htq⟩ := exists_odd_prime_gt_two_bounds l (Nat.card (Units.torsion E))
  have ht : ¬ q ∣ Nat.card (Units.torsion E) := fun h =>
    absurd (Nat.le_of_dvd Nat.card_pos h) (by omega)
  set 𝔪 : Ideal (𝓞 E) := Ideal.span {((q : ℕ) : 𝓞 E)} with h𝔪
  have hq0 : ((q : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  have hm : 𝔪 ≠ ⊥ := by rw [h𝔪, Ne, Ideal.span_singleton_eq_bot]; exact hq0
  let m : InfinitePlace E → ℤ := fun w => 2 * n w.embedding - w0
  have hbij : Function.Bijective fun w : InfinitePlace E => InfinitePlace.mk w.embedding := by
    simp only [InfinitePlace.mk_embedding]
    exact Function.bijective_id
  obtain ⟨ψ, hψ, hψu, hψi, -, hψS, hψd⟩ := GlobalTheory.ModelChar.exists_modelChar E (InfinitePlace E) (fun w => w.embedding)
    hbij m ∅ (fun _ => 1) (by simp)
  have hinf := (GlobalTheory.InfTypeLocal.infType_iff_local E (InfinitePlace E) (fun w => w.embedding) hbij ψ hψ _).2 hψi
  let U : Subgroup (Neutral.B1.Ideles E) := GlobalTheory.Mem.Chr.unitIdl E ⊓ GlobalTheory.RayChar.congrIdl 𝔪
  have hU : IsOpen (U : Set (Neutral.B1.Ideles E)) :=
    GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.inter (GlobalTheory.RayChar.isOpen_congrIdl hm)
  have hmem : ∀ k : Eˣ, infDiag k ∈ U := fun k => by
    refine ⟨?_, (GlobalTheory.RayChar.mem_congrIdl hm).2 fun v _ => ?_⟩
    · unfold infDiag
      rw [MonoidHom.finsetProd_apply]
      exact Subgroup.prod_mem _ fun w _ => GlobalTheory.Mem.Chr.AntiExist.inf_mem w _
    · have h1 : GlobalTheory.RayChar.cmp (infDiag k) v = 1 :=
        congrArg Units.val (GlobalTheory.ModelChar.finEv_infDiag v k)
      rw [h1, sub_self, map_zero]
      exact zero_le
  obtain ⟨χ1, hχc, -, hχU, hχd⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (Neutral.B1.Ideles E) Eˣ U hU
    (Neutral.B1.diagUnits E) 1 ψ hψ hψu (fun _ => by simp) (fun k hk => by
      obtain ⟨u, hu⟩ := GlobalTheory.DefU.NonTriv.exists_unit k hk.1
      have hu1 : (u : 𝓞 E) - 1 ∈ 𝔪 := (GlobalTheory.RayChar.mem_iff_at hm _).2 fun v hv => by
        rw [GlobalTheory.RayChar.at'_sub_one]
        have h2 := (GlobalTheory.RayChar.mem_congrIdl hm).1 hk.2 v hv
        rw [GlobalTheory.RayChar.cmp_diag, ← hu] at h2
        exact h2
      show (1 : ℂˣ) = ψ (Neutral.B1.diagUnits E k)
      rw [hψd, Finset.prod_empty, mul_one]
      refine (Units.ext ?_).symm
      rw [hinf k, Units.val_one, ← hu]
      exact phase_prod_eq_one hq hq2 ht u hu1 m w0 fun w => ⟨n w.embedding, rfl⟩)
  let χ0 : HChar E := ⟨χ1, hχc, fun k => by rw [hχd]; rfl⟩
  let s : ℝ := (w0 : ℝ) / 2
  let ν : HChar E := GlobalTheory.Mem.Chr.CharModel.absChar E (s : ℂ)
  have hν : ν.IsAbsPow s := GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow s
  refine ⟨χ0 * ν, fun k _ => ?_, fun w hw x hx => ?_⟩
  · have h1 : ((χ0.inf k : ℂˣ) : ℂ) = ∏ w : InfinitePlace E, (w.embedding (k : E) / ((‖w.embedding (k : E)‖ : ℝ) : ℂ)) ^ m w := by
      show ((χ1 (infDiag k) : ℂˣ) : ℂ) = _
      rw [hχU _ (hmem k)]
      exact hinf k
    rw [HChar.inf_mul, Units.val_mul, h1, hν.2.2 k]
    exact _root_.GlobalTheory.Div.CMAlgChar.algChar_eq_arg_mul_abs E n w0 hn (k : E) k.ne_zero
  · have hwq : ¬ w.asIdeal ∣ 𝔪 := by
      rw [h𝔪, Ideal.dvd_span_singleton]
      intro hqw
      have hc : IsCoprime ((l : ℕ) : 𝓞 E) ((q : ℕ) : 𝓞 E) :=
        Nat.Coprime.cast ((Nat.coprime_primes hl hq).2 hlq.ne)
      obtain ⟨a, b, hab⟩ := hc
      apply w.isPrime.ne_top
      rw [Ideal.eq_top_iff_one, ← hab]
      exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hw) (w.asIdeal.mul_mem_left _ hqw)
    change χ0.loc w x * ν.loc w x = 1
    rw [hν.1 w x hx, mul_one]
    show χ1 (Neutral.B1.localIdele E w x) = 1
    rw [hχU _ ⟨GlobalTheory.RayChar.local_mem_unitIdl hx, GlobalTheory.RayChar.local_mem_congrIdl hwq x⟩]
    exact hψS w (Finset.notMem_empty w) x

end GlobalTheory.AlgCharUnr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenIdeleSubgroupCongruenceModQ
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.OpenCongrIdele

theorem exists_open_congr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsCMField E] (q : ℕ), q ≠ 0 → ∃ U : Subgroup (AF F ⊗[F] E)ˣ, IsOpen (U : Set (AF F ⊗[F] E)ˣ) ∧ (∀ z : (AF F ⊗[F] E)ˣ, At (evI F) ((z : AF F ⊗[F] E) - 1) → z ∈ U) ∧ ∀ k : Eˣ, Units.map (incAF F E).toMonoidHom k ∈ U → ∃ u : (𝓞 E)ˣ, ((u : 𝓞 E) : E) = k ∧ (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} := by
  intro F E _ _ _ _ _ _ q hq
  obtain ⟨Θ, hc, hΘ⟩ := GlobalTheory.CharTransport.exists_toAdele F E
  set 𝔪 : Ideal (𝓞 E) := Ideal.span {((q : ℕ) : 𝓞 E)} with h𝔪
  have hm : 𝔪 ≠ ⊥ := by
    rw [h𝔪, Ne, Ideal.span_singleton_eq_bot]; exact Nat.cast_ne_zero.2 hq
  let V : Subgroup (Neutral.B1.Ideles E) := GlobalTheory.Mem.Chr.unitIdl E ⊓ GlobalTheory.RayChar.congrIdl 𝔪
  let φ : (AF F ⊗[F] E)ˣ →* Neutral.B1.Ideles E := Units.map Θ.toMonoidHom
  refine ⟨V.comap φ, ?_, fun z hz => ?_, fun k hk => ?_⟩
  · exact (GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.inter (GlobalTheory.RayChar.isOpen_congrIdl hm)).preimage
      (Continuous.units_map _ hc)
  · have hfin : (Θ (z : AF F ⊗[F] E)).2 = 1 := by
      let a : AF F := pairA F 0 1
      have ha : evI F a = 0 := by
        show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
        exact map_zero _
      have h0 : a • ((z : AF F ⊗[F] E) - 1) = 0 := hz a ha
      have h1 : Θ (a • ((z : AF F ⊗[F] E) - 1)) =
          GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a * Θ ((z : AF F ⊗[F] E) - 1) := by
        rw [Algebra.smul_def, map_mul]
        congr 1
        change Θ (a ⊗ₜ[F] (1 : E)) = _
        rw [hΘ, map_one, mul_one]
      have h2 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a).2 = 1 := map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E)
      have h3 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a * Θ ((z : AF F ⊗[F] E) - 1)).2 = 0 := by
        rw [← h1, h0, map_zero]; rfl
      have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a).2 * (Θ ((z : AF F ⊗[F] E) - 1)).2 = 0 := h3
      rw [h2, one_mul, map_sub, map_one] at h4
      exact sub_eq_zero.1 h4
    have hv : ∀ v : HeightOneSpectrum (𝓞 E), GlobalTheory.RayChar.cmp (φ z) v = 1 := fun v => by
      show (Θ (z : AF F ⊗[F] E)).2 v = 1
      rw [hfin]; rfl
    refine ⟨fun v => ?_, (GlobalTheory.RayChar.mem_congrIdl hm).2 fun v _ => ?_⟩
    · show Valued.v (GlobalTheory.RayChar.cmp (φ z) v) = 1
      rw [hv v, map_one]
    · rw [hv v, sub_self, map_zero]; exact zero_le'
  · have he : φ (Units.map (incAF F E).toMonoidHom k) = Neutral.B1.diagUnits E k := Units.ext (by
      change Θ ((1 : AF F) ⊗ₜ[F] (k : E)) = _
      rw [hΘ, map_one, one_mul]; rfl)
    have hk' : Neutral.B1.diagUnits E k ∈ V := by rw [← he]; exact hk
    obtain ⟨u, hu⟩ := GlobalTheory.DefU.NonTriv.exists_unit k hk'.1
    refine ⟨u, hu, (GlobalTheory.RayChar.mem_iff_at hm _).2 fun v hv => ?_⟩
    rw [GlobalTheory.RayChar.at'_sub_one]
    have h2 := (GlobalTheory.RayChar.mem_congrIdl hm).1 hk'.2 v hv
    rw [GlobalTheory.RayChar.cmp_diag, ← hu] at h2
    exact h2

end GlobalTheory.OpenCongrIdele
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthonormalBasisDefiniteHermitianSpace
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteFrame

theorem exists_unitary_frame : ∀ (D : D7) (V : HSp D), V.SigOK → (∀ τ, V.sig τ = (V.rank, 0)) →
    ∃ fr : GL (Fin V.rank) D.host.E, Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 := by
  intro D V hs hp
  obtain ⟨b, hli, horth⟩ := GlobalTheory.DefiniteOrthonormal.landherrHasse D V hs hp
  have hsp : Submodule.span D.host.E (Set.range b) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli]
    simp [V.rank_eq]
  let B : Module.Basis (Fin V.rank) D.host.E V.V := Module.Basis.mk hli (by rw [hsp])
  have hB : ∀ a, B a = b a := fun a => by simp [B]
  let M : Matrix (Fin V.rank) (Fin V.rank) D.host.E := V.frame.toMatrix B
  let M' : Matrix (Fin V.rank) (Fin V.rank) D.host.E := B.toMatrix V.frame
  let fr : GL (Fin V.rank) D.host.E :=
    ⟨M, M', Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩
  refine ⟨fr, ?_⟩
  ext a c
  have key : V.hT (b a) (b c) = ∑ i, ∑ j, star (M i a) * V.gram i j * M j c := by
    rw [← hB a, ← hB c]
    conv_lhs => rw [← V.frame.sum_repr (B a), ← V.frame.sum_repr (B c)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, Finset.mul_sum, M, Module.Basis.toMatrix_apply, Formalism.BasicNotions.HSpace.gram]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [RingHom.id_apply]
    ring
  have lhs : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1) a c
      = ∑ i, ∑ j, star (M i a) * V.gram i j * M j c := by
    simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    rfl
  rw [lhs, ← key, horth, Matrix.one_apply]

end GlobalTheory.DefiniteFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPairingCoordinatesSchrodingerFolland
section
open scoped SchwartzMap Matrix

open scoped RealInnerProductSpace
noncomputable section
namespace GlobalTheory.ArchUniq
open GlobalTheory.RealWeil
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def leftForm {P : V → V → ℝ} (hP : IsPairing P) (b : V) : V →ₗ[ℝ] ℝ where
  toFun x := P x b
  map_add' x x' := hP.addL x x' b
  map_smul' c x := hP.smulL c x b

theorem pair_expand {n : ℕ} (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) {P : V → V → ℝ} (hP : IsPairing P) (y b : V) :
    P y b = ∑ i, C y i * P (C.symm (EuclideanSpace.single i 1)) b := by
  have hy : y = ∑ i, C y i • C.symm (EuclideanSpace.single i 1) := by
    conv_lhs => rw [← C.symm_apply_apply y, ← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (C y)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  have e : P y b = leftForm hP b y := rfl
  rw [e]
  conv_lhs => rw [hy]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp [leftForm, hP.smulL]

def pairCoordsL {n : ℕ} (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) {P : V → V → ℝ} (hP : IsPairing P) :
    V × V →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) where
  toFun v := Sum.elim (fun i => C v.1 i) (fun i => -P (C.symm (EuclideanSpace.single i 1)) v.2)
  map_add' v v' := by
    funext j
    rcases j with i | i <;> simp [hP.addR]; ring
  map_smul' c v := by
    funext j
    rcases j with i | i <;> simp [hP.smulR]

theorem pairCoordsL_injective {n : ℕ} (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) {P : V → V → ℝ} (hP : IsPairing P) :
    Function.Injective (pairCoordsL C hP) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨a, b⟩ h
  have ha : a = 0 := by
    apply C.injective
    ext i
    simpa [pairCoordsL] using congrFun h (Sum.inl i)
  have hb : b = 0 := by
    apply hP.nondegR
    intro x
    rw [pair_expand C hP]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := congrFun h (Sum.inr i)
    simp [pairCoordsL] at this
    simp [this]
  simp [ha, hb]

theorem exists_pairing_coords : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : V → V → ℝ), GlobalTheory.ArchUniq.IsPairing P → ∀ n : ℕ, Module.finrank ℝ V = n →
    ∃ (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v v', GlobalTheory.RealWeil.sympl (φ v) (φ v') = -GlobalTheory.ArchUniq.omega P v v') ∧
      ∀ v (f : EuclideanSpace ℝ (Fin n) → ℂ),
        GlobalTheory.ArchUniq.schrF P v (f ∘ C) = GlobalTheory.RealWeil.rhoFun (φ v) f ∘ C := by
  intro V _ _ _ P hP n hn
  let C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (hn.trans (finrank_euclideanSpace_fin).symm)
  have hdim : Module.finrank ℝ (V × V) = Module.finrank ℝ (Fin n ⊕ Fin n → ℝ) := by
    simp [Module.finrank_prod, hn]
  let φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) :=
    LinearMap.linearEquivOfInjective (pairCoordsL C hP) (pairCoordsL_injective C hP) hdim
  have hφ : ∀ v, φ v = pairCoordsL C hP v := fun v => rfl
  have hp : ∀ v : V × V, pPart (φ v) = C v.1 := by
    intro v; ext i; simp [hφ, pPart, pairCoordsL]
  have hq : ∀ (v : V × V) (x : EuclideanSpace ℝ (Fin n)),
      ⟪qPart (φ v), x⟫ = -∑ i, P (C.symm (EuclideanSpace.single i 1)) v.2 * x i := by
    intro v x
    simp [hφ, qPart, pairCoordsL, PiLp.inner_apply, mul_comm]
  have hq' : ∀ (v : V × V) (y : V), ⟪qPart (φ v), C y⟫ = -P y v.2 := by
    intro v y
    rw [hq, pair_expand C hP y v.2]
    simp [mul_comm]
  have hCq : ∀ (v : V × V) (y : V), ⟪C y, qPart (φ v)⟫ = -P y v.2 := by
    intro v y
    rw [real_inner_comm, hq']
  refine ⟨C, φ, ?_, ?_⟩
  · intro v v'
    simp only [sympl, omega, hp, hCq, hq']
    ring
  · intro v f
    funext y
    simp only [schrF, rhoFun, phase, Function.comp_apply, map_add (f := _), hp, hq', hCq]
    congr 1
    congr 1
    push_cast
    ring
end GlobalTheory.ArchUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertIntegralTwistedConjugatesTwistedCentralizerStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_integral_twistedConjugates_twistedCentralizer_mul_maxCompact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), ¬ IsSplitAt w →
    ∀ y g : GLw n w, y ∈ GlobalTheory.LFun.KGL w (n := n) →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w y).val.charpoly + v * derivative (nrmL n w y).val.charpoly = 1) →
    g⁻¹ * y * thL n w g ∈ GlobalTheory.LFun.KGL w (n := n) → ∃ t ∈ twCent (thL n w) y, ∃ k ∈ GlobalTheory.LFun.KGL w (n := n), g = t * k := by
  first | exact @GlobalTheory.InertUniq.eq_twCent_mul_KGL | exact GlobalTheory.InertUniq.eq_twCent_mul_KGL | (intros; apply GlobalTheory.InertUniq.eq_twCent_mul_KGL <;> assumption)
end

