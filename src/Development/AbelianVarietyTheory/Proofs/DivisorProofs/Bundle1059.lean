module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryPointOfLocalFamily
section
noncomputable section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.LocGlue

theorem entry_mem {E : Type} [Field E] [NumberField E] {n : ℕ} {v : HeightOneSpectrum (𝓞 E)}
    {g : GL (Fin n) (v.adicCompletion E)} (hg : g ∈ GlobalTheory.LFun.KGL v (n := n)) (i j : Fin n) :
    g.val i j ∈ v.adicCompletionIntegers E ∧ (g⁻¹ : GL (Fin n) (v.adicCompletion E)).val i j ∈ v.adicCompletionIntegers E := by
  obtain ⟨g0, rfl⟩ := hg
  refine ⟨(g0.val i j).2, ?_⟩
  rw [← map_inv]
  exact ((g0⁻¹).val i j).2

theorem glue : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (g : ∀ v : HeightOneSpectrum (𝓞 E), GL (Fin n) (v.adicCompletion E)), (∀ᶠ v in cofinite, g v ∈ GlobalTheory.LFun.KGL v (n := n)) → ∃ k : GL (Fin n) (Af E), ∀ v, GeneralLinearGroup.map (pLoc E v) k = g v := by
  intro E _ _ n g hg
  have hent : ∀ i j, ∀ᶠ v in cofinite, (g v).val i j ∈ v.adicCompletionIntegers E ∧
      ((g v)⁻¹ : GL (Fin n) (v.adicCompletion E)).val i j ∈ v.adicCompletionIntegers E :=
    fun i j => hg.mono fun v hv => entry_mem hv i j
  let M : Matrix (Fin n) (Fin n) (Af E) := fun i j => ⟨fun v => (g v).val i j, (hent i j).mono fun v h => h.1⟩
  let N : Matrix (Fin n) (Fin n) (Af E) := fun i j =>
    ⟨fun v => ((g v)⁻¹ : GL (Fin n) (v.adicCompletion E)).val i j, (hent i j).mono fun v h => h.2⟩
  have hM : ∀ v, RingHom.mapMatrix (pLoc E v) M = (g v).val := fun v => rfl
  have hN : ∀ v, RingHom.mapMatrix (pLoc E v) N = ((g v)⁻¹ : GL (Fin n) (v.adicCompletion E)).val := fun v => rfl
  have hMN : M * N = 1 := GlobalTheory.SplitPts.matAf_ext fun v => by
    rw [map_mul, map_one, hM, hN, Units.mul_inv]
  have hNM : N * M = 1 := GlobalTheory.SplitPts.matAf_ext fun v => by
    rw [map_mul, map_one, hM, hN, Units.inv_mul]
  exact ⟨⟨M, N, hMN, hNM⟩, fun v => Units.ext (hM v)⟩

theorem intst : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (v u : HeightOneSpectrum (𝓞 E)) (f : v.adicCompletion E →+* u.adicCompletion E), (∀ x, Valued.v (f x) = Valued.v x) → ∀ g ∈ GlobalTheory.LFun.KGL v (n := n), invT n _ (GeneralLinearGroup.map f g) ∈ GlobalTheory.LFun.KGL u (n := n) := by
  intro E _ _ n v u f hf g hg
  obtain ⟨g0, rfl⟩ := hg
  let r : Formalism.UG.Ov E v →+* Formalism.UG.Ov E u := f.restrict _ _ fun x hx => by
    change _ ∈ u.adicCompletionIntegers E
    change x ∈ v.adicCompletionIntegers E at hx
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
    rw [hf]
    exact hx
  refine ⟨invT n _ (GeneralLinearGroup.map r g0), ?_⟩
  apply Units.ext
  ext i j
  rfl

theorem ns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Y : ∀ v : HeightOneSpectrum (𝓞 E), GL (Fin n) (v.adicCompletion E)) (u : HeightOneSpectrum (𝓞 E)), ¬ IsSplitAt u → GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) u) (Y (conjSrc (GlobalTheory.SplitPts.conjE E) u)) = GeneralLinearGroup.map (cj u) (Y u) := by
  intro E _ _ _ n Y u hu
  have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (_ : v = u) (f : v.adicCompletion E →+* u.adicCompletion E), Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k)) →
      GeneralLinearGroup.map f (Y v) = GeneralLinearGroup.map (cj u) (Y u) := by
    rintro v rfl f hf hext
    have hex : ∃ s : v.adicCompletion E →+* v.adicCompletion E, Continuous s ∧
        ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨f, hf, hext⟩
    have hcj : cj v = hex.choose := by unfold cj; rw [dite_eq_left hex]
    have hfs : (f : v.adicCompletion E → v.adicCompletion E) = hex.choose :=
      (HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf hex.choose_spec.1
        (funext fun k => (hext k).trans (hex.choose_spec.2 k).symm)
    rw [hcj]
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact congrFun hfs ((Y v).val i j)
  have hcu : conjSrc (GlobalTheory.SplitPts.conjE E) u = u := by
    by_contra h
    exact hu ⟨_, h, (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u _).2
      (Or.inr (GlobalTheory.SplitPts.conjPl_self_conjSrc u))⟩
  exact key _ hcu _ (conjLoc_spec _ u).1 (conjLoc_spec _ u).2.1

theorem twice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Y : ∀ v : HeightOneSpectrum (𝓞 E), GL (Fin n) (v.adicCompletion E)) (u : HeightOneSpectrum (𝓞 E)), GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) u) (GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) (conjSrc (GlobalTheory.SplitPts.conjE E) u)) (Y (conjSrc (GlobalTheory.SplitPts.conjE E) (conjSrc (GlobalTheory.SplitPts.conjE E) u)))) = Y u := by
  intro E _ _ _ n Y u
  have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (_ : v = u) (f : v.adicCompletion E →+* u.adicCompletion E), Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ k) → GeneralLinearGroup.map f (Y v) = Y u := by
    rintro v rfl f hf hext
    have hfs : (f : v.adicCompletion E → v.adicCompletion E) = id :=
      (HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf continuous_id (funext fun k => hext k)
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact congrFun hfs ((Y v).val i j)
  have h := key _ (GlobalTheory.SplitPts.conjSrc_conjSrc_cm u)
    ((conjLoc (GlobalTheory.SplitPts.conjE E) u).comp (conjLoc (GlobalTheory.SplitPts.conjE E) (conjSrc (GlobalTheory.SplitPts.conjE E) u)))
    ((conjLoc_spec _ u).1.comp (conjLoc_spec _ _).1) fun k => by
      rw [RingHom.comp_apply, (conjLoc_spec _ _).2.1, (conjLoc_spec _ _).2.1]
      exact congrArg _ (IsCMField.complexConj_apply_apply E k)
  rw [← h]
  rfl

end GlobalTheory.BCT.LocGlue

theorem GlobalTheory.BCT.exists_finU_of_loc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E), IsSection S → ∀ y : ∀ w : Pl E, UL n w, (∀ᶠ w in cofinite, y w ∈ KL n w) → ∃ x : finU (E := E) (n := n), ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) = y w := by
  intro E _ _ _ _ n S hS y hy
  set c := GlobalTheory.SplitPts.conjE E with hc
  have hnotS : ∀ v, v ∉ S → conjSrc c v ∈ S := by
    intro v hv
    obtain ⟨s, ⟨hsS, hsv⟩, -⟩ := hS v
    have hne : v ≠ s := fun e => hv (e ▸ hsS)
    have hsp : IsSplitAt s := ⟨v, hne, hsv.symm⟩
    obtain ⟨-, -, hover⟩ := GlobalTheory.SplitPts.over_split hsp
    rcases hover v hsv.symm with h | h
    · exact absurd h hne
    · rw [h, GlobalTheory.SplitPts.conjSrc_conjSrc_cm]; exact hsS
  have hSsplit : ∀ v ∈ S, IsSplitAt v → conjSrc c v ∉ S := by
    intro v hv hsp h
    obtain ⟨hne, hund, -⟩ := GlobalTheory.SplitPts.over_split hsp
    exact hne ((hS v).unique ⟨h, hund⟩ ⟨hv, rfl⟩)
  let z : ∀ v : Pl E, GLw n v := fun v => if v ∈ S then (y v).1 else
    invT n _ (GeneralLinearGroup.map (conjLoc c v) (y (conjSrc c v)).1)
  have hz_in : ∀ v ∈ S, z v = (y v).1 := fun v hv => if_pos hv
  have hz_out : ∀ v, v ∉ S → z v = invT n _ (GeneralLinearGroup.map (conjLoc c v) (y (conjSrc c v)).1) :=
    fun v hv => if_neg hv
  have hint : ∀ᶠ v in cofinite, z v ∈ GlobalTheory.LFun.KGL v (n := n) := by
    have h1 : ∀ᶠ v in cofinite, (y v).1 ∈ GlobalTheory.LFun.KGL v (n := n) := hy.mono fun v hv => Subgroup.mem_subgroupOf.1 hv
    have h2 := (conjSrc_injective c).tendsto_cofinite.eventually h1
    filter_upwards [h1, h2] with v a1 a2
    by_cases hv : v ∈ S
    · rw [hz_in v hv]; exact a1
    · rw [hz_out v hv]; exact GlobalTheory.BCT.LocGlue.intst E n _ v (conjLoc c v) (conjLoc_spec c v).2.2 _ a2
  obtain ⟨k, hk⟩ := GlobalTheory.BCT.LocGlue.glue E n z hint
  have hk' : ∀ u, ((GeneralLinearGroup.map (pLoc E (conjSrc c u)) k).val.map (conjLoc c u))ᵀ *
      (GeneralLinearGroup.map (pLoc E u) k).val = 1 := by
    intro u
    rw [hk, hk]
    show ((GeneralLinearGroup.map (conjLoc c u) (z (conjSrc c u))).val)ᵀ * (z u).val = 1
    by_cases hu : u ∈ S
    · by_cases hsp : IsSplitAt u
      · rw [hz_out _ (hSsplit u hu hsp), hz_in u hu, GlobalTheory.SplitPts.invT_map,
          GlobalTheory.BCT.LocGlue.twice E n (fun v => (y v).1) u]
        change ((((y u).1)⁻¹ : GLw n u).val)ᵀᵀ * (y u).1.val = 1
        rw [Matrix.transpose_transpose, Units.inv_mul]
      · have hcu : conjSrc c u = u := by
          by_contra h
          exact hsp ⟨_, h, (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
            (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u _).2
            (Or.inr (GlobalTheory.SplitPts.conjPl_self_conjSrc u))⟩
        rw [hz_in _ (by rw [hcu]; exact hu), hz_in u hu, GlobalTheory.BCT.LocGlue.ns E n (fun v => (y v).1) u hsp]
        have key : ∀ g : GLw n u, g ∈ UL n u → g ∈ UJ (cj u) 1 := by
          intro g hg
          unfold UL at hg
          rwa [if_neg hsp] at hg
        have hUL : (y u).1 ∈ UJ (cj u) 1 := key _ (y u).2
        have h3 : cT (cj u) (y u).1.val * 1 * (y u).1.val = 1 := hUL
        rw [Matrix.mul_one] at h3
        exact h3
    · rw [hz_out u hu, hz_in _ (hnotS u hu)]
      change ((GeneralLinearGroup.map (conjLoc c u) (y (conjSrc c u)).1).val)ᵀ *
        (((GeneralLinearGroup.map (conjLoc c u) (y (conjSrc c u)).1)⁻¹ : GLw n u).val)ᵀ = 1
      rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  let x : finU (E := E) (n := n) := ⟨⟨finGL E n k, GlobalTheory.SplitPts.finGL_mem_UA k hk'⟩, MonoidHom.mem_ker.2 (pInf_finGL k)⟩
  refine ⟨x, fun w hw => ?_⟩
  show toSub (UL n w) (cLoc w ⟨finGL E n k, GlobalTheory.SplitPts.finGL_mem_UA k hk'⟩) = y w
  rw [GlobalTheory.SplitPts.cLoc_finGL, hk, hz_in w hw]
  unfold toSub
  rw [dite_eq_left (y w).2]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDimStablePolyAveragesWeights
section
noncomputable section

open MeasureTheory MvPolynomial
open Formalism.REAL (KG toMK muK)
open GlobalTheory.PsCo.Pc1
open ReciprocityTheory.ChartRestriction.DS (IsURepOn UJset)

namespace GlobalTheory.PsCo.PolyAvg

variable {n : ℕ}

theorem totalDegree_bind_le {α β : Type} (g : α → MvPolynomial β ℂ) (hg : ∀ i, (g i).totalDegree ≤ 1)
    (Q : MvPolynomial α ℂ) : (bind₁ g Q).totalDegree ≤ Q.totalDegree := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [Q.as_sum, map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hs)
  refine (Finset.sum_le_sum fun i _ => (totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left _ (hg i))).trans ?_
  simp [Finsupp.sum]

theorem exists_translate (a : Mat n) (P : Poly n) :
    ∃ Q : Poly n, Q.totalDegree ≤ P.totalDegree ∧ ∀ g, ev (a * g) P = ev g Q := by
  let f : (Fin n × Fin n) ⊕ (Fin n × Fin n) → Poly n := Sum.elim
    (fun x => ∑ c, C (a x.1 c) * X (Sum.inl (c, x.2))) (fun x => ∑ c, C (star (a x.1 c)) * X (Sum.inr (c, x.2)))
  refine ⟨bind₁ f P, totalDegree_bind_le f ?_ P, fun g => ?_⟩
  · rintro (x | x) <;>
    · refine totalDegree_finsetSum_le fun l _ => (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X, totalDegree_C]
  · have h : ev (a * g) = (ev g).comp (bind₁ f : Poly n →ₐ[ℂ] Poly n).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) ?_
      · simp [ev]
      · rintro (x | x) <;> simp [ev, f, Matrix.mul_apply]
    rw [h]; rfl

def varWt : (Fin n × Fin n) ⊕ (Fin n × Fin n) → Fin n → ℝ :=
  Sum.elim (fun x => -Pi.single x.1 1) (fun x => Pi.single x.1 1)

def monWt (s : (Fin n × Fin n) ⊕ (Fin n × Fin n) →₀ ℕ) : Fin n → ℝ := fun a => ∑ i, (s i : ℝ) * varWt i a

theorem ev_diag_monomial (θ : Fin n → ℝ) (g : Mat n) (s : (Fin n × Fin n) ⊕ (Fin n × Fin n) →₀ ℕ) :
    ev (Matrix.diagonal (fun a => Complex.exp (-((θ a : ℂ) * Complex.I))) * g) (monomial s 1) =
      Complex.exp (((∑ a, monWt s a * θ a : ℝ) : ℂ) * Complex.I) * ev g (monomial s 1) := by
  have h1 : (∑ a, monWt s a * θ a : ℝ) = ∑ i, (s i : ℝ) * ∑ a, varWt i a * θ a := by
    simp only [monWt, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  rw [h1]
  simp only [ev, eval_monomial, one_mul]
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Complex.ofReal_sum, Finset.sum_mul,
    Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc, Complex.exp_nat_mul, ← mul_pow]
  congr 1
  rcases i with x | x
  · simp [varWt, Pi.single_apply, ite_mul]
  · simp [varWt, Pi.single_apply, ite_mul, ← Complex.exp_conj]

theorem continuous_toMK (ε : Fin n → Bool) : Continuous fun k : KG ε => toMK k :=
  (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.continuous.comp continuous_subtype_val

theorem continuous_ev (P : Poly n) : Continuous fun g : Mat n => ev g P := by
  refine (MvPolynomial.continuous_eval P).comp (continuous_pi ?_)
  rintro (x | x)
  · simp only [Sum.elim_inl]; fun_prop
  · simp only [Sum.elim_inr]; fun_prop

theorem toMK_mem (ε : Fin n → Bool) (k : KG ε) : toMK k ∈ UJset ε := (k : Formalism.REAL.UJ ε).2

theorem toMK_mul (ε : Fin n → Bool) (a b : KG ε) : toMK (a * b) = toMK a * toMK b := rfl

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Mat n → (H →L[ℂ] H)}

omit [CompleteSpace H] in
theorem integrable_avg (hσ : IsURepOn (UJset ε) σ) (u : H) (P : Poly n) :
    Integrable (fun k : KG ε => ev (toMK k) P • σ (toMK k) u) (muK ε) := by
  have h : Continuous fun k : KG ε => ev (toMK k) P • σ (toMK k) u :=
    ((continuous_ev P).comp (continuous_toMK ε)).smul
      ((hσ.2.2 u).comp_continuous (continuous_toMK ε) (toMK_mem ε))
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def avg (hσ : IsURepOn (UJset ε) σ) (u : H) : Poly n →ₗ[ℂ] H where
  toFun P := ∫ k : KG ε, ev (toMK k) P • σ (toMK k) u ∂(muK ε)
  map_add' P Q := by
    rw [← integral_add (integrable_avg hσ u P) (integrable_avg hσ u Q)]
    simp only [map_add (f := _), add_smul]
  map_smul' c P := by
    rw [RingHom.id_apply, ← integral_smul]
    simp [ev, smul_eq_C_mul, mul_smul]

theorem apply_avg (hσ : IsURepOn (UJset ε) σ) (u : H) (P : Poly n) (g : KG ε) :
    σ (toMK g) (avg hσ u P) = ∫ k : KG ε, ev (toMK g⁻¹ * toMK k) P • σ (toMK k) u ∂(muK ε) := by
  change σ (toMK g) (∫ k : KG ε, ev (toMK k) P • σ (toMK k) u ∂(muK ε)) = _
  rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_avg hσ u P),
    ← integral_mul_left_eq_self (fun k : KG ε => ev (toMK g⁻¹ * toMK k) P • σ (toMK k) u) g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only
  rw [← toMK_mul, inv_mul_cancel_left, toMK_mul, hσ.1.2 _ (toMK_mem ε g) _ (toMK_mem ε k), map_smul]
  rfl

theorem isWtOn_avg (hσ : IsURepOn (UJset ε) σ) (u : H) (s : (Fin n × Fin n) ⊕ (Fin n × Fin n) →₀ ℕ) :
    Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ (monWt s) (avg hσ u (monomial s 1)) := by
  intro θ hθ
  rw [← Formalism.REAL.range_toMK] at hθ
  obtain ⟨g, hg⟩ := hθ
  simp only at hg
  have hinv : toMK g⁻¹ = Matrix.diagonal (fun a => Complex.exp (-((θ a : ℂ) * Complex.I))) := by
    have h1 : toMK g * Matrix.diagonal (fun a => Complex.exp (-((θ a : ℂ) * Complex.I))) = 1 := by
      rw [hg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have h2 : toMK g⁻¹ * toMK g = 1 := by rw [← toMK_mul, inv_mul_cancel]; rfl
    rw [← Matrix.mul_one (toMK g⁻¹), ← h1, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [← hg, apply_avg, hinv]
  simp only [ev_diag_monomial, mul_smul]
  rw [integral_smul]
  rfl

theorem polyAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ), ∃ A : Set (Fin n → ℝ), A.Finite ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.UJset ε) σ → ∀ u : H, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Formalism.MainNotions.S.IsKStableOn ε σ S ∧ (∀ P : GlobalTheory.PsCo.Pc1.Poly n, P.totalDegree ≤ d → ∫ k : Formalism.REAL.KG ε, GlobalTheory.PsCo.Pc1.ev (Formalism.REAL.toMK k) P • σ (Formalism.REAL.toMK k) u ∂(Formalism.REAL.muK ε) ∈ S) ∧ ∀ (μ : Fin n → ℝ) (s : H), s ∈ S → s ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ s → μ ∈ A := by
  intro n ε d
  refine ⟨monWt '' {s | s.degree ≤ d}, (Finsupp.finite_of_degree_le d).image _, ?_⟩
  intro H _ _ _ σ hσ u
  refine ⟨(restrictTotalDegree _ ℂ d).map (avg hσ u), inferInstance, ?_, ?_, ?_⟩
  · rintro g hg v ⟨P, hP, rfl⟩
    rw [← Formalism.REAL.range_toMK] at hg
    obtain ⟨g, rfl⟩ := hg
    obtain ⟨Q, hQ, hQ'⟩ := exists_translate (toMK g⁻¹) P
    refine ⟨Q, (mem_restrictTotalDegree _ _ _).2 (hQ.trans ((mem_restrictTotalDegree _ _ _).1 hP)), ?_⟩
    simp only
    rw [apply_avg]
    simp only [hQ']
    rfl
  · intro P hP
    exact ⟨P, (mem_restrictTotalDegree _ _ _).2 hP, rfl⟩
  · rintro μ v ⟨P, hP, rfl⟩ hv hw
    by_contra hμ
    apply hv
    have hP' : P.totalDegree ≤ d := (mem_restrictTotalDegree _ _ _).1 hP
    rw [← inner_self_eq_zero (𝕜 := ℂ)]
    have e : avg hσ u P = ∑ s ∈ P.support, AddMonoidAlgebra.coeff P s • avg hσ u (monomial s 1) := by
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [P.as_sum, map_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]
    generalize avg hσ u P = v at e hw
    have : inner ℂ v (∑ s ∈ P.support, AddMonoidAlgebra.coeff P s • avg hσ u (monomial s 1)) = 0 := by
      rw [inner_sum]
      refine Finset.sum_eq_zero fun s hs => ?_
      rw [inner_smul_right, ReciprocityTheory.ChartRestriction.DS.kfin_wt_orth hσ hw (isWtOn_avg hσ u s), mul_zero]
      rintro rfl
      exact hμ ⟨s, (le_totalDegree hs).trans hP', rfl⟩
    rwa [← e] at this

end GlobalTheory.PsCo.PolyAvg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLCompletionLatticeEqColumns
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.TwLat

theorem exists_GLw_lat_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ L : Submodule K.O B.A, GlobalTheory.UnitLemma.IsLat K.O K.E L → ∃ g : GLw m w, GlobalTheory.TwLat.lat e b g = L := by
  intro E _ _ _ _ w _ K e _ _ _ B m b L hL
  obtain ⟨hfg, hsp⟩ := hL
  haveI : Module.Finite K.O L := Module.Finite.iff_fg.mpr hfg
  haveI : NoZeroSMulDivisors K.O B.A := by
    constructor
    intro c x h
    rw [← algebraMap_smul K.E c x, smul_eq_zero] at h
    rcases h with h | h
    · left; exact (IsFractionRing.injective K.O K.E) (by simpa using h)
    · right; exact h
  haveI : Module.Free K.O L := Module.free_of_finite_type_torsion_free'
  set n := Module.finrank K.O L
  let bL := Module.finBasis K.O L
  let v : Fin n → B.A := fun i => (bL i : B.A)
  have hspanO : Submodule.span K.O (Set.range v) = L := by
    have : Set.range v = L.subtype '' Set.range bL := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, bL.span_eq, Submodule.map_subtype_top]
  have hli : LinearIndependent K.E v := by
    rw [← LinearIndependent.iff_fractionRing K.O K.E]
    exact LinearIndependent.map' bL.linearIndependent L.subtype (by simp)
  have hspE : ⊤ ≤ Submodule.span K.E (Set.range v) := by
    rw [← Submodule.span_span_of_tower K.O K.E (Set.range v), hspanO, hsp]
  let bE := Module.Basis.mk hli hspE
  have hnm : n = m := by
    have h1 := Module.finrank_eq_card_basis bE
    have h2 := Module.finrank_eq_card_basis b
    simp only [Fintype.card_fin] at h1 h2
    omega
  let v' : Fin m → B.A := v ∘ finCongr hnm.symm
  let bE' := bE.reindex (finCongr hnm)
  have hv' : ∀ j, bE' j = v' j := by
    intro j; simp [bE', v', bE, Module.Basis.mk_apply]
  let M : Matrix (Fin m) (Fin m) K.E := b.toMatrix bE'
  have hM : IsUnit M := by
    haveI := b.invertibleToMatrix bE'
    exact isUnit_of_invertible M
  have hMe : IsUnit (M.map e) := hM.map e.mapMatrix
  refine ⟨hMe.unit, ?_⟩
  unfold lat
  rw [← hspanO]
  have hcol : (fun j => ∑ i, e.symm ((hMe.unit : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) • b i) = v' := by
    funext j
    simp only [IsUnit.unit_spec, Matrix.map_apply, RingEquiv.symm_apply_apply, M, Module.Basis.toMatrix_apply]
    rw [b.sum_repr, hv']
  rw [hcol]
  congr 1
  exact EquivLike.range_comp v _

end GlobalTheory.TwLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOfClassOfFixedUnitsEq
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.UnitLemma.InvAlg.ClRel

theorem eq_of_mk_eq : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (x y : {x : B.Aˣ // B.σ (x : B.A) = x}), (Quot.mk _ x : B.Cl) = Quot.mk _ y → ∃ a : B.Aˣ, (y.1 : B.A) = x.1 * (a * B.σ a) := by
  intro K B x y h
  have hsu : ∀ u : B.Aˣ, B.σ (u : B.A) * B.σ ((u⁻¹ : B.Aˣ) : B.A) = 1 := fun u => by
    rw [← map_mul, Units.mul_inv, map_one]
  have heq : Equivalence (fun x y : {x : B.Aˣ // B.σ (x : B.A) = x} =>
      ∃ u : B.Aˣ, (y.1 : B.A) = x.1 * (u * B.σ (u : B.A))) := by
    refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨u, hu⟩
      refine ⟨u⁻¹, ?_⟩
      rw [hu]
      calc (x.1 : B.A) = (x.1 : B.A) * (((u : B.A) * ((u⁻¹ : B.Aˣ) : B.A)) *
            (B.σ (u : B.A) * B.σ ((u⁻¹ : B.Aˣ) : B.A))) := by rw [hsu, Units.mul_inv, one_mul, mul_one]
        _ = _ := by ring
    · rintro x y z ⟨u, hu⟩ ⟨v, hv⟩
      refine ⟨u * v, ?_⟩
      rw [hv, hu, Units.val_mul, map_mul]
      ring
  exact (heq.eqvGen_iff).mp (Quot.eqvGen_exact h)

end GlobalTheory.UnitLemma.InvAlg.ClRel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareMatrixImageSubmoduleContainsUniformi
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

namespace GlobalTheory

theorem exists_square_matrix_of_submodule_between
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (ϖ : O)
    (N : Submodule O (Fin n → O)) (hϖ : ϖ ≠ 0)
    (hN : ∀ y : Fin n → O, (fun a => ϖ * y a) ∈ N) :
    ∃ A : Matrix (Fin n) (Fin n) O, (∀ x, x ∈ N ↔ ∃ u, A *ᵥ u = x) ∧ A.det ≠ 0 := by
  first
  | exact @_root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq
  | exact _root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq
  | (apply _root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq ..)
end GlobalTheory
end

