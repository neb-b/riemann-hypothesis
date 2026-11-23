module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0182
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClozelCohomology.ContinuousEntryPairings.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.NormMapIntegerLeOne
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

private theorem norm_map_integer_le_one {E : Type} [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (u : HeightOneSpectrum (𝓞 E)) (j : u.adicCompletion E →+* Qbar l) (hl : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal)
    (hj : Continuous j) (y : u.adicCompletion E) (hy : y ∈ u.adicCompletionIntegers E) : ‖j y‖ ≤ 1 := by
  have hvl : Valued.v ((l : ℕ) : u.adicCompletion E) < 1 := by
    have h1 : u.valuation E (((l : ℕ) : 𝓞 E) : E) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) u _).2 hl
    have h2 : (((l : ℕ) : u.adicCompletion E)) = algebraMap E (u.adicCompletion E) (((l : ℕ) : 𝓞 E) : E) := by simp
    rw [h2]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u _).trans_lt h1
  have hlnorm : ‖j ((l : ℕ) : u.adicCompletion E)‖ = (l : ℝ)⁻¹ := by
    have h0 : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [map_natCast, h0, PadicAlgCl.norm_extends (p := l) (l : ℚ_[l]), Padic.norm_p]
  have hlt : ∀ k : ℕ, ‖j ((l : ℕ) : u.adicCompletion E)‖ * ‖j y‖ ^ k < 1 := by
    intro k
    have hyv : Valued.v y ≤ 1 := hy
    have hv : Valued.v (((l : ℕ) : u.adicCompletion E) * y ^ k) < 1 := by
      rw [map_mul, map_pow]
      exact mul_lt_one_of_lt_of_le hvl (pow_le_one' hyv k)
    have ht := Valued.tendsto_zero_pow_of_v_lt_one hv
    have ht2 : Filter.Tendsto (fun m : ℕ => (j (((l : ℕ) : u.adicCompletion E) * y ^ k)) ^ m) Filter.atTop (nhds 0) := by
      have := (hj.tendsto 0).comp ht
      simpa [Function.comp_def, map_pow] using this
    have := tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 ht2
    simpa [map_mul, map_pow, norm_mul, norm_pow] using this
  by_contra hcon
  have hgt : 1 < ‖j y‖ := not_le.1 hcon
  have hlpos : 0 < ‖j ((l : ℕ) : u.adicCompletion E)‖ := by
    rw [hlnorm]
    exact inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖j ((l : ℕ) : u.adicCompletion E)‖⁻¹) hgt
  have := hlt k
  have h3 : 1 < ‖j ((l : ℕ) : u.adicCompletion E)‖ * ‖j y‖ ^ k := by
    rw [inv_lt_iff_one_lt_mul₀ hlpos] at hk
    exact hk.trans_eq (mul_comm _ _)
  linarith

private theorem norm_map_entry_le {E : Type} [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] {n : ℕ}
    (u : HeightOneSpectrum (𝓞 E)) (j : u.adicCompletion E →+* Qbar l) (hl : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal)
    (hj : Continuous j) (d : ℕ) (M : Matrix (Fin n) (Fin n) (u.adicCompletion E))
    (hM : GlobalTheory.CongW.IntMat u (((l : u.adicCompletion E) ^ d) • M)) (a b : Fin n) : ‖j (M a b)‖ ≤ (l : ℝ) ^ d := by
  have h1 := norm_map_integer_le_one l u j hl hj _ (hM a b)
  have hlnorm : ‖j ((l : ℕ) : u.adicCompletion E)‖ = (l : ℝ)⁻¹ := by
    have h0 : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [map_natCast, h0, PadicAlgCl.norm_extends (p := l) (l : ℚ_[l]), Padic.norm_p]
  have hl0 : (0 : ℝ) < (l : ℝ) ^ d := pow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) d
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, norm_mul, norm_pow, hlnorm, inv_pow] at h1
  rwa [inv_mul_le_iff₀ hl0, mul_one] at h1

theorem UpperTheory.Gal.Gen.kappa_pf :
    UpperTheory.Gal.Gen.Kappa := by
  intro E _ _ _ l _ ι n
  have hex := fun v : InfinitePlace E =>
    GlobalTheory.LadicInf.exists_place E l (ι.symm.toRingHom.comp v.embedding)
  choose u j hl hj hjE using hex
  let f : InfinitePlace E → Af E →+* ℂ := fun v =>
    ι.toRingHom.comp ((j v).comp (pLoc E (u v)))
  let κ : UA E n →* (InfinitePlace E → GL (Fin n) ℂ) :=
    MonoidHom.pi fun v => (Matrix.GeneralLinearGroup.map ((f v).comp (pFin E))).comp (UA E n).subtype
  have hκ : ∀ (g : UA E n) (v : InfinitePlace E),
      κ g v = Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (j v)) (cLoc (u v) g) := by
    intro g v
    ext
    rfl
  refine ⟨κ, ?_, ?_, ?_⟩
  · rintro γ ⟨g₀, hg₀⟩
    funext v
    ext a b
    change (f v) (pFin E ((γ.1 : Matrix (Fin n) (Fin n) (Ad E)) a b)) =
      coord v.embedding (pInf E ((γ.1 : Matrix (Fin n) (Fin n) (Ad E)) a b))
    have hg₁ : (γ.1 : GL (Fin n) (Ad E)) = ratGL E n g₀ := hg₀.symm
    rw [hg₁]
    change (f v) (pFin E (algebraMap E (Ad E) ((g₀ : Matrix (Fin n) (Fin n) E) a b))) =
      coord v.embedding (pInf E (algebraMap E (Ad E) ((g₀ : Matrix (Fin n) (Fin n) E) a b)))
    rw [coord_algebraMap]
    have h := congrArg (fun φ : E →+* Qbar l => φ ((g₀ : Matrix (Fin n) (Fin n) E) a b)) (hjE v)
    simp only [RingHom.coe_comp, Function.comp_apply] at h
    change ι (j v (algebraMap E (u v |>.adicCompletion E) _)) = _
    rw [h]
    simp
  · intro x hx
    funext v
    have hx' : Matrix.GeneralLinearGroup.map (pFin E) x.1 = 1 := hx
    have h2 : Matrix.GeneralLinearGroup.map ((f v).comp (pFin E)) x.1 =
        Matrix.GeneralLinearGroup.map (f v) (Matrix.GeneralLinearGroup.map (pFin E) x.1) := by ext; rfl
    change Matrix.GeneralLinearGroup.map ((f v).comp (pFin E)) x.1 = 1
    rw [h2, hx', map_one]
  · intro g d hd v a b
    obtain ⟨h1, h2⟩ := hd (u v) (hl v)
    constructor
    · rw [hκ g v]
      change ‖ι.symm (ι (j v (((cLoc (u v) g : GL (Fin n) ((u v).adicCompletion E)) :
        Matrix (Fin n) (Fin n) ((u v).adicCompletion E)) a b)))‖ ≤ _
      rw [RingEquiv.symm_apply_apply]
      exact norm_map_entry_le l (u v) (j v) (hl v) (hj v) d _ h1 a b
    · rw [hκ g v, ← map_inv]
      change ‖ι.symm (ι (j v ((((cLoc (u v) g)⁻¹ : GL (Fin n) ((u v).adicCompletion E)) :
        Matrix (Fin n) (Fin n) ((u v).adicCompletion E)) a b)))‖ ≤ _
      rw [RingEquiv.symm_apply_apply]
      exact norm_map_entry_le l (u v) (j v) (hl v) (hj v) d _ h2 a b
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.PowNhds
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen
open Topology Filter

section
variable {𝕜 R : Type*} [NontriviallyNormedField 𝕜] [NormedRing R] [NormedAlgebra 𝕜 R]

private lemma strict_pow (N : ℕ) :
    HasStrictFDerivAt (fun x : R => x ^ N) ((N : 𝕜) • ContinuousLinearMap.id 𝕜 R) (1 : R) := by
  refine (hasStrictFDerivAt_pow' (𝕜 := 𝕜) N (x := (1 : R))).congr_fderiv ?_
  simp only [one_pow, MulOpposite.op_one, one_smul, Finset.sum_const, Finset.card_range]
  rw [Nat.cast_smul_eq_nsmul]

private lemma map_pow_nhds [CharZero 𝕜] [CompleteSpace 𝕜] [CompleteSpace R] {N : ℕ} (hN : N ≠ 0) :
    map (fun x : R => x ^ N) (𝓝 1) = 𝓝 1 := by
  have hN' : (N : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hN
  let e : R ≃L[𝕜] R := ContinuousLinearEquiv.equivOfInverse ((N : 𝕜) • ContinuousLinearMap.id 𝕜 R)
    ((N : 𝕜)⁻¹ • ContinuousLinearMap.id 𝕜 R) (fun x => by simp [smul_smul, hN'])
    (fun x => by simp [smul_smul, hN'])
  have hf : HasStrictFDerivAt (fun x : R => x ^ N) (e : R →L[𝕜] R) 1 := strict_pow (𝕜 := 𝕜) N
  simpa using hf.map_nhds_eq_of_equiv

private lemma units_pow_nhds [CharZero 𝕜] [CompleteSpace 𝕜] [CompleteSpace R] {N : ℕ} (hN : N ≠ 0)
    {V : Set Rˣ} (hV : V ∈ 𝓝 (1 : Rˣ)) : (fun x => x ^ N) '' V ∈ 𝓝 (1 : Rˣ) := by
  have he := Units.isOpenEmbedding_val (R := R)
  have h1 : ((↑) : Rˣ → R) '' V ∈ 𝓝 (1 : R) := by
    simpa using he.image_mem_nhds.mpr hV
  have h2 : (fun x : R => x ^ N) '' (((↑) : Rˣ → R) '' V) ∈ 𝓝 (1 : R) := by
    rw [← map_pow_nhds (𝕜 := 𝕜) hN]
    exact image_mem_map h1
  rw [← he.image_mem_nhds]
  rw [Set.image_image, Units.val_one]
  rw [Set.image_image] at h2
  simpa using h2
end

theorem UpperTheory.Gal.Gen.powNhds_pf :
    UpperTheory.Gal.Gen.PowNhds := by
  intro E _ _ w a N hN V hV
  letI : NontriviallyNormedField (w.adicCompletion E) :=
    Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  letI : NormedRing (Matrix (Fin a) (Fin a) (w.adicCompletion E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra (w.adicCompletion E) (Matrix (Fin a) (Fin a) (w.adicCompletion E)) :=
    Matrix.linftyOpNormedAlgebra
  haveI : @CompleteSpace (Matrix (Fin a) (Fin a) (w.adicCompletion E))
      (@Matrix.linftyOpNormedRing (Fin a) (w.adicCompletion E) _ _ _).toUniformSpace :=
    inferInstanceAs (CompleteSpace (Fin a → Fin a → w.adicCompletion E))
  exact units_pow_nhds (𝕜 := w.adicCompletion E) hN hV
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.SizeLe
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen.SeparatingAlgebraSizeBound

private def sz {a : ℕ} (lam : DomWeight a) : ℕ := ∑ k, (lam.w k).natAbs

private theorem sz_dual {a : ℕ} (lam : DomWeight a) : sz lam.dual = sz lam := by
  unfold sz DomWeight.dual
  simp only [Int.natAbs_neg]
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun k => by simp)

private theorem one_le {a : ℕ} (lam : DomWeight a) :
    ∑ i, lam.natW i + a * lam.detShift.natAbs ≤ a * (2 * sz lam) := by
  have key : ∀ i : Fin a, lam.natW i + lam.detShift.natAbs ≤ 2 * sz lam := by
    intro i
    have ha : 0 < a := i.pos
    have hd : lam.detShift = lam.w ⟨a - 1, by omega⟩ := by
      simp only [DomWeight.detShift, dif_pos ha]
    have hnat : lam.natW i = (lam.w i - lam.w ⟨a - 1, by omega⟩).toNat := by
      simp only [DomWeight.natW, hd]
    have hLle : (lam.w ⟨a - 1, by omega⟩).natAbs ≤ sz lam := by
      unfold sz
      exact Finset.single_le_sum (f := fun k => (lam.w k).natAbs) (fun k _ => Nat.zero_le _)
        (Finset.mem_univ _)
    rw [hnat, hd]
    by_cases hi : i = ⟨a - 1, by omega⟩
    · have h0 : (lam.w i - lam.w ⟨a - 1, by omega⟩).toNat = 0 := by
        rw [hi, sub_self]; rfl
      omega
    · have hpair : (lam.w i).natAbs + (lam.w ⟨a - 1, by omega⟩).natAbs ≤ sz lam := by
        unfold sz
        have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => (lam.w k).natAbs)
          (Finset.subset_univ {i, ⟨a - 1, by omega⟩}) (fun _ _ _ => Nat.zero_le _)
        rwa [Finset.sum_pair hi] at h
      omega
  calc ∑ i, lam.natW i + a * lam.detShift.natAbs
      = ∑ i, (lam.natW i + lam.detShift.natAbs) := by
        simp [Finset.sum_add_distrib]
    _ ≤ ∑ _i : Fin a, 2 * sz lam := Finset.sum_le_sum fun i _ => key i
    _ = a * (2 * sz lam) := by simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

private noncomputable def emb : InfinitePlace E ⊕ InfinitePlace E → (E →+* ℂ)
  | .inl v => v.embedding
  | .inr v => ComplexEmbedding.conjugate v.embedding

private theorem mk_emb_inl (v : InfinitePlace E) : InfinitePlace.mk (emb (.inl v)) = v :=
  InfinitePlace.mk_embedding v

private theorem mk_emb_inr (v : InfinitePlace E) : InfinitePlace.mk (emb (.inr v)) = v := by
  simp [emb]

private theorem emb_injective : Function.Injective (emb (E := E)) := by
  intro x y h
  have hm : InfinitePlace.mk (emb x) = InfinitePlace.mk (emb y) := by rw [h]
  rcases x with v | v <;> rcases y with w | w <;>
    simp only [mk_emb_inl, mk_emb_inr] at hm <;> subst hm
  · rfl
  · simp only [emb] at h
    exact absurd h.symm (conjugate_ne _)
  · simp only [emb] at h
    exact absurd h (conjugate_ne _)
  · rfl

private theorem two_le (W : Wt E a) : ∑ v, 2 * sz (W v) ≤ GlobalTheory.CongW.wtSize W.at := by
  have h1 : ∑ v, 2 * sz (W v)
      = ∑ s : InfinitePlace E ⊕ InfinitePlace E, sz (W.at (emb s)) := by
    rw [Fintype.sum_sum_type]
    simp only [emb, Wt.at_embedding, Wt.at_conjugate, sz_dual, two_mul, Finset.sum_add_distrib]
  have h2 : ∑ s : InfinitePlace E ⊕ InfinitePlace E, sz (W.at (emb s))
      = ∑ τ ∈ Finset.univ.map ⟨emb, emb_injective⟩, sz (W.at τ) := by
    rw [Finset.sum_map]; rfl
  have h3 : GlobalTheory.CongW.wtSize W.at = ∑ τ, sz (W.at τ) := rfl
  rw [h1, h2, h3]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

end UpperTheory.Gal.Gen.SeparatingAlgebraSizeBound

open UpperTheory.Gal.Gen.SeparatingAlgebraSizeBound in
theorem UpperTheory.Gal.Gen.sizeLe_pf :
    UpperTheory.Gal.Gen.SizeLe := by
  intro E _ _ _ a W
  calc (∑ v, ∑ i, (W v).natW i) + ∑ v, a * (W v).detShift.natAbs
      = ∑ v, (∑ i, (W v).natW i + a * (W v).detShift.natAbs) := Finset.sum_add_distrib.symm
    _ ≤ ∑ v, a * (2 * sz (W v)) := Finset.sum_le_sum fun v _ => one_le (W v)
    _ = a * ∑ v, 2 * sz (W v) := by rw [Finset.mul_sum]
    _ ≤ a * GlobalTheory.CongW.wtSize W.at := Nat.mul_le_mul_left a (two_le W)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.TotalDegreeLeOfCol
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

private theorem totalDegree_le_of_col {r n : ℕ} {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) ℂ}
    (h : MvPolynomial.IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW r n) F ν) : F.totalDegree ≤ ∑ i, ν i := by
  unfold MvPolynomial.totalDegree
  refine Finset.sup_le fun m hm => ?_
  have hw : Finsupp.weight (Formalism.GradedWeylDivisibility.colW r n) m = ν := h (MvPolynomial.mem_support_iff.mp hm)
  rw [← hw, Finsupp.weight_apply]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, Formalism.GradedWeylDivisibility.colW, smul_eq_mul]
  rw [Finset.sum_comm]
  refine le_of_eq (Finset.sum_congr rfl fun v _ => ?_)
  simp [Pi.single_apply]

theorem UpperTheory.Gal.Gen.degLe_pf :
    UpperTheory.Gal.Gen.DegLe := by
  intro T _ n lam x hx
  refine Submodule.span_induction (p := fun x _ => MvPolynomial.totalDegree x ≤ ∑ τ, ∑ i, (lam τ).natW i)
    ?_ ?_ ?_ ?_ hx
  · rintro P ⟨F, hF, rfl⟩
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
    refine (MvPolynomial.totalDegree_rename_le (fun v => (τ, v)) (F τ)).trans ?_
    have hm := (Submodule.mem_inf.mp (hF τ)).1
    exact totalDegree_le_of_col ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp hm)
  · simp
  · intro a b _ _ ha hb
    exact (MvPolynomial.totalDegree_add a b).trans (max_le ha hb)
  · intro c a _ ha
    exact (MvPolynomial.totalDegree_smul_le c a).trans ha
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.TyStep
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.tyStep_pf :
    UpperTheory.Gal.Gen.LevFacts → UpperTheory.Gal.Gen.Ell → UpperTheory.Gal.Gen.KerOpen → UpperTheory.Gal.Gen.CharSum → UpperTheory.Gal.Gen.TwistPart → UpperTheory.Gal.Gen.TyStep := by
  intro hLev hEll hKer hCS hTw E _ _ _ l _ ι a w₀ hs K hK W J hJo hJc htf m θ f hf
  classical
  obtain ⟨hLvl, -, hC, -, -, -⟩ := hLev E a w₀ hs K hK J hJo hJc
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : Finite (Multiplicative (ZMod (l ^ m))) :=
    inferInstanceAs (Finite (ZMod (l ^ m)))
  let lam : (lev K w₀ J) →* Multiplicative (ZMod (l ^ m)) :=
    θ.comp (((cLoc w₀).comp (lev K w₀ J).subtype).codRestrict J fun c => hC c.1 c.2)
  have hlam : ∀ c : lev K w₀ J, lam c = θ ⟨cLoc w₀ c.1, hC c.1 c.2⟩ := fun c => rfl
  obtain ⟨N, hNo, hN1, hN⟩ := hKer E w₀ a J hJo _ θ
  obtain ⟨ℓ, hℓi, hℓC, hℓa⟩ := hEll E a (lev K w₀ J) hLvl _ lam
    ⟨cLoc w₀ ⁻¹' N, hNo.preimage (GlobalTheory.BCT.GlobLev.continuous_cLoc w₀), by simpa using hN1,
      fun c hc => hN ⟨cLoc w₀ c.1, hC c.1 c.2⟩ hc⟩
    (fun c hc => by
      obtain ⟨k, hk0, hk⟩ := isOfFinOrder_iff_pow_eq_one.1 hc
      have h1 : (cLoc w₀ c.1) ^ k = 1 := by
        have h0 : c.1 ^ k = 1 := by simpa using congrArg Subtype.val hk
        rw [← map_pow, h0, map_one]
      have h2 := htf _ (hC c.1 c.2) k hk0 h1
      have h3 : (⟨cLoc w₀ c.1, hC c.1 c.2⟩ : J) = 1 := Subtype.ext h2
      rw [hlam, h3, map_one])
  obtain ⟨s, hs1, hs2⟩ := hCS (l ^ m)
  have hex : ∀ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ,
      ∃ F : algForms W, ∀ v g, F.1 v g = ((χ (ℓ g) : ℂˣ) : ℂ) * f.1 v g := fun χ =>
    GlobalTheory.T.exists_algebraicModularForm_mul_archInvariant E a W f (fun g => ((χ (ℓ g) : ℂˣ) : ℂ)) (hℓa fun y => ((χ y : ℂˣ) : ℂ))
      fun g x hx => by simp only [hℓi g x hx]
  choose F hF using hex
  have hpart : ∀ χ ∈ s, F χ ∈ part W K
      (fun U => ∃ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ, χ ≠ 1 ∧ GlobalTheory.CongW.HasTypeVec w₀ K J θ χ U) := by
    intro χ hχ
    have h := hTw E a w₀ K W J _ θ χ hC (fun k hk => hK.one k hk w₀ (not_apart_self w₀)) (F χ)
      (fun c hc v g => by
        rw [hF, hF, hℓC g ⟨c, hc⟩, hf c hc v g, map_mul, Units.val_mul, hlam, mul_comm (((χ (ℓ g) : ℂˣ) : ℂ))]
        ring)
    refine (?_ : part W K _ ≤ part W K _) h
    exact iSup₂_le fun π hπ => le_iSup₂_of_le π ⟨χ, hs1 χ hχ, hπ⟩ le_rfl
  refine ⟨-∑ χ ∈ s, F χ, neg_mem (sum_mem hpart), fun g => 1 + ∑ χ ∈ s, ((χ (ℓ g) : ℂˣ) : ℂ), ?_, ?_⟩
  · intro g
    rcases hs2 (ℓ g) with h | h
    · simp only [h, map_zero, norm_zero]
      positivity
    · simp only [h]
      rw [map_natCast, Nat.cast_pow, norm_pow]
  · intro v g
    have e : ((-∑ χ ∈ s, F χ : algForms W) : W.Sp →ₗ[ℂ] (UA E a → ℂ)) v g = -∑ χ ∈ s, (F χ).1 v g := by
      simp [Finset.sum_apply, LinearMap.sum_apply]
    change f.1 v g - ((-∑ χ ∈ s, F χ : algForms W) : W.Sp →ₗ[ℂ] (UA E a → ℂ)) v g = _
    rw [e, Finset.sum_congr rfl fun χ _ => hF χ v g, ← Finset.sum_mul]
    ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.WBound
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen


open MvPolynomial in
private theorem continuous_coeff_blockAct' {Y : Type} [TopologicalSpace Y] {T : Type} {k n : ℕ}
    (A : Y → T → Matrix (Fin k) (Fin k) ℂ) (hA : ∀ t a b, Continuous fun x => A x t a b)
    (F : MvPolynomial (T × Fin k × Fin n) ℂ) :
    ∀ m, Continuous fun x => (Formalism.GradedWeylDivisibility.blockAct ℂ (A x) F).coeff m := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a =>
    intro m
    have e : ∀ x, Formalism.GradedWeylDivisibility.blockAct ℂ (n := n) (A x) (C a) = (C a : MvPolynomial (T × Fin k × Fin n) ℂ) :=
      fun x => (Formalism.GradedWeylDivisibility.blockAct ℂ (n := n) (A x)).commutes a
    simp only [e]
    exact continuous_const
  | add p q hp hq =>
    intro m
    simp only [map_add (f := _), AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact (hp m).add (hq m)
  | mul_X p w hp =>
    intro m
    have e : ∀ x, Formalism.GradedWeylDivisibility.blockAct ℂ (A x) (X w) = ∑ b : Fin k, C (A x w.1 w.2.1 b) * X (w.1, (b, w.2.2)) :=
      fun x => aeval_X _ _
    simp only [map_mul, e, Finset.mul_sum, coeff_sum]
    refine continuous_finsetSum _ fun b _ => ?_
    simp only [mul_left_comm _ (C _), coeff_C_mul, coeff_mul_X']
    by_cases hw : ((w.1, (b, w.2.2)) : T × Fin k × Fin n) ∈ m.support
    · simp only [hw, ite_true]
      exact (hA _ _ _).mul (hp _)
    · simp only [hw, ite_false, mul_zero]
      exact continuous_const

private theorem continuous_detTwK' {Y : Type} [TopologicalSpace Y] {T : Type} [Fintype T] {n : ℕ}
    (lam : T → DomWeight n) (g : Y → (T → GL (Fin n) ℂ))
    (hg : ∀ v a b, Continuous fun x => ((g x v : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b) :
    Continuous fun x => Formalism.L2.DIV.detTwK lam (g x) := by
  simp only [Formalism.L2.DIV.detTwK]
  refine continuous_finsetProd _ fun τ _ => ?_
  have e : ∀ x, detPow ℂ n (g x τ) (lam τ).detShift =
      ((g x τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ^ (lam τ).detShift := by
    intro x
    rw [detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
  simp only [e]
  have hc : Continuous fun x => ((g x τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) :=
    continuous_pi fun a => continuous_pi fun b => hg τ a b
  refine hc.matrix_det.zpow₀ _ fun x => Or.inl ?_
  exact (Matrix.isUnit_iff_isUnit_det _).1 (g x τ).isUnit |>.ne_zero


private theorem continuous_rhoK_coeff' {Y : Type} [TopologicalSpace Y] {T : Type} [Fintype T] {n : ℕ}
    (lam : T → DomWeight n) {d : ℕ} (B : Module.Basis (Fin d) ℂ (Formalism.L2.DIV.VV ℂ lam)) (g : Y → (T → GL (Fin n) ℂ))
    (hg : ∀ v a b, Continuous fun x => ((g x v : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b) (i j : Fin d) :
    Continuous fun x => LinearMap.toMatrix B B (Formalism.L2.DIV.rhoK lam (g x)) i j := by
  classical
  obtain ⟨s, a, ha⟩ := GlobalTheory.IntStruct.exists_coord_eq_sum_coeff (Formalism.L2.DIV.VV ℂ lam) B i
  have e : ∀ x, LinearMap.toMatrix B B (Formalism.L2.DIV.rhoK lam (g x)) i j = ∑ m : s, a m *
      (Formalism.L2.DIV.detTwK lam (g x) * (Formalism.GradedWeylDivisibility.blockAct ℂ
        (fun τ => Matrix.transpose ((g x τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
        ((B j : Formalism.L2.DIV.VV ℂ lam) : Formalism.L2.DIV.Pol ℂ T n)).coeff m.1) := by
    intro x
    rw [LinearMap.toMatrix_apply, ha]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
  simp only [e]
  exact continuous_finsetSum _ fun m _ => continuous_const.mul ((continuous_detTwK' lam g hg).mul
    (continuous_coeff_blockAct' _ (fun t a b => hg t b a) _ m.1))

private theorem continuous_rep_coeff {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (W : Wt E a) {d : ℕ}
    (B : Module.Basis (Fin d) ℂ W.Sp) (i j : Fin d) :
    Continuous fun x : infU E a => B.repr (W.rep x (B i)) j := by
  have h := continuous_rhoK_coeff' (T := InfinitePlace E) W B (fun x : infU E a => cAll x.1)
    (fun v p q => GlobalTheory.PolyRealU.continuous_entry v.embedding p q) j i
  refine h.congr fun x => ?_
  rw [LinearMap.toMatrix_apply]
  rfl

theorem UpperTheory.Gal.Gen.wBound_pf :
    UpperTheory.Gal.Gen.WBound := by
  intro E _ _ _ a W d B
  haveI := GlobalTheory.InfUCompact.compactSpace_infU E a
  have hc : Continuous fun x : infU E a => fun (i j : Fin d) => B.repr (W.rep x (B i)) j :=
    continuous_pi fun i => continuous_pi fun j => continuous_rep_coeff W B i j
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun x i j => ?_⟩
  exact ((norm_le_pi_norm (fun j => B.repr (W.rep x (B i)) j) j).trans
    (norm_le_pi_norm (fun (i j : Fin d) => B.repr (W.rep x (B i)) j) i)).trans (hC x (Set.mem_univ _))
end

