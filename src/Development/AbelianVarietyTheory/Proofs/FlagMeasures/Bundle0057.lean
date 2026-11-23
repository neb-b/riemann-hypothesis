module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0047
public import Formalism.HermitianLattices.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalCommonStabiliserEqOneOfFixesSecondFrame
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.StabFix

section Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem local_eq_one (h : S.GLV) (hS : h ∈ S.St) (hf' : ∀ b, h (S.f' b) = S.f' b) : h = 1 := by
  obtain ⟨_, hcompl, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hW0 := (GlobalTheory.HL.FrameStab.stab_eq L r k S).1 h hS
  have hHe : IsHerm L S.Hm := S.herm.1
  have hN : h ∈ S.N := (Subgroup.mem_inf.1 hS).1
  simp only [Frames.N, Frames.Nof, Subgroup.mem_inf] at hN
  obtain ⟨⟨hiso, -⟩, hU⟩ := hN
  have hiso' : ∀ x y, hf L S.Hm (h x) (h y) = hf L S.Hm x y := hiso
  obtain ⟨-, hU2⟩ := hU

  have hfX : ∀ a, S.f a ∈ perp L S.Hm (S.spanTo S.f r) := by
    intro a
    rw [Frames.spanTo, Set.image_eq_range, GlobalTheory.FrameBasic.mem_perp_span L hHe]
    rintro ⟨j, hj⟩
    rw [S.gram]
    have : j ≠ Fin.last r := by
      intro e; simp [e] at hj
    simp [this]
  have hXle : S.spanTo S.f r ≤ S.ME := by
    refine le_trans (Submodule.span_mono (Set.image_mono ?_)) le_sup_left
    intro i hi
    exact Nat.lt_succ_of_lt hi
  have hME : S.ME = Submodule.span E (Set.range (Sum.elim S.f S.f')) := by
    rw [Frames.ME, GlobalTheory.HL.FrameStab.spanTo_top, GlobalTheory.HL.FrameStab.spanTo_top, Set.Sum.elim_range,
      Submodule.span_union]
  have hsub : ∀ a b y, hf L S.Hm (a - b) y = hf L S.Hm a y - hf L S.Hm b y := fun a b y =>
    (GlobalTheory.FrameBasic.hfL L S.Hm y).map_sub a b
  have hfix : ∀ a, h (S.f a) = S.f a := by
    intro a
    have hu : h (S.f a) - S.f a ∈ S.spanTo S.f r := hU2 _ (hfX a)
    have hW : h (S.f a) - S.f a ∈ S.W0 := by
      rw [Frames.W0, hME, GlobalTheory.FrameBasic.mem_perp_span L hHe]
      rintro (i | b)
      · simp only [Sum.elim_inl]
        rw [GlobalTheory.FrameBasic.hf_conj L hHe, hfX i _ hu, map_zero]
      · simp only [Sum.elim_inr]
        rw [hsub, ← hf' b, hiso', hf' b, sub_self]
    have := (Submodule.disjoint_def.1 hcompl.disjoint) _ (hXle hu) hW
    exact sub_eq_zero.1 this
  have hall : ∀ v, h v = v := by
    intro v
    have hv : v ∈ S.ME ⊔ S.W0 := by rw [hcompl.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    have hy' : y ∈ LinearMap.eqLocus (h : S.V →ₗ[E] S.V) LinearMap.id := by
      have : S.ME ≤ LinearMap.eqLocus (h : S.V →ₗ[E] S.V) LinearMap.id := by
        rw [hME, Submodule.span_le]
        rintro _ ⟨i | b, rfl⟩
        · exact hfix i
        · exact hf' b
      exact this hy
    rw [map_add (f := _), hW0 z hz]
    rw [LinearMap.mem_eqLocus] at hy'
    rw [show h y = y from hy']
  exact LinearEquiv.ext hall
end Loc

theorem nonempty_place (F : Type) [Field F] [NumberField F] : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩⟩

theorem eq_one_of_fix : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ x ∈ G.St,
    (∀ b, x (G.f' b) = G.f' b) → x = 1 := by
  intro F E _ _ _ _ _ sig A r k G x hx hfix
  obtain ⟨p⟩ := nonempty_place F
  have := (A.loc p).lf
  have := (A.loc p).char0
  obtain ⟨x', hx'St, hext⟩ := hx p
  have hloc : ∀ b, x' ((G.S p).f' b) = (G.S p).f' b := by
    intro b
    let u : ((A.loc p).Ep)ˣ := Units.map (algebraMap (A.loc p).Fp (A.loc p).Ep).toMonoidHom (G.c p ^ (r - (b : ℕ)))
    have hu : ((u : (A.loc p).Ep)) = algebraMap (A.loc p).Fp (A.loc p).Ep ((G.c p : (A.loc p).Fp) ^ (r - (b : ℕ))) := by
      simp [u]
    have h1 : x' ((u : (A.loc p).Ep) • (G.S p).f' b) = (u : (A.loc p).Ep) • (G.S p).f' b := by
      rw [hu, G.f'_eq p b, hext, hfix b]
    rw [map_smul] at h1
    have h2 := congrArg (fun v => ((u⁻¹ : ((A.loc p).Ep)ˣ) : (A.loc p).Ep) • v) h1
    simpa [smul_smul] using h2
  have h1 : x' = 1 := local_eq_one (G.S p) x' hx'St hloc
  have hinj := (GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p).1
  refine LinearEquiv.ext fun v => hinj ?_
  rw [← hext v, h1]
  rfl

end GlobalTheory.HL.StabFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootDiscrGeThreeHalvesOfIsTotallyComplex
section
open MeasureTheory NumberField Finset

namespace GlobalTheory


open MeasureTheory NumberField Finset in
theorem _root_.GlobalTheory.rootDiscr_ge_three_halves_of_totallyComplex :
    ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K →
      Module.finrank ℚ K = 2 * _root_.Formalism.HermitianLatticesTheory.fDeg K ∧ 1 ≤ _root_.Formalism.HermitianLatticesTheory.fDeg K ∧
      (3 / 2 : ℝ) ≤ 2 * _root_.Formalism.HermitianLatticesTheory.vInv K ∧
      Real.sqrt |(discr K : ℝ)| = (2 * _root_.Formalism.HermitianLatticesTheory.vInv K) ^ _root_.Formalism.HermitianLatticesTheory.fDeg K := by
  intro K _ _ hK
  have hf : _root_.Formalism.HermitianLatticesTheory.fDeg K = InfinitePlace.nrComplexPlaces K := by
    unfold _root_.Formalism.HermitianLatticesTheory.fDeg
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  have hn : Module.finrank ℚ K = 2 * _root_.Formalism.HermitianLatticesTheory.fDeg K := by
    rw [hf]; exact IsTotallyComplex.finrank K
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  have h1 : 1 ≤ _root_.Formalism.HermitianLatticesTheory.fDeg K := by omega
  have hv : 2 * _root_.Formalism.HermitianLatticesTheory.vInv K = |(discr K : ℝ)| ^ (1 / (2 * (_root_.Formalism.HermitianLatticesTheory.fDeg K : ℝ))) := by
    unfold _root_.Formalism.HermitianLatticesTheory.vInv; ring
  have hD0 : 0 ≤ |(discr K : ℝ)| := abs_nonneg _
  have hbound : (3 / 2 : ℝ) ^ (2 * _root_.Formalism.HermitianLatticesTheory.fDeg K) ≤ |(discr K : ℝ)| := by
    have hd := abs_discr_ge (K := K) (by omega)
    rw [hn, Int.cast_abs] at hd
    refine le_trans ?_ hd
    obtain ⟨m, hm⟩ : ∃ m, _root_.Formalism.HermitianLatticesTheory.fDeg K = m + 1 := ⟨_root_.Formalism.HermitianLatticesTheory.fDeg K - 1, by omega⟩
    rw [hm, pow_mul, pow_mul, pow_succ ((3 / 2 : ℝ) ^ 2), pow_succ ((3 * Real.pi / 4) ^ 2)]
    have hpi := Real.pi_gt_d2
    have hc : (11 / 2 : ℝ) ≤ (3 * Real.pi / 4) ^ 2 := by nlinarith
    have hm' : ((3 / 2 : ℝ) ^ 2) ^ m ≤ ((3 * Real.pi / 4) ^ 2) ^ m :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) m
    have hc' : (3 / 2 : ℝ) ^ 2 ≤ 4 / 9 * (3 * Real.pi / 4) ^ 2 := by nlinarith
    have := mul_le_mul hm' hc' (by positivity) (by positivity)
    linarith
  have hne : (2 * _root_.Formalism.HermitianLatticesTheory.fDeg K) ≠ 0 := by omega
  have hexp : (1 / (2 * (_root_.Formalism.HermitianLatticesTheory.fDeg K : ℝ))) = (((2 * _root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ))⁻¹ := by
    push_cast; rw [one_div]
  refine ⟨hn, h1, ?_, ?_⟩
  · rw [hv, hexp]
    calc (3 / 2 : ℝ) = ((3 / 2 : ℝ) ^ (2 * _root_.Formalism.HermitianLatticesTheory.fDeg K)) ^ (((2 * _root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ))⁻¹ :=
          (Real.pow_rpow_inv_natCast (by norm_num) hne).symm
      _ ≤ |(discr K : ℝ)| ^ (((2 * _root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ))⁻¹ :=
          Real.rpow_le_rpow (by positivity) hbound (by positivity)
  · rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hD0, Real.sqrt_eq_rpow]
    congr 1
    have : (_root_.Formalism.HermitianLatticesTheory.fDeg K : ℝ) ≠ 0 := by exact_mod_cast (by omega : _root_.Formalism.HermitianLatticesTheory.fDeg K ≠ 0)
    field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumAbsNormRpowNegLeDedekindZetaBound
section
open MeasureTheory NumberField Finset
open scoped ArithmeticFunction.zeta

namespace GlobalTheory.IdealZetaSum

theorem sum_Ioc_rpow_neg_le {s : ℝ} (hs : 1 < s) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) ≤ s / (s - 1) := by
  have hs1 : 0 < s - 1 := by linarith
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Ioc_self, sum_empty]; positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
    intro x hx y _ hxy
    have : (1 : ℝ) ≤ x := by simpa using hx.1
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hxy (by linarith)
  have h := AntitoneOn.sum_le_integral_Ico hN hanti
  rw [integral_rpow (Or.inr ⟨by linarith, by
    rw [Set.uIcc_of_le (by simpa using hN1)]; simp⟩)] at h
  have e : ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s)
      = 1 + ∑ i ∈ Ico 1 N, (((i + 1 : ℕ) : ℝ)) ^ (-s) := by
    rw [sum_Ico_add' (fun n : ℕ => (n : ℝ) ^ (-s)) 1 N 1]
    have : Ioc 0 N = insert 1 (Ico (1 + 1) (N + 1)) := by
      ext n; simp only [mem_Ioc, mem_insert, mem_Ico]; omega
    rw [this, sum_insert (by simp)]
    simp
  rw [e]
  have hpos : 0 ≤ (N : ℝ) ^ (-s + 1) := by positivity
  have h2 : ((N : ℝ) ^ (-s + 1) - ((1 : ℕ) : ℝ) ^ (-s + 1)) / (-s + 1) ≤ 1 / (s - 1) := by
    rw [Nat.cast_one, Real.one_rpow, show -s + 1 = -(s - 1) by ring, div_neg, ← neg_div]
    rw [show -s + 1 = -(s - 1) by ring] at hpos
    exact div_le_div_of_nonneg_right (by linarith) hs1.le
  have h3 : s / (s - 1) = 1 + 1 / (s - 1) := by field_simp; ring
  linarith

theorem sum_zeta_pow_mul_rpow_le (s : ℝ) (N k : ℕ) :
    ∑ n ∈ Ioc 0 N, (((ζ ^ k : ArithmeticFunction ℕ) n : ℕ) : ℝ) * (n : ℝ) ^ (-s)
      ≤ (∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s)) ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero, ArithmeticFunction.one_apply, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      ite_mul, one_mul, zero_mul, sum_ite_eq']
    split_ifs <;> simp
  | succ k ih =>
    rw [pow_succ (∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s))]
    refine le_trans ?_ (mul_le_mul_of_nonneg_right ih (sum_nonneg fun n _ => by positivity))
    rw [sum_mul_sum, ← sum_product', pow_succ]
    have e : ∀ n ∈ Ioc 0 N, (((ζ ^ k * ζ : ArithmeticFunction ℕ) n : ℕ) : ℝ) * (n : ℝ) ^ (-s)
        = ∑ x ∈ (Ioc 0 N ×ˢ Ioc 0 N).filter (fun x => x.1 * x.2 = n),
          (((ζ ^ k : ArithmeticFunction ℕ) x.1 : ℕ) : ℝ) * (x.1 : ℝ) ^ (-s) * (x.2 : ℝ) ^ (-s) := by
      intro n hn
      rw [mem_Ioc] at hn
      rw [ArithmeticFunction.mul_apply, Nat.cast_sum, sum_mul]
      refine sum_congr ?_ ?_
      · ext x
        simp only [Nat.mem_divisorsAntidiagonal, mem_filter, mem_product, mem_Ioc]
        constructor
        · rintro ⟨h, h0⟩
          have h1 : 0 < x.1 := Nat.pos_of_ne_zero (by rintro h1; rw [h1] at h; omega)
          have h2 : 0 < x.2 := Nat.pos_of_ne_zero (by rintro h1; rw [h1] at h; omega)
          refine ⟨⟨⟨h1, ?_⟩, h2, ?_⟩, h⟩ <;> nlinarith
        · rintro ⟨_, h⟩
          exact ⟨h, by omega⟩
      · intro x hx
        simp only [mem_filter, mem_product, mem_Ioc] at hx
        rw [← hx.2, Nat.cast_mul, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity),
          ArithmeticFunction.zeta_apply_ne hx.1.2.1.ne']
        simp [mul_assoc]
    rw [sum_congr rfl e, sum_fiberwise_eq_sum_filter]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun x _ _ => by positivity

theorem sum_absNorm_rpow_neg_le : ∀ (K : Type) [Field K] [NumberField K] (s : ℝ), 1 < s →
    ∀ (S : Finset (Ideal (𝓞 K))), (∀ I ∈ S, I ≠ ⊥) →
      ∑ I ∈ S, (Ideal.absNorm I : ℝ) ^ (-s) ≤ (s / (s - 1)) ^ Module.finrank ℚ K := by
  intro K _ _ s hs S hS
  classical
  set N := S.sup (fun I => Ideal.absNorm I) with hN
  refine le_trans ?_ (pow_le_pow_left₀ (sum_nonneg fun n _ => by positivity)
    (sum_Ioc_rpow_neg_le hs N) _)
  refine le_trans ?_ (sum_zeta_pow_mul_rpow_le s N _)
  rw [← sum_fiberwise_of_maps_to (s := S) (t := Ioc 0 N) (g := fun I => Ideal.absNorm I)]
  · refine sum_le_sum fun n hn => ?_
    rw [sum_congr rfl (g := fun _ => (n : ℝ) ^ (-s))
      (fun I hI => by rw [(mem_filter.mp hI).2]), sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [Nat.cast_le]
    refine le_trans ?_ (ncard_ideal_absNorm_eq_le K (mem_Ioc.mp hn).1.ne')
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard (fun I hI => (mem_filter.mp (mem_coe.mp hI)).2)
      (Ideal.finite_setOfPred_absNorm_eq n)
  · intro I hI
    rw [mem_Ioc]
    exact ⟨Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hS I hI),
      le_sup (f := fun I => Ideal.absNorm I) hI⟩

end GlobalTheory.IdealZetaSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermFramesCongrModThetaUnitriangular
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameChange

theorem coef_zero {ι M R : Type*} [CommRing R] [AddCommGroup M] [Module R M] {v : ι → M}
    (hv : LinearIndependent R v) {s : Set ι} {x : ι} (hx : x ∉ s) {c : R}
    (h : c • v x ∈ Submodule.span R (v '' s)) : c = 0 := by
  rw [Finsupp.mem_span_image_iff_linearCombination] at h
  obtain ⟨l, hl, e⟩ := h
  have h2 : Finsupp.single x c = l := hv (by rw [e, Finsupp.linearCombination_single])
  have h3 := congrArg (fun l : ι →₀ R => l x) h2
  simp only [Finsupp.single_eq_same] at h3
  rw [h3]
  exact (Finsupp.mem_supported' _ _).1 hl x hx

theorem diag_mul {m : ℕ} {R : Type*} [CommRing R] {P Q : Matrix (Fin m) (Fin m) R}
    (hP : P.BlockTriangular id) (hQ : Q.BlockTriangular id) (a : Fin m) :
    (P * Q) a a = P a a * Q a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with h | h
    · rw [hP h, zero_mul]
    · rw [hQ h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem sum_mem_spanTo (g g' : Fin (r + 1) → S.V) (hg' : ∀ a : Fin (r + 1), g' a ∈ S.spanTo g (a + 1))
    (c : Fin (r + 1) → E) (j : ℕ) (hc : ∀ a : Fin (r + 1), j ≤ (a : ℕ) → c a = 0) :
    ∑ a, c a • g' a ∈ S.spanTo g j :=
  Submodule.sum_mem _ fun a _ => by
    by_cases h : (a : ℕ) < j
    · exact Submodule.smul_mem _ _ (TermBasic.spanTo_mono S g (by omega) (hg' a))
    · rw [hc a (by omega), zero_smul]; exact Submodule.zero_mem _

theorem coeffs (g : Fin (r + 1) → S.V) (j : ℕ) (v : S.V)
    (hv : v ∈ Submodule.span L.O (g '' {i | (i : ℕ) < j})) :
    ∃ c : Fin (r + 1) → L.O, (∀ a : Fin (r + 1), j ≤ (a : ℕ) → c a = 0) ∧
      v = ∑ a, ((c a : L.O) : E) • g a := by
  rw [Finsupp.mem_span_image_iff_linearCombination] at hv
  obtain ⟨l, hl, rfl⟩ := hv
  refine ⟨l, fun a ha => (Finsupp.mem_supported' _ _).1 hl a (by simp; omega), ?_⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
  rfl

end GlobalTheory.HL.FrameChange

namespace GlobalTheory.HL.FrameChange

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem tri_coeffs {g : Fin (r + 1) → S.V} (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0)
    (hli : LinearIndependent E g) {n : S.GLV} (hn : n ∈ S.Nof g) {Λ : Submodule L.O S.V}
    (t : ∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo g j) ↔
      x ∈ Submodule.span L.O ((fun b => n (g b)) '' {i | (i : ℕ) < j}))
    (z : Fin (r + 1) → S.V) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hB0 : ∀ a b, b < a → B a b = 0) (hB1 : ∀ a, B a a = 1) (hz : ∀ b, z b = ∑ a, B a b • g a)
    (hzΛ : ∀ b, z b ∈ Λ) :
    ∃ C : Matrix (Fin (r + 1)) (Fin (r + 1)) L.O, (∀ a b, b < a → C a b = 0) ∧ (∀ a, C a a = 1) ∧
      ∀ b, z b = ∑ a, ((C a b : L.O) : E) • n (g a) := by
  have hself : ∀ a : Fin (r + 1), g a ∈ S.spanTo g (a + 1) := fun a =>
    TermBasic.self_mem S g (by omega)
  have hmem : ∀ a : Fin (r + 1), n (g a) ∈ S.spanTo g (a + 1) := fun a =>
    TermBasic.map_mem hg hn _ (hself a)
  have key : ∀ b : Fin (r + 1), ∃ c : Fin (r + 1) → L.O, (∀ a : Fin (r + 1), (b : ℕ) + 1 ≤ (a : ℕ) → c a = 0) ∧
      z b = ∑ a, ((c a : L.O) : E) • n (g a) := fun b => by
    have h1 : z b ∈ S.spanTo g (b + 1) := by
      rw [hz b]
      exact sum_mem_spanTo S g g hself _ _ fun a ha => hB0 a b (Fin.lt_def.2 (by omega))
    exact coeffs S _ _ _ ((t _ (by omega) _).1 ⟨hzΛ b, h1⟩)
  choose c hc0 hc using key
  refine ⟨Matrix.of fun a b => c b a, fun a b h => hc0 b a (by rw [Fin.lt_def] at h; omega),
    fun b => ?_, fun b => hc b⟩
  show c b b = 1
  apply Subtype.ext
  have e1 : z b - g b ∈ S.spanTo g b := by
    have : z b - g b = ∑ a, (B a b - if a = b then 1 else 0) • g a := by
      rw [hz b]; simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
    rw [this]
    refine sum_mem_spanTo S g g hself _ _ fun a ha => ?_
    by_cases hab : a = b
    · subst hab; simp [hB1]
    · have : b < a := Fin.lt_def.2 (by have := Fin.val_ne_of_ne hab; omega)
      simp [hab, hB0 a b this]
  have e2 : z b - ((c b b : L.O) : E) • n (g b) ∈ S.spanTo g b := by
    have : z b - ((c b b : L.O) : E) • n (g b) =
        ∑ a, (((c b a : L.O) : E) - if a = b then ((c b b : L.O) : E) else 0) • n (g a) := by
      rw [hc b]; simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
    rw [this]
    refine sum_mem_spanTo S g _ hmem _ _ fun a ha => ?_
    by_cases hab : a = b
    · subst hab; simp
    · have := Fin.val_ne_of_ne hab
      simp [hab, hc0 b a (by omega)]
  have e3 : n (g b) - g b ∈ S.spanTo g b := TermBasic.sub_mem hg hn b
  have e4 : (((c b b : L.O) : E) - 1) • g b = (z b - g b) - (z b - ((c b b : L.O) : E) • n (g b)) -
      ((c b b : L.O) : E) • (n (g b) - g b) := by
    simp only [sub_smul, smul_sub, one_smul]; abel
  have h5 := (S.spanTo g b).sub_mem ((S.spanTo g b).sub_mem e1 e2) ((S.spanTo g b).smul_mem ((c b b : L.O) : E) e3)
  rw [← e4] at h5
  have h6 := coef_zero hli (s := {i | (i : ℕ) < b}) (x := b) (by simp) h5
  simpa [sub_eq_zero] using h6

end GlobalTheory.HL.FrameChange

namespace GlobalTheory.HL.FrameChange

theorem frames_congr : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : Formalism.MainNotions.S.Loc.LocE F E) (r k : ℕ) (S : GlobalTheory.HL.Frames L r k) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ (y x : Fin (r + 1) → S.V) (B B' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → B a b = 0) → (∀ a, B a a = 1) → (∀ a b, b < a → B' a b = 0) → (∀ a, B' a a = 1) → (∀ b, y b = ∑ a, B a b • S.f a) → (∀ b, x b = ∑ a, B' a b • S.f' a) → (∀ a, y a ∈ Λ) → (∀ b, x b ∈ Λ) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ a b, ξ a b ∈ L.O) ∧ (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, S.InTh Λ (x b - ∑ a, ξ a b • y a) := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT y x B B' hB0 hB1 hB'0 hB'1 hy hx hyΛ hxΛ
  obtain ⟨-, hW, -, t, t', hli, -, -⟩ := TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, hn, hn', -, -, hth, -⟩ := hW
  have hg : ∀ a (j : Fin r), hf L S.Hm (S.f a) (S.f j.castSucc) = 0 := fun a j => by
    simp [S.gram, Fin.castSucc_ne_last]
  have hg' : ∀ a (j : Fin r), hf L S.Hm (S.f' a) (S.f' j.castSucc) = 0 := fun a j => by
    simp [S.gram', Fin.castSucc_ne_last]
  have hl1 : LinearIndependent E (S.fr d Λ) := hli.comp Sum.inl Sum.inl_injective
  have hl2 : LinearIndependent E (S.fr' d Λ) := hli.comp Sum.inr Sum.inr_injective
  have hlf : LinearIndependent E S.f := by
    have := hl1.map' (S.wit d Λ).1.symm.toLinearMap (LinearEquiv.ker _)
    have e : S.f = ⇑((S.wit d Λ).1.symm.toLinearMap) ∘ S.fr d Λ := by
      funext a; simp [Frames.fr]
    rw [e]; exact this
  have hlf' : LinearIndependent E S.f' := by
    have := hl2.map' (S.wit d Λ).2.symm.toLinearMap (LinearEquiv.ker _)
    have e : S.f' = ⇑((S.wit d Λ).2.symm.toLinearMap) ∘ S.fr' d Λ := by
      funext a; simp [Frames.fr']
    rw [e]; exact this
  obtain ⟨C, hC0, hC1, hCy⟩ := tri_coeffs S hg hlf hn t y B hB0 hB1 hy hyΛ
  obtain ⟨C', hC'0, hC'1, hC'x⟩ := tri_coeffs S hg' hlf' hn' t' x B' hB'0 hB'1 hx hxΛ
  have hCt : C.BlockTriangular id := fun a b h => hC0 a b h
  have hC't : C'.BlockTriangular id := fun a b h => hC'0 a b h
  have hdet : C.det = 1 := by
    rw [Matrix.det_of_upperTriangular hCt]; simp [hC1]
  letI : Invertible C := Matrix.invertibleOfIsUnitDet C (by rw [hdet]; exact isUnit_one)
  have hCit : C⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hCt
  have hCi1 : ∀ a, C⁻¹ a a = 1 := fun a => by
    have h1 := diag_mul hCit hCt a
    rw [Matrix.inv_mul_of_invertible, hC1, mul_one] at h1
    simpa using h1.symm
  set D := C⁻¹ * C' with hD
  have hDt : D.BlockTriangular id := hCit.mul hC't
  have hCD : C * D = C' := by rw [hD, ← Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.one_mul]
  choose w hwΛ hw using hth
  refine ⟨Matrix.of fun a b => ((D a b : L.O) : E), fun a b => (D a b).2, fun a b h => ?_, fun a => ?_,
    fun b => ?_⟩
  · simp [hDt h]
  · simp [hD, diag_mul hCit hC't, hCi1, hC'1]
  · have e1 : ∑ a, (Matrix.of fun a b => ((D a b : L.O) : E)) a b • y a =
        ∑ c, ((C' c b : L.O) : E) • (S.wit d Λ).1 (S.f c) := by
      simp only [Matrix.of_apply, hCy, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.sum_smul, ← hCD, Matrix.mul_apply]
      push_cast
      simp only [mul_comm]
    refine ⟨∑ c, ((C' c b : L.O) : E) • w c, Λ.sum_mem fun c _ => Λ.smul_mem (C' c b) (hwΛ c), ?_⟩
    rw [e1, hC'x b, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← smul_sub, hw c, smul_comm]

end GlobalTheory.HL.FrameChange
end

