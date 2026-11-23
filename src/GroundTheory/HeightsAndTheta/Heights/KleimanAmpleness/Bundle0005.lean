module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Objects
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0008

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section PointLemmas

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {j : Fin (N + 1)}

theorem ideal_eq_of_isHomogeneous {I J : Ideal (Poly S N)}
    (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I)
    (hJ : ∀ p ∈ J, ∀ d : ℕ, homogeneousComponent d p ∈ J)
    (h : ∀ (f : Poly S N) (e : ℕ), f.IsHomogeneous e → (f ∈ I ↔ f ∈ J)) : I = J := by
  ext f
  constructor
  · intro hf
    rw [← sum_homogeneousComponent f]
    exact J.sum_mem fun d _ => (h _ d (homogeneousComponent_isHomogeneous d f)).mp (hI f hf d)
  · intro hf
    rw [← sum_homogeneousComponent f]
    exact I.sum_mem fun d _ => (h _ d (homogeneousComponent_isHomogeneous d f)).mpr (hJ f hf d)

theorem exists_eq_X_pow_of_mem_monos_single {s : Poly S N} (hs : s ∈ monos {j}) :
    ∃ n : ℕ, s = X j ^ n := by
  have hs' : s ∈ Submonoid.closure {(X j : Poly S N)} := by
    have : ((fun i => (X i : Poly S N)) '' ((({j} : Finset (Fin (N + 1))) : Set (Fin (N + 1))))) =
        {X j} := by simp
    rw [← this]
    exact hs
  obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.mp hs'
  exact ⟨n, rfl⟩

theorem notMem_of_mem_monos_single {pp : Ideal (Poly S N)} [hpp : pp.IsPrime]
    (hX : (X j : Poly S N) ∉ pp) {s : Poly S N} (hs : s ∈ monos {j}) : s ∉ pp := by
  obtain ⟨n, rfl⟩ := exists_eq_X_pow_of_mem_monos_single hs
  exact fun h => hX (hpp.mem_of_pow_mem n h)

theorem mem_of_div_eq (hj : x j ≠ 0) {pp : Ideal (Poly S N)} [hpp : pp.IsPrime]
    (hle : primeOf (S := S) x ≤ pp) (hX : (X j : Poly S N) ∉ pp) {f s' G s : Poly S N} {e D : ℕ}
    (hf : f.IsHomogeneous e) (hs' : s' ∈ monos {j}) (hs'e : s'.IsHomogeneous e) (hG : G ∈ pp)
    (hGD : G.IsHomogeneous D) (hs : s ∈ monos {j}) (hsD : s.IsHomogeneous D)
    (h : aeval x f / aeval x s' = aeval x G / aeval x s) : f ∈ pp := by
  have h0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos (singleChart hj) hs
  have h0' : aeval x s' ≠ 0 := eval_ne_zero_of_mem_monos (singleChart hj) hs'
  rw [div_eq_div_iff h0' h0] at h
  have h2 : (s' * G).IsHomogeneous (D + e) := by
    rw [add_comm D e]
    exact hs'e.mul hGD
  have hF : s * f - s' * G ∈ primeOf (S := S) x := by
    rw [mem_primeOf_of_isHomogeneous x ((hsD.mul hf).sub h2)]
    simp only [map_sub, map_mul]
    linear_combination h
  have h3 : s * f ∈ pp := by
    have := pp.add_mem (hle hF) (pp.mul_mem_left s' hG)
    rwa [sub_add_cancel] at this
  exact (hpp.mem_or_mem h3).resolve_left (notMem_of_mem_monos_single hX hs)


variable (x) in
def chartPrimeIdeal (hj : x j ≠ 0) (pp : Ideal (Poly S N)) :
    Ideal (chartRing S x (singleChart hj)) where
  carrier := {a | ∃ (f s : Poly S N) (e : ℕ), f ∈ pp ∧ s ∈ monos {j} ∧ f.IsHomogeneous e ∧
    s.IsHomogeneous e ∧ (a : Ω) = aeval x f / aeval x s}
  zero_mem' := ⟨0, 1, 0, pp.zero_mem, one_mem _, isHomogeneous_zero _ _ _, isHomogeneous_one _ _,
    by simp⟩
  add_mem' := by
    rintro a b ⟨f, s, e, hf, hs, hfe, hse, ha⟩ ⟨g, t, d, hg, ht, hgd, htd, hb⟩
    refine ⟨f * t + s * g, s * t, e + d, pp.add_mem (pp.mul_mem_right t hf) (pp.mul_mem_left s hg),
      mul_mem hs ht, (hfe.mul htd).add (hse.mul hgd), hse.mul htd, ?_⟩
    rw [Subalgebra.coe_add, ha, hb, div_add_div _ _ (eval_ne_zero_of_mem_monos (singleChart hj) hs)
      (eval_ne_zero_of_mem_monos (singleChart hj) ht)]
    simp only [map_add (f := _), map_mul]
  smul_mem' := by
    rintro c a ⟨g, t, d, hg, ht, hgd, htd, ha⟩
    obtain ⟨f, s, e, hs, hfe, hse, hc⟩ := c.2
    refine ⟨f * g, s * t, e + d, pp.mul_mem_left f hg, mul_mem hs ht, hfe.mul hgd, hse.mul htd, ?_⟩
    change (c : Ω) * (a : Ω) = _
    rw [hc, ha, map_mul, map_mul, div_mul_div_comm]

theorem chartPrime_le_chartPrimeIdeal (hj : x j ≠ 0) (pp : Ideal (Poly S N)) :
    chartPrime pp hj ≤ chartPrimeIdeal x hj pp := by
  rw [chartPrime, Ideal.span_le]
  intro a ha
  exact ha

theorem mem_chartPrime_iff (hj : x j ≠ 0) {pp : Ideal (Poly S N)} [pp.IsPrime]
    (hle : primeOf (S := S) x ≤ pp) (hX : (X j : Poly S N) ∉ pp) {a : chartRing S x (singleChart hj)}
    {f s : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) (hs : s ∈ monos {j}) (hse : s.IsHomogeneous e)
    (ha : (a : Ω) = aeval x f / aeval x s) : a ∈ chartPrime pp hj ↔ f ∈ pp := by
  constructor
  · intro h
    obtain ⟨G, t, D, hG, ht, hGD, htD, hat⟩ := chartPrime_le_chartPrimeIdeal hj pp h
    exact mem_of_div_eq hj hle hX hf hs hse hG hGD ht htD (ha.symm.trans hat)
  · intro h
    exact Ideal.subset_span ⟨f, s, e, h, hs, hf, hse, ha⟩

theorem coe_aeval_ratio (hj : x j ≠ 0) {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) :
    ((aeval (ratio (S := S) hj) f : chartRing S x (singleChart hj)) : Ω) = aeval x f / x j ^ e := by
  rw [← aeval_div_of_isHomogeneous hf j]
  change (chartRing S x (singleChart hj)).val _ = _
  rw [comp_aeval_apply]
  rfl

theorem coe_aeval_ratio' (hj : x j ≠ 0) {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) :
    ((aeval (ratio (S := S) hj) f : chartRing S x (singleChart hj)) : Ω) =
      aeval x f / aeval x (X j ^ e : Poly S N) := by
  rw [coe_aeval_ratio hj hf, map_pow, aeval_X]

end PointLemmas

theorem PrimeFiltration.Point.proof : PrimeFiltration.Point.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x pp hpp hhom hle j hj hX
  refine ⟨?_, ?_⟩
  · rw [Ideal.isPrime_iff]
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one]
      rw [mem_chartPrime_iff (f := 1) (s := 1) hj hle hX (isHomogeneous_one _ _) (one_mem _)
        (isHomogeneous_one _ _) (by simp)]
      exact (Ideal.ne_top_iff_one pp).mp hpp.ne_top
    · intro a b hab
      obtain ⟨f, s, e, hs, hf, hse, ha⟩ := a.2
      obtain ⟨g, t, d, ht, hg, htd, hb⟩ := b.2
      have hab' : ((a * b : chartRing S x (singleChart hj)) : Ω) = aeval x (f * g) / aeval x (s * t) := by
        rw [Subalgebra.coe_mul, ha, hb, map_mul, map_mul, div_mul_div_comm]
      rw [mem_chartPrime_iff hj hle hX (hf.mul hg) (mul_mem hs ht) (hse.mul htd) hab'] at hab
      rw [mem_chartPrime_iff hj hle hX hf hs hse ha, mem_chartPrime_iff hj hle hX hg ht htd hb]
      exact hpp.mem_or_mem hab
  · intro K' _ _ ψ hker
    apply ideal_eq_of_isHomogeneous (fun p hp d => homogeneousComponent_mem_primeOf _ hp d) hhom
    intro f e hf
    rw [mem_primeOf_of_isHomogeneous _ hf, ← comp_aeval_apply, ← RingHom.mem_ker, hker]
    exact mem_chartPrime_iff hj hle hX hf (pow_mem (X_mem_monos (Finset.mem_singleton_self j)) e)
      (isHomogeneous_X_pow j e) (coe_aeval_ratio' hj hf)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistSections
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Loc

variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type*} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]

theorem locRes_locRes {I J K : Finset (Fin (N + 1))} (h1 : I ⊆ J) (h2 : J ⊆ K) (x : LocMod S N M I) :
    locRes h2 (locRes h1 x) = locRes (h1.trans h2) x := by
  revert x
  refine LocalizedModule.induction_on ?_
  intro m s
  rw [locRes_mk, locRes_mk, locRes_mk]

theorem locRes_self {I : Finset (Fin (N + 1))} (h : I ⊆ I) (x : LocMod S N M I) : locRes h x = x := by
  revert x
  refine LocalizedModule.induction_on ?_
  intro m s
  rw [locRes_mk]

theorem locRes_mem_degLoc (𝓜 : GradedPMod S N M) (c : ℤ) (I J : StdCell N) (h : I.1 ⊆ J.1)
    {x : LocMod S N M I.1} (hx : x ∈ degLoc 𝓜 c I) : locRes h x ∈ degLoc 𝓜 c J := by
  have key : degLoc 𝓜 c I ≤ (degLoc 𝓜 c J).comap (locResS I J h) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, s, a, e, hm, hs, hae, rfl⟩
    show locRes h (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I.1) M) ∈ degLoc 𝓜 c J
    rw [locRes_mk]
    exact Submodule.subset_span ⟨m, ⟨s, monos_mono h s.2⟩, a, e, hm, hs, hae, rfl⟩
  exact key hx

end Loc

section Proof

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (y : Fin (N + 1) → Ω)

def primeQuotGraded : GradedPMod S N (Poly S N ⧸ primeOf (S := S) y) :=
  quotGraded (primeOf (S := S) y) fun _ hf d => homogeneousComponent_mem_primeOf y hf d

theorem coordGraded_piece_le_secs (n : ℕ) :
    (coordGraded S y).piece (n : ℤ) ≤ (twistSys S y (n : ℤ)).secs := by
  change Submodule.span S _ ≤ _
  rw [Submodule.span_le]
  rintro _ ⟨f, e, hf, he, rfl⟩
  simp only [SetLike.mem_coe, SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem]
  intro I
  exact Submodule.subset_span ⟨f, 1, 0, e, one_mem _, hf, isHomogeneous_one _ _, by simp [he],
    by simp⟩

theorem exists_rep_of_mem_twistMod (n : ℕ) {j : Fin (N + 1)} (hj : y j ≠ 0) {z : Ω}
    (hz : z ∈ twistMod S y (n : ℤ) (singleChart hj)) :
    ∃ (g s : Poly S N) (e : ℕ), s ∈ monos ({j} : Finset (Fin (N + 1))) ∧ s.IsHomogeneous e ∧
      g.IsHomogeneous (e + n) ∧ aeval y g = z * aeval y s := by
  rw [twistMod_eq_span (n : ℤ) (singleChart hj) (Finset.mem_singleton_self j),
    Submodule.mem_span_singleton] at hz
  obtain ⟨b, rfl⟩ := hz
  obtain ⟨f, s, e, hs, hf, hse, hb⟩ := b.2
  have hs0 : aeval y s ≠ 0 := eval_ne_zero_of_mem_monos (singleChart hj) hs
  refine ⟨f * X j ^ n, s, e, hs, hse, hf.mul (isHomogeneous_X_pow j n), ?_⟩
  rw [chartRing_smul_def, hb, map_mul, map_pow, aeval_X, zpow_natCast]
  field_simp

theorem smul_quot_eq_zero {q : Poly S N} (hq : q ∈ primeOf (S := S) y)
    (m : Poly S N ⧸ primeOf (S := S) y) : q • m = 0 := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective m
  change Ideal.Quotient.mk _ (q * f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right f _ hq

theorem locMod_quot_eq_zero {J : Finset (Fin (N + 1))} {i : Fin (N + 1)} (hi : i ∈ J) (hyi : y i = 0)
    (x : LocMod S N (Poly S N ⧸ primeOf (S := S) y) J) : x = 0 := by
  revert x
  refine LocalizedModule.induction_on ?_
  intro m s
  show (LocalizedModule.mk m s : LocalizedModule (monos (S := S) J) _) = 0
  rw [← LocalizedModule.zero_mk s]
  refine LocalizedModule.mk_eq.mpr ⟨⟨X i, X_mem_monos hi⟩, ?_⟩
  rw [smul_zero, smul_zero, Submonoid.smul_def]
  exact smul_quot_eq_zero y
    ((mem_primeOf_of_isHomogeneous y (isHomogeneous_X S i)).mpr (by rw [aeval_X, hyi])) _

theorem locRes_rep_eq {n : ℕ} {z : Ω} {J : Finset (Fin (N + 1))} {a b : Fin (N + 1)}
    (ha : a ∈ J) (hb : b ∈ J) (ga sa gb sb : Poly S N) (ea eb : ℕ)
    (hsa : sa ∈ monos ({a} : Finset (Fin (N + 1)))) (hsb : sb ∈ monos ({b} : Finset (Fin (N + 1))))
    (hsae : sa.IsHomogeneous ea) (hsbe : sb.IsHomogeneous eb)
    (hga : ga.IsHomogeneous (ea + n)) (hgb : gb.IsHomogeneous (eb + n))
    (hza : aeval y ga = z * aeval y sa) (hzb : aeval y gb = z * aeval y sb) :
    locRes (Finset.singleton_subset_iff.mpr ha)
        (LocalizedModule.mk (Ideal.Quotient.mk (primeOf (S := S) y) ga) ⟨sa, hsa⟩ :
          LocMod S N (Poly S N ⧸ primeOf (S := S) y) {a}) =
      locRes (Finset.singleton_subset_iff.mpr hb)
        (LocalizedModule.mk (Ideal.Quotient.mk (primeOf (S := S) y) gb) ⟨sb, hsb⟩ :
          LocMod S N (Poly S N ⧸ primeOf (S := S) y) {b}) := by
  rw [locRes_mk, locRes_mk]
  refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
  rw [one_smul, one_smul, Submonoid.smul_def, Submonoid.smul_def]
  change Ideal.Quotient.mk _ (sb * ga) = Ideal.Quotient.mk _ (sa * gb)
  rw [Ideal.Quotient.eq]
  have h1 : (sb * ga).IsHomogeneous (eb + (ea + n)) := hsbe.mul hga
  have h2 : (sa * gb).IsHomogeneous (eb + (ea + n)) := by
    have := hsae.mul hgb
    rwa [show ea + (eb + n) = eb + (ea + n) by omega] at this
  rw [mem_primeOf_of_isHomogeneous y (h1.sub h2), map_sub, map_mul, map_mul, hza, hzb]
  ring

theorem secs_le_of_surjective (hy : y ≠ 0) (n : ℕ)
    (hsurj : Function.Surjective (toH0 (primeQuotGraded (S := S) y) (n : ℤ))) :
    (twistSys S y (n : ℤ)).secs ≤ (coordGraded S y).piece (n : ℤ) := by
  intro z hz
  have hloc : ∀ j : Fin (N + 1), ∃ w : LocMod S N (Poly S N ⧸ primeOf (S := S) y) {j},
      w ∈ degLoc (primeQuotGraded (S := S) y) (n : ℤ)
        ⟨{j}, Finset.singleton_nonempty j, Finset.subset_univ _⟩ ∧
      ∀ _ : y j ≠ 0, ∃ (g s : Poly S N) (e : ℕ) (hs : s ∈ monos ({j} : Finset (Fin (N + 1)))),
        s.IsHomogeneous e ∧ g.IsHomogeneous (e + n) ∧ aeval y g = z * aeval y s ∧
        w = LocalizedModule.mk (Ideal.Quotient.mk (primeOf (S := S) y) g) ⟨s, hs⟩ := by
    intro j
    by_cases hj : y j = 0
    · exact ⟨0, Submodule.zero_mem _, fun h => absurd hj h⟩
    · have hzj : z ∈ twistMod S y (n : ℤ) (singleChart hj) := by
        have h' := hz
        simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at h'
        exact h' (singleChart hj)
      obtain ⟨g, s, e, hs, hse, hg, hgz⟩ := exists_rep_of_mem_twistMod y n hj hzj
      refine ⟨LocalizedModule.mk (Ideal.Quotient.mk (primeOf (S := S) y) g) ⟨s, hs⟩,
        Submodule.subset_span ⟨Ideal.Quotient.mk (primeOf (S := S) y) g, ⟨s, hs⟩, ((e + n : ℕ) : ℤ), e,
          mem_quotGraded_piece.mpr ⟨g, isWeightedHomogeneous_int_of_isHomogeneous hg, rfl⟩, hse,
          by push_cast; ring, rfl⟩,
        fun _ => ⟨g, s, e, hs, hse, hg, hgz, rfl⟩⟩
  choose w hwdeg hwrep using hloc
  have hcompat : ∀ (J : Finset (Fin (N + 1))) (a b : Fin (N + 1)) (ha : a ∈ J) (hb : b ∈ J),
      locRes (Finset.singleton_subset_iff.mpr ha) (w a) =
        locRes (Finset.singleton_subset_iff.mpr hb) (w b) := by
    intro J a b ha hb
    by_cases h0 : ∃ i ∈ J, y i = 0
    · obtain ⟨i, hi, hyi⟩ := h0
      rw [locMod_quot_eq_zero y hi hyi (locRes (Finset.singleton_subset_iff.mpr ha) (w a)),
        locMod_quot_eq_zero y hi hyi (locRes (Finset.singleton_subset_iff.mpr hb) (w b))]
    · push Not at h0
      obtain ⟨ga, sa, ea, hsa, hsae, hga, hza, hwa⟩ := hwrep a (h0 a ha)
      obtain ⟨gb, sb, eb, hsb, hsbe, hgb, hzb, hwb⟩ := hwrep b (h0 b hb)
      rw [hwa, hwb]
      exact locRes_rep_eq y ha hb ga sa gb sb ea eb hsa hsb hsae hsbe hga hgb hza hzb
  let v : ∀ I : StdCell N, LocMod S N (Poly S N ⧸ primeOf (S := S) y) I.1 := fun I =>
    locRes (Finset.singleton_subset_iff.mpr (I.1.min'_mem I.2.1)) (w (I.1.min' I.2.1))
  have hv : ∀ (I : StdCell N) (a : Fin (N + 1)) (ha : a ∈ I.1),
      v I = locRes (Finset.singleton_subset_iff.mpr ha) (w a) :=
    fun I a ha => hcompat I.1 _ a (I.1.min'_mem I.2.1) ha
  have hvres : ∀ (I J : StdCell N) (h : I.1 ⊆ J.1), locResS I J h (v I) = v J := by
    intro I J h
    change locRes h (v I) = v J
    obtain ⟨a, ha⟩ := I.2.1
    rw [hv I a ha, hv J a (h ha), locRes_locRes]
  let ζ : Cech.Cochain (locSys S N (Poly S N ⧸ primeOf (S := S) y)) 0 := fun I => v I.1
  have hζ : ζ ∈ Cech.cocyDeg (locSys S N (Poly S N ⧸ primeOf (S := S) y))
      (degLoc (primeQuotGraded (S := S) y) (n : ℤ)) locResS 0 := by
    refine Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr
      (Cech.d_zero_of_compat (G := locSys S N (Poly S N ⧸ primeOf (S := S) y)) (ρ := locResS) v hvres), ?_⟩
    rw [Cech.Cdeg, Submodule.mem_pi]
    intro I _
    obtain ⟨a, ha⟩ := I.1.2.1
    change v I.1 ∈ _
    rw [hv I.1 a ha]
    exact locRes_mem_degLoc _ _ ⟨{a}, Finset.singleton_nonempty a, Finset.subset_univ _⟩ I.1 _ (hwdeg a)
  obtain ⟨m, hm⟩ := hsurj (Submodule.Quotient.mk ⟨ζ, hζ⟩)
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (funext h)
  have heq : constCochain (m : Poly S N ⧸ primeOf (S := S) y) = ζ := by
    change Submodule.Quotient.mk (⟨constCochain (m : Poly S N ⧸ primeOf (S := S) y),
      constCochain_mem _ _ _ m.2⟩ : Cech.cocyDeg (locSys S N (Poly S N ⧸ primeOf (S := S) y))
        (degLoc (primeQuotGraded (S := S) y) (n : ℤ)) locResS 0) = _ at hm
    have h2 := (Submodule.Quotient.eq _).mp hm
    rw [Submodule.mem_comap] at h2
    change _ ∈ (⊥ : Submodule S (Cech.Cochain (locSys S N (Poly S N ⧸ primeOf (S := S) y)) 0)) at h2
    rw [Submodule.mem_bot, map_sub] at h2
    exact sub_eq_zero.mp h2
  have hj1 := congrFun heq ⟨⟨{j}, Finset.singleton_nonempty j, Finset.subset_univ _⟩,
    Finset.card_singleton j⟩
  have hvj : v ⟨{j}, Finset.singleton_nonempty j, Finset.subset_univ _⟩ = w j := by
    rw [hv _ j (Finset.mem_singleton_self j), locRes_self]
  obtain ⟨g, s, e, hs, hse, hg, hgz, hwj⟩ := hwrep j hj
  obtain ⟨f, hf, hfm⟩ := mem_quotGraded_piece.mp m.2
  change LocalizedModule.mk (m : Poly S N ⧸ primeOf (S := S) y) 1 =
    v ⟨{j}, Finset.singleton_nonempty j, Finset.subset_univ _⟩ at hj1
  rw [hvj, hwj, ← hfm] at hj1
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp hj1
  rw [one_smul, Submonoid.smul_def, Submonoid.smul_def, Submonoid.smul_def] at hu
  change Ideal.Quotient.mk _ ((u : Poly S N) * (s * f)) = Ideal.Quotient.mk _ ((u : Poly S N) * g) at hu
  rw [Ideal.Quotient.eq, ← mul_sub] at hu
  have hu0 : (u : Poly S N) ∉ primeOf (S := S) y := by
    obtain ⟨eu, heu⟩ := monos_isHomogeneous u.2
    rw [mem_primeOf_of_isHomogeneous y heu]
    exact eval_ne_zero_of_mem_monos (singleChart hj) u.2
  have hsf := (Ideal.IsPrime.mem_or_mem inferInstance hu).resolve_left hu0
  have hfh : f.IsHomogeneous n := isHomogeneous_of_isWeightedHomogeneous_one hf
  have h1 : (s * f - g).IsHomogeneous (e + n) := (hse.mul hfh).sub hg
  rw [mem_primeOf_of_isHomogeneous y h1, map_sub, map_mul, hgz] at hsf
  have hs0 : aeval y s ≠ 0 := eval_ne_zero_of_mem_monos (singleChart hj) hs
  have hzf : z = aeval y f := by
    have h3 : aeval y s * (aeval y f - z) = 0 := by linear_combination hsf
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h hs0
    · exact (sub_eq_zero.mp h).symm
  rw [hzf]
  exact Submodule.subset_span ⟨f, n, hfh, rfl, rfl⟩

end Proof

theorem TwistSections.proof (h : SerreOnto.Statement.{u, u}) : TwistSections.Statement.{u, w} := by
  intro S _ _ Ω _ _ N y hy
  obtain ⟨c₀, hc₀⟩ := h S N (Poly S N ⧸ primeOf (S := S) y) (primeQuotGraded y) (finite_quot _)
  rw [Filter.eventually_atTop]
  refine ⟨c₀.toNat, fun n hn => le_antisymm ?_ (coordGraded_piece_le_secs y n)⟩
  exact secs_le_of_surjective y hy n (hc₀ n ((Int.self_le_toNat c₀).trans (by exact_mod_cast hn)))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsDegLocExact
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

def DegLocExact.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (N : ℕ) (M' M M'' : Type v)
    [AddCommGroup M'] [Module (Poly S N) M'] [Module S M'] [IsScalarTower S (Poly S N) M']
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    [AddCommGroup M''] [Module (Poly S N) M''] [Module S M''] [IsScalarTower S (Poly S N) M'']
    (𝓜' : GradedPMod S N M') (𝓜 : GradedPMod S N M) (𝓜'' : GradedPMod S N M'')
    (f : GradedHom 𝓜' 𝓜) (g : GradedHom 𝓜 𝓜''),
    Function.Injective f.toLin → Function.Surjective g.toLin → Function.Exact f.toLin g.toLin →
    ∀ (c : ℤ) (I : StdCell N),
      (∀ z ∈ degLoc 𝓜 c I, locMap g.toLin I.1 z = 0 →
        ∃ z' ∈ degLoc 𝓜' c I, locMap f.toLin I.1 z' = z) ∧
      (∀ z'' ∈ degLoc 𝓜'' c I, ∃ z ∈ degLoc 𝓜 c I, locMap g.toLin I.1 z = z'')

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsDegreePos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ProjDegreePositive.Statement : Prop :=
  ∀ (F : Type u) [Field F] (ι₀ : Type) [Fintype ι₀] (q : Ideal (MRing (fun _ : Unit => ι₀) F))
    (D : ℕ), IsMultiProjPrime q →
    ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) = ((D + 1 : ℕ) : WithBot ℕ∞) →
    0 < intNum F q (fun _ : Fin D => fun _ => (1 : ℤ))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

