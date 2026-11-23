module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeIndependenceHarmonic
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IndexRangeMatrix
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueIntegralOfUnitDiscriminant
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.ChartUnram

open ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

theorem isRQ_or_rat (T : CDVR) : TB.IsRQ (R := T.V) T.Fr ∨ Nonempty (Algebra ℚ T.V) := by
  by_cases hN : ∃ N : ℕ, N ≠ 0 ∧ ¬ IsUnit (N : T.V)
  · left
    obtain ⟨N, hN0, hNu⟩ := hN
    refine ⟨IsFractionRing.injective T.V T.Fr, fun y => ?_⟩
    have hNV0 : (N : T.V) ≠ 0 := by exact_mod_cast hN0
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
    obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hNV0 hϖ
    have hϖN : ϖ ∣ (N : T.V) := by
      rcases m with _ | m
      · exact absurd (hm.isUnit_iff.2 (by simp)) hNu
      · exact (dvd_pow_self ϖ (Nat.succ_ne_zero m)).trans hm.symm.dvd
    obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := T.V) y
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hs0 hϖ
    obtain ⟨c, hc⟩ : s ∣ (N : T.V) ^ n := hn.dvd.trans (pow_dvd_pow_of_dvd hϖN n)
    refine ⟨c * a, N ^ n, pow_pos (Nat.pos_of_ne_zero hN0) n, ?_⟩
    have hsK : algebraMap T.V T.Fr s ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)]; exact hs0
    have hcast : ((N ^ n : ℕ) : T.Fr) = algebraMap T.V T.Fr ((N : T.V) ^ n) := by
      rw [map_pow, map_natCast]; push_cast; rfl
    rw [hcast, hc, map_mul, map_mul]
    field_simp
  · right
    push Not at hN
    have hu : ∀ z : nonZeroDivisors ℤ, IsUnit (Int.castRingHom T.V z) := by
      rintro ⟨z, hz⟩
      have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
      have h1 := hN z.natAbs (Int.natAbs_ne_zero.2 hz0)
      rcases Int.natAbs_eq z with h | h
      · show IsUnit ((z : ℤ) : T.V)
        rw [h, Int.cast_natCast]; exact h1
      · show IsUnit ((z : ℤ) : T.V)
        rw [h, Int.cast_neg, Int.cast_natCast]; exact h1.neg
    exact ⟨(IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ) hu).toAlgebra⟩

section Abstract

variable {R k : Type} [CommRing R] [Field k] [Algebra ℚ k] [Algebra R k]
  {d : ℕ} {O : Type} [CommRing O] [StarRing O]

theorem value_mem_rat [Algebra ℚ R] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O]
    (B : FB R d O) (h : PS k 2 d) (hg : B.IsCanonGauge k h) (w0 : O) (m : ℕ)
    {T : Type} [Fintype T] (rr : T → ℕ) (cc : T → T) (hcc : ∀ τ, cc (cc τ) = τ) (isX : T → Prop)
    (hX : ∀ τ, isX τ ∨ isX (cc τ)) (σ : T → O →+* k) (hσ : ∀ τ a, σ (cc τ) a = σ τ (star a))
    (hsep : ∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a))
    (u : (Σ τ : T, Fin (rr τ)) → Fin d → R)
    (hu : ∀ l a, (dAct k B a).mulVec (fun j => algebraMap R k (u l j)) = σ l.1 a • fun j => algebraMap R k (u l j))
    (n : ℕ) (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T rr n) k)
    (hP : P ∈ HaO rr n k (algebraMap R k).range cc isX a)
    (f : Fin n → PS k 1 d) (hf : ∀ b, TB.IntAA (R := R) k (f b)) :
    ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal k h w0 m (f b) (fun ℓ j => algebraMap R k (u ℓ j))
      (MvPolynomial.monomial (colL rr n mo b) 1) ∈ (algebraMap R k).range := by
  classical
  obtain ⟨h0, hh0⟩ := GlobalTheory.canonGauge_exists R d O R B
  obtain ⟨hc, hv⟩ := GlobalTheory.canonGauge_nabVal_baseChange R d O B R k (Algebra.ofId R k) h0 hh0
  have e := GlobalTheory.canonGauge_independence_harmonic R d O k B h _ hg hc T rr cc isX σ hcc hX hσ hsep
    (fun ℓ j => algebraMap R k (u ℓ j)) hu n (MvPolynomial.rename (CVA.lEq (T := T) (r := rr) (n := n)) P)
    (CVA.harm_rename (r := rr) (n := n) cc isX P hP.1.1) w0 m f
  rw [CVA.sum_rename, CVA.sum_rename] at e
  simp only [colM_lEq_colL] at e
  rw [e]
  refine Subring.sum_mem _ fun mo _ => Subring.mul_mem _ (hP.2 mo) (Subring.prod_mem _ fun b _ => ?_)
  choose g hg' using hf b
  have hfb : f b = MvPowerSeries.map (Algebra.ofId R k : R →+* k) (g : PS R 1 d) := by
    ext mm
    exact (hg' mm).symm
  have h1 := hv w0 m g _ u (MvPolynomial.monomial (colL rr n mo b) 1)
  rw [MvPolynomial.map_monomial, map_one, ← hfb] at h1
  exact ⟨_, h1.symm⟩

theorem value_mem_idem (hRQ : TB.IsRQ (R := R) k)
    (B : FB R d O) (h : PS k 2 d) (hg : B.IsCanonGauge k h) (w0 : O) (hw0 : w0 + star w0 = 1) (m : ℕ)
    {T : Type} [Fintype T] (rr : T → ℕ) (cc : T → T) (hcc : ∀ τ, cc (cc τ) = τ) (isX : T → Prop)
    (hX : ∀ τ, isX τ ∨ isX (cc τ)) (hX' : ∀ τ, ¬ (isX τ ∧ isX (cc τ)))
    (σ : T → O →+* k) (hσ : ∀ τ a, σ (cc τ) a = σ τ (star a))
    (hsep : ∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a))
    (hidem : ∀ t : T, ∃ (n : ℕ) (b : Fin n → O) (c : Fin n → R), (∑ i, algebraMap R k (c i) * σ t (b i) = 1) ∧
      ∀ a : O, ∃ m : Fin n → Fin n → ℤ, (∀ i, a * b i = ∑ j, m i j • b j) ∧
        ∀ j, ∑ i, (m i j : k) * algebraMap R k (c i) = σ t a * algebraMap R k (c j))
    (u : (Σ τ : T, Fin (rr τ)) → Fin d → R)
    (hu : ∀ l a, (dAct k B a).mulVec (fun j => algebraMap R k (u l j)) = σ l.1 a • fun j => algebraMap R k (u l j))
    (n : ℕ) (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T rr n) k)
    (hP : P ∈ HaO rr n k (algebraMap R k).range cc isX a)
    (f : Fin n → PS k 1 d) (hf : ∀ b, TB.IntAA (R := R) k (f b)) :
    ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal k h w0 m (f b) (fun ℓ j => algebraMap R k (u ℓ j))
      (MvPolynomial.monomial (colL rr n mo b) 1) ∈ (algebraMap R k).range := by
  classical
  obtain ⟨φ, hφ⟩ := EigA.eigLift_core hRQ B h hg (fun ℓ : (Σ τ : T, Fin (rr τ)) => ℓ.1) σ u hu hidem
  have heig0 : ∀ ℓ ℓ' : (Σ τ : T, Fin (rr τ)), ℓ'.1 ≠ cc ℓ.1 →
      ∑ i, (algebraMap R k (φ ℓ' i) - (TB.sg1 k h).mulVec (fun j => algebraMap R k (u ℓ' j)) i) *
        algebraMap R k (u ℓ i) = 0 := by
    intro ℓ ℓ' hne
    obtain ⟨x, hx⟩ := hsep ℓ.1 (cc ℓ'.1) fun e => hne (by rw [e, hcc])
    rw [hσ] at hx
    exact hφ ℓ ℓ' ⟨x, sub_ne_zero.1 hx.ne_zero⟩
  let c : T → T := fun τ => if isX τ then τ else cc τ
  let s : T → Bool := fun τ => decide (isX τ)
  have hcs : ∀ τ, c (cc τ) = c τ ∧ s (cc τ) ≠ s τ := by
    intro τ
    have hc : cc (cc τ) = τ := hcc τ
    by_cases h1 : isX τ
    · have h2 : ¬ isX (cc τ) := fun h2 => hX' τ ⟨h1, h2⟩
      constructor
      · simp only [c, h1, h2, if_true, if_false, hc]
      · simp [s, h1, h2]
    · have h2 : isX (cc τ) := (hX τ).resolve_left h1
      constructor
      · simp only [c, h1, h2, if_true, if_false]
      · simp [s, h1, h2]
  have hnot : ∀ ℓ ℓ' : (Σ τ : T, Fin (rr τ)), ¬ (c ℓ.1 = c ℓ'.1 ∧ s ℓ.1 ≠ s ℓ'.1) → ℓ'.1 ≠ cc ℓ.1 := by
    intro ℓ ℓ' hn he'
    apply hn
    rw [he']
    exact ⟨(hcs ℓ.1).1.symm, (hcs ℓ.1).2.symm⟩
  have key := chartValJ (R := R) (k := k) hRQ 1
    (Submodule.mem_one.2 ⟨1, map_one _⟩) B h hg w0 hw0 m rr cc hcc isX hX c s hcs u φ (fun _ _ => 0)
    (fun _ _ => Submodule.zero_mem _)
    (fun ℓ ℓ' hne => by simpa only [add_zero] using heig0 ℓ ℓ' hne)
    (fun ℓ ℓ' hn => by
      have h1 := hnot ℓ ℓ' hn
      have h2 : ℓ.1 ≠ cc ℓ'.1 := fun h2 => h1 (by rw [h2]; exact (hcc _).symm)
      simp only [TB.betaH]
      rw [Finset.sum_sub_distrib, heig0 ℓ ℓ' h1]
      have h3 := heig0 ℓ' ℓ h2
      simp only [mul_comm] at h3 ⊢
      rw [h3, sub_self])
    (fun ℓ ℓ' _ => by simp [TB.betaH]) (fun ℓ ℓ' _ => by simp [TB.betaH])
    n a P hP
    (∑ mo ∈ P.support, ∑ b, TB.pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (colL _ n mo b))
    (fun mo hmo => Finset.single_le_sum (f := fun mo => ∑ b, TB.pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1)
      (fun ℓ => s ℓ.1) (colL _ n mo b)) (fun _ _ => Nat.zero_le _) hmo) f hf
  rw [one_pow] at key
  exact Submodule.mem_one.1 key

end Abstract

end GlobalTheory.ChartUnram


open GlobalTheory.ChartUnram ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf in
theorem GlobalTheory.PlaceInt.chBound_zero_of_isUnit_discr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), IsUnit ((NumberField.discr E : ℤ) : T.V) → ∀ (e : ℕ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ChBound C e 0 w n := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C hdisc e w n
  refine GlobalTheory.PlaceInt.chBound_of_columns E H Dw l Xo c hstar T io y C e 0 w n fun k P hP f hf => ?_
  letI := io.toAlgebra
  obtain ⟨B, hBT, hB⟩ := GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound E H Dw l Xo c hstar T io y C
  obtain ⟨hg, -, heig, -⟩ := hB B hBT
  obtain ⟨gF, gA, -, -, -, -, gu⟩ := C.gen.1
  have hu : C.ch.uvec = fun ℓ i => algebraMap T.V T.Fr (C.uvecT ℓ i) := funext fun ℓ => funext fun i => gu ℓ i
  rw [hu] at heig
  have eF : B.FK T.Fr = C.ch.B.FK T.Fr := by
    funext i
    change MvPowerSeries.map _ (B.G.F i) = MvPowerSeries.map _ (C.ch.B.G.F i)
    rw [ChartBiext.toK_self, gF, hBT.1]
  have eA : ∀ a, B.actK T.Fr a = C.ch.B.actK T.Fr a := by
    intro a
    funext i
    change MvPowerSeries.map _ (B.A.act a i) = MvPowerSeries.map _ (C.ch.B.A.act a i)
    rw [ChartBiext.toK_self, gA, hBT.2.1]
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ => star_star τ
  have hσ : ∀ (τ : E →+* ℂ) (a : 𝓞 E), (io.comp (embK c (ComplexEmbedding.conjugate τ))) a =
      (io.comp (embK c τ)) (star a) := by
    intro τ a
    refine congrArg io (Subtype.ext ?_)
    change ((embK c _ a : c.F) : ℂ) = ((embK c _ _ : c.F) : ℂ)
    simp only [embK_coe]
    rw [ComplexEmbedding.conjugate_coe_eq, hstar, H.bar_eq, NumberField.IsCMField.complexEmbedding_complexConj]
  have hsep : ∀ τ τ' : E →+* ℂ, τ ≠ τ' → ∃ a, IsUnit ((io.comp (embK c τ)) a - (io.comp (embK c τ')) a) := by
    intro τ τ' hne
    by_contra hall
    push Not at hall
    apply hne
    refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun x => ?_
    have h0 := hall x
    rw [isUnit_iff_ne_zero, not_not, sub_eq_zero] at h0
    have h2 := congrArg (fun z : c.F => (z : ℂ)) (io.injective h0)
    simpa only [embK_coe] using h2
  have key : ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal T.Fr C.ch.h H.w0 k (f b)
      (fun ℓ j => algebraMap T.V T.Fr (C.uvecT ℓ j)) (MvPolynomial.monomial (colL Dw.mult n mo b) 1) ∈
        (algebraMap T.V T.Fr).range := by
    rcases isRQ_or_rat T with hRQ | ⟨⟨_⟩⟩
    · have hunit : IsUnit (((discr E).natAbs : ℕ) : T.V) := by
        rcases Int.natAbs_eq (discr E) with h | h
        · rwa [h, Int.cast_natCast] at hdisc
        · rw [h, Int.cast_neg, Int.cast_natCast] at hdisc
          simpa using hdisc.neg
      obtain ⟨v, hv⟩ : ∃ v : T.V, algebraMap T.V T.Fr v * (((discr E).natAbs : ℕ) : T.Fr) = 1 := by
        refine ⟨↑hunit.unit⁻¹, ?_⟩
        rw [← map_natCast (algebraMap T.V T.Fr), ← map_mul, hunit.val_inv_mul, map_one]
      have hint : ∀ τ : E →+* ℂ, ∀ x : 𝓞 E, ∃ v : T.V,
          algebraMap T.V T.Fr v = (io.comp (embF c τ)) (algebraMap (𝓞 E) E x) := by
        intro τ x
        obtain ⟨Q, hPm, hPe⟩ := RingOfIntegers.isIntegral_coe x
        refine IsIntegrallyClosed.isIntegral_iff.1 ⟨Q.map (Int.castRingHom T.V), hPm.map _, ?_⟩
        rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap T.V T.Fr).comp (Int.castRingHom T.V))
          ((io.comp (embF c τ)).comp (algebraMap ℤ E)), ← Polynomial.hom_eval₂]
        exact (congrArg _ hPe).trans (map_zero _)
      exact value_mem_idem hRQ B C.ch.h hg H.w0 (by rw [hstar]; exact CVA.cmHostUnit_add_conj_eq_one H) k Dw.mult _ hcc (InPsi H)
        (CVA.inPsi_or H) (CVA.not_inPsi_both H) (fun τ => io.comp (embK c τ)) hσ hsep
        (fun τ => EigA.idem_data (io.comp (embF c τ)) (hint τ) v hv) C.uvecT heig n _ P hP f hf
    · exact value_mem_rat B C.ch.h hg H.w0 k Dw.mult _ hcc (InPsi H)
        (CVA.inPsi_or H) (fun τ => io.comp (embK c τ)) hσ hsep C.uvecT heig n _ P hP f hf
  rw [neg_zero, EReal.coe_zero]
  refine nval_nonneg_of_int e ?_
  unfold FB.nabVal FB.hL at key ⊢
  rw [eF, eA] at key
  rw [hu]
  exact key
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LatticeTrivialAtPrimeIndicesAndUnits
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt GlobalTheory.LatticeIndex

namespace GlobalTheory.TrivLattice

private theorem isAddTorsion_quotient_of_nsmul_mem {G : Type} [AddCommGroup G] (A B : AddSubgroup G) (m : ℕ) (hm : m ≠ 0)
    (h : ∀ b ∈ B, m • b ∈ A) : IsAddTorsion (B ⧸ A.addSubgroupOf B) := by
  intro x
  refine QuotientAddGroup.induction_on x (fun b => ?_)
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨m, Nat.pos_of_ne_zero hm, ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  simpa using h b b.2

theorem relIndex_ne_zero_of_fg {G : Type} [AddCommGroup G] (A B : AddSubgroup G) [AddGroup.FG B] (m : ℕ) (hm : m ≠ 0)
    (h : ∀ b ∈ B, m • b ∈ A) : A.relIndex B ≠ 0 := by
  haveI : AddGroup.FG (B ⧸ A.addSubgroupOf B) :=
    AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective (A.addSubgroupOf B))
  haveI := AddCommGroup.finite_of_fg_isAddTorsion _ (isAddTorsion_quotient_of_nsmul_mem A B m hm h)
  exact AddSubgroup.index_ne_zero_of_finite

section
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem nsmul_mem_of_le {A B : Submodule (𝓞 E) (Fin n → E)} {k : ℕ} (h : Ideal.span {(k : 𝓞 E)} • A ≤ B)
    {v : Fin n → E} (hv : v ∈ A) : k • v ∈ B := by
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact h (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hv)

theorem fg_of_nsmul_mem (A : Submodule (𝓞 E) (Fin n → E)) {k : ℕ} (hk : k ≠ 0) (h : ∀ v ∈ A, k • v ∈ stdLat E n) :
    AddGroup.FG A.toAddSubgroup := by
  let f : (Fin n → E) →ₗ[ℤ] (Fin n → E) := (k : ℤ) • LinearMap.id
  have hf : Function.Injective f := by
    intro x y hxy
    have h0 : (k : ℤ) • (x - y) = 0 := by
      simp only [f, LinearMap.smul_apply, LinearMap.id_apply] at hxy
      rw [smul_sub, hxy, sub_self]
    rcases smul_eq_zero.1 h0 with h0 | h0
    · exact absurd (by exact_mod_cast h0) hk
    · exact sub_eq_zero.1 h0
  let T : Submodule ℤ (Fin n → E) := LinearMap.range ((GlobalTheory.LatticeIndex.incl E n).restrictScalars ℤ)
  have hT : T.FG := by
    simp only [T, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  haveI := isNoetherian_of_fg_of_noetherian T hT
  have hle : (A.restrictScalars ℤ).map f ≤ T := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨u, hu⟩ := GlobalTheory.LatticeIndex.mem_std.1 (h v hv)
    refine ⟨u, ?_⟩
    simp only [f, LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul]
    exact hu
  have hA : (A.restrictScalars ℤ).FG :=
    Submodule.fg_of_fg_map_injective f hf (Submodule.FG.of_le_of_isNoetherian hle)
  exact (AddGroup.fg_iff_addSubgroup_fg _).2 ((Submodule.fg_iff_addSubgroup_fg _).1 hA)

theorem index_part (Λ : GenLat E n) (N M ℓ k : ℕ) (hL : Λ.LevOK N M) (hl : ℓ.Prime) (hk : Nat.Coprime k ℓ)
    (h1 : ∀ v ∈ Λ.La, k • v ∈ stdLat E n) (r : ℕ) :
    (Λ.zCard N r).factorization ℓ = (Λ.mIdx N r).factorization ℓ ∧ Λ.mIdx N r ≠ 0 := by
  obtain ⟨hNodd, -, hNle⟩ := hL
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hl.ne_one ((Nat.coprime_zero_left ℓ).1 hk)
  have memLn : ∀ x, x ∈ Λ.Ln ↔ x ∈ Λ.La ∧ x ∈ stdLat E n := fun x => by
    unfold GenLat.Ln
    exact Submodule.mem_inf
  have hS : (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup ≤ Λ.Ln.toAddSubgroup := fun x hx => hNle hx
  have hLn : Λ.Ln.toAddSubgroup ≤ Λ.La.toAddSubgroup := fun x hx => ((memLn x).1 hx).1
  haveI := fg_of_nsmul_mem Λ.La hk0 h1
  haveI := fg_of_nsmul_mem Λ.Ln one_ne_zero (fun v hv => by rw [one_smul]; exact ((memLn v).1 hv).2)
  have hkLn : ∀ b ∈ Λ.La.toAddSubgroup, k • b ∈ Λ.Ln.toAddSubgroup := fun b hb =>
    (memLn _).2 ⟨nsmul_mem hb k, h1 b hb⟩
  have ha : Λ.Ln.toAddSubgroup.relIndex Λ.La.toAddSubgroup ≠ 0 :=
    relIndex_ne_zero_of_fg _ _ k hk0 hkLn
  have hnd := GlobalTheory.LatticeIndex.not_dvd_relIndex _ _ k ℓ hl hk ha hkLn
  have hb : (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.Ln.toAddSubgroup ≠ 0 := by
    refine relIndex_ne_zero_of_fg _ _ N hNodd.pos.ne' (fun b hb => ?_)
    show N • b ∈ Ideal.span {(N : 𝓞 E)} • stdLat E n
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) ((memLn b).1 hb).2
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ hS hLn
  change ((Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup ^ r).factorization ℓ =
      ((Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.Ln.toAddSubgroup ^ r).factorization ℓ ∧
    (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.relIndex Λ.Ln.toAddSubgroup ^ r ≠ 0
  refine ⟨?_, pow_ne_zero _ hb⟩
  rw [← hmul, mul_pow, Nat.factorization_mul (pow_ne_zero _ hb) (pow_ne_zero _ ha)]
  simp [Nat.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hnd]

theorem detSet_max {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (w : Valuation E Γ)
    (hw : ∀ r : 𝓞 E, w (algebraMap (𝓞 E) E r) ≤ 1) (A : Submodule (𝓞 E) (Fin n → E)) {k : ℕ} (hk : w (k : E) = 1)
    (h1 : ∀ v ∈ A, k • v ∈ stdLat E n) (h2 : ∀ v ∈ stdLat E n, k • v ∈ A) :
    (∀ y ∈ detSet A, w y ≤ 1) ∧ ∃ y ∈ detSet A, w y = 1 := by
  constructor
  · rintro y ⟨v, hv, rfl⟩
    have hc := GlobalTheory.LatticeIndex.det_cols (m := (1 : Matrix (Fin n) (Fin n) E)) (a := (k : E)) (v := v)
      (u := fun i => k • v i) (fun i => by rw [Matrix.one_mulVec, Nat.cast_smul_eq_nsmul])
    obtain ⟨r, hr⟩ := GlobalTheory.LatticeIndex.det_std (u := fun i => k • v i) (fun i => h1 _ (hv i))
    rw [Matrix.det_one, _root_.one_mul, ← hr] at hc
    have hwc := congrArg w hc
    rw [map_mul, map_pow, hk, one_pow, _root_.one_mul] at hwc
    rw [hwc]
    exact hw r
  · refine ⟨(k : E) ^ n, ⟨fun i => k • (Pi.single i 1 : Fin n → E),
      fun i => h2 _ (GlobalTheory.LatticeIndex.single_std i), ?_⟩, ?_⟩
    · have hc := GlobalTheory.LatticeIndex.det_cols (m := (1 : Matrix (Fin n) (Fin n) E)) (a := (k : E))
        (v := fun i => (Pi.single i 1 : Fin n → E)) (u := fun i => k • (Pi.single i 1 : Fin n → E))
        (fun i => by rw [Matrix.one_mulVec, Nat.cast_smul_eq_nsmul])
      beta_reduce at hc
      rw [GlobalTheory.LatticeIndex.det_single, _root_.mul_one, Matrix.det_one, _root_.one_mul] at hc
      exact hc
    · rw [map_pow, hk, one_pow]

private theorem valuation_beta_of_lattice_commensurable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (c : Coeff l) {n : ℕ} (Λ : GenLat E n) (k : ℕ) (h1 : ∀ v ∈ Λ.La, k • v ∈ stdLat E n)
    (h2 : ∀ v ∈ stdLat E n, k • v ∈ Λ.La) {K : Type} [Field K] (io : c.F →+* K) (v0 : Valuation K (WithZero (Multiplicative ℤ)))
    (hint : ∀ x : K, IsIntegral ℤ x → v0 x ≤ 1) (hnat : v0 (k : K) = 1) (β : c.F)
    (hB : BetaIs (Dw := Dw) c Λ β) : v0 (io β) = 1 := by
  let w : Valuation c.F (WithZero (Multiplicative ℤ)) := v0.comap io
  have hwR : ∀ r : 𝓞 c.F, w (algebraMap (𝓞 c.F) c.F r) ≤ 1 := fun r =>
    hint _ ((NumberField.RingOfIntegers.isIntegral_coe r).map io.toIntAlgHom)
  have hA : ∀ A : Submodule (𝓞 E) (Fin n → E), (∀ v ∈ A, k • v ∈ stdLat E n) → (∀ v ∈ stdLat E n, k • v ∈ A) →
      ∀ τ : E →+* ℂ, GlobalTheory.LatticeIndex.HasMax w (idealAt c A τ) 1 := by
    intro A hA1 hA2 τ
    let wτ : Valuation E (WithZero (Multiplicative ℤ)) := w.comap (embF c τ)
    have hwE : ∀ r : 𝓞 E, wτ (algebraMap (𝓞 E) E r) ≤ 1 := fun r =>
      hint _ ((NumberField.RingOfIntegers.isIntegral_coe r).map (io.comp (embF c τ)).toIntAlgHom)
    have hkE : wτ (k : E) = 1 := by
      simp only [wτ, w, Valuation.comap_apply, map_natCast]
      exact hnat
    have hm := detSet_max wτ hwE A hkE hA1 hA2
    unfold idealAt
    refine GlobalTheory.LatticeIndex.hasMax_span hwR ?_ ?_
    · rintro _ ⟨d, hd, rfl⟩
      exact hm.1 d hd
    · obtain ⟨d, hd, hd1⟩ := hm.2
      exact ⟨_, ⟨d, hd, rfl⟩, hd1⟩
  have hprod : ∀ A : Submodule (𝓞 E) (Fin n → E), (∀ v ∈ A, k • v ∈ stdLat E n) → (∀ v ∈ stdLat E n, k • v ∈ A) →
      GlobalTheory.LatticeIndex.HasMax w (∏ τ : E →+* ℂ, idealAt c A τ ^ Dw.mult τ) 1 := by
    intro A hA1 hA2
    have := GlobalTheory.LatticeIndex.hasMax_prod hwR Finset.univ (fun τ => idealAt c A τ ^ Dw.mult τ) (fun _ => 1)
      (fun τ => by simpa using (hA A hA1 hA2 τ).pow hwR (Dw.mult τ))
    simpa using this
  have memLn : ∀ x, x ∈ Λ.Ln ↔ x ∈ Λ.La ∧ x ∈ stdLat E n := fun x => by
    unfold GenLat.Ln
    exact Submodule.mem_inf
  have hLa := hprod Λ.La h1 h2
  have hLn := hprod Λ.Ln (fun v hv => nsmul_mem ((memLn v).1 hv).2 k)
    (fun v hv => (memLn _).2 ⟨h2 v hv, nsmul_mem hv k⟩)
  have hβ : GlobalTheory.LatticeIndex.HasMax w (𝓞 c.F ∙ β) (w β) :=
    GlobalTheory.LatticeIndex.hasMax_span hwR (by rintro y rfl; exact le_rfl) ⟨β, Set.mem_singleton β, rfl⟩
  have hm := hβ.mul hLa
  unfold BetaIs at hB
  rw [hB] at hm
  have hu := hm.unique hLn
  rw [_root_.mul_one] at hu
  exact hu

end

theorem trivAt_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.Unimod → Λ.LevOK N M → ℓ.Prime → Λ.TrivAt ℓ → (Λ.zCard N (Dw.p + Dw.q)).factorization ℓ = (Λ.mIdx N (Dw.p + Dw.q)).factorization ℓ ∧ Λ.mIdx N (Dw.p + Dw.q) ≠ 0 ∧ ∀ (T : CDVR) (io : c.F →+* T.Fr), ¬ IsUnit (ℓ : T.V) → (∀ β : c.F, β ≠ 0 → BetaIs (Dw := Dw) c Λ β → vV T.V (io β) = 0) ∧ ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w → MvPolynomial.map io P ∈ FFV (Dw := Dw) T w n := by
  intro E _ _ _ H Dw l c n Λ N M ℓ _ hL hl hT
  obtain ⟨k, hk, hk1, hk2⟩ := hT
  have h1 : ∀ v ∈ Λ.La, k • v ∈ stdLat E n := fun v hv => nsmul_mem_of_le hk1 hv
  have h2 : ∀ v ∈ stdLat E n, k • v ∈ Λ.La := fun v hv => nsmul_mem_of_le hk2 hv
  obtain ⟨hidx, hne⟩ := index_part Λ N M ℓ k hL hl hk h1 (Dw.p + Dw.q)
  refine ⟨hidx, hne, fun T io hlT => ⟨?_, ?_⟩⟩
  · intro β _ hB
    have key : valV T.V (io β) = 1 := by
      have hint : ∀ x : T.Fr, IsIntegral ℤ x → valV T.V x ≤ 1 := fun x hx => GlobalTheory.LatticeIndex.valV_integral T hx
      have hnat := GlobalTheory.LatticeIndex.valV_nat T hk hlT
      unfold valV at hint hnat ⊢
      refine valuation_beta_of_lattice_commensurable c Λ k h1 h2 io _ ?_ ?_ β hB
      · intro x hx
        refine hint x ?_
        convert hx
        all_goals first
          | rfl
          | exact rfl
          | exact Subsingleton.elim _ _
          | (apply Algebra.algebra_ext; intro r; simp)
      · first
          | exact hnat
          | convert hnat using 2
    unfold vV
    rw [key]
    simp
  · intro w P hP
    have hunit : IsUnit (k : T.V) := by
      obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hk).map (Int.castRingHom T.V)
      have hab' : a * (k : T.V) + b * (ℓ : T.V) = 1 := by simpa using hab
      rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab' with h | h
      · exact isUnit_of_mul_isUnit_right h
      · exact absurd (isUnit_of_mul_isUnit_right h) hlT
    have hunitary : ∀ i j : Fin n, ∑ b, IsCMField.complexConj E ((1 : Matrix (Fin n) (Fin n) E) b i) *
        (1 : Matrix (Fin n) (Fin n) E) b j = if i = j then 1 else 0 := by
      intro i j
      rw [Finset.sum_eq_single i]
      · simp [Matrix.one_apply]
      · intro b _ hb
        simp [Matrix.one_apply_ne hb]
      · intro h
        exact absurd (Finset.mem_univ i) h
    obtain ⟨hmem, hone, -⟩ := GlobalTheory.PushIntegral.map_pushL_mem_FFV E H Dw l c n Λ w P hP T io k 1 hunit hunitary
      (fun v hv => by rw [Matrix.one_mulVec, Nat.cast_smul_eq_nsmul]; exact h1 v hv)
    rwa [hone] at hmem

end GlobalTheory.TrivLattice
end
end

