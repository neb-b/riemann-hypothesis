module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1343
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PNearNbhd
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (Plc GLw)
open UpperTheory.Gal.Int.Geo.Pl
open scoped Classical Topology

private lemma v_coe_algebraMap {E : Type} [Field E] [NumberField E] (w : Plc E) (c : 𝓞 E) :
    Valued.v ((algebraMap (𝓞 E) (w.adicCompletionIntegers E) c : w.adicCompletionIntegers E) : w.adicCompletion E)
      = w.intValuation c := by
  have h : ((algebraMap (𝓞 E) (w.adicCompletionIntegers E) c : w.adicCompletionIntegers E) : w.adicCompletion E)
      = algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E c) := rfl
  rw [h]
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := E) w (algebraMap (𝓞 E) E c)
  rw [HeightOneSpectrum.valuation_of_algebraMap] at this
  exact this

private lemma v_le_of_inId {E : Type} [Field E] [NumberField E] (w : Plc E) (e : ℕ)
    (y : w.adicCompletion E) (h : InId w (w.asIdeal ^ e) y) : Valued.v y ≤ WithZero.exp (-(e : ℤ)) := by
  obtain ⟨z, hz, rfl⟩ := h
  refine Submodule.span_induction
    (p := fun (z : w.adicCompletionIntegers E) _ => Valued.v (z : w.adicCompletion E) ≤ WithZero.exp (-(e : ℤ)))
    ?_ ?_ ?_ ?_ (show z ∈ Submodule.span _ _ from hz)
  · rintro _ ⟨c, hc, rfl⟩
    rw [v_coe_algebraMap]
    exact (HeightOneSpectrum.intValuation_le_pow_iff_mem w c e).2 hc
  · simp
  · intro a b _ _ ha hb
    have := Valuation.map_add_le (Valued.v) ha hb
    simpa using this
  · intro a b _ hb
    have ha : Valued.v (a : w.adicCompletion E) ≤ 1 := a.2
    simp only [smul_eq_mul, MulMemClass.coe_mul, map_mul]
    exact mul_le_of_le_one_of_le ha hb

private lemma v_inv_sub_one_le {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Plc E) (g : GLw n w)
    (hg : g ∈ KGL w (n := n)) (γ : WithZero (Multiplicative ℤ))
    (h : ∀ i k, Valued.v ((g.val - 1) i k) ≤ γ) (i k : Fin n) :
    Valued.v (((g⁻¹).val - 1) i k) ≤ γ := by
  have hI := ((GlobalTheory.HenQ.Basic.mem_KGL_iff w g).1 hg).2
  have e : (g⁻¹).val - 1 = -((g⁻¹).val * (g.val - 1)) := by
    rw [mul_sub, mul_one, Units.inv_mul]
    abel
  rw [e, Matrix.neg_apply, Valuation.map_neg, Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le (hI i j) (h j k)

private lemma tendsto_of_v_le {E : Type} [Field E] [NumberField E] (w : Plc E)
    (y : ℕ → w.adicCompletion E) (c : w.adicCompletion E)
    (h : ∀ e : ℕ, Valued.v (y e - c) ≤ WithZero.exp (-(e : ℤ))) : Filter.Tendsto y Filter.atTop (𝓝 c) := by
  rw [← tendsto_sub_nhds_zero_iff, (Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  obtain ⟨m, hm⟩ := exists_pow_lt₀ hlt (Units.mk0 _ hne)
  filter_upwards [Filter.eventually_ge_atTop m] with e he
  rw [Valuation.restrict_lt_iff_lt_embedding]
  refine lt_of_le_of_lt ((h e).trans ?_) hm
  rw [← WithZero.exp_nsmul, WithZero.exp_le_exp]
  simpa using he

private lemma tendsto_mat_of_v_le {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Plc E)
    (M : ℕ → Matrix (Fin n) (Fin n) (w.adicCompletion E))
    (h : ∀ (e : ℕ) i k, Valued.v ((M e - 1) i k) ≤ WithZero.exp (-(e : ℤ))) :
    Filter.Tendsto M Filter.atTop (𝓝 1) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun k => ?_
  exact tendsto_of_v_le w _ _ fun e => h e i k

theorem UpperTheory.Gal.Int.Geo.Pl.nearNbhd_holds :
    UpperTheory.Gal.Int.Geo.Pl.NearNbhd := by
  intro E _ _ n w O hO h1
  by_contra hcon
  push_neg at hcon
  choose e' he g hgK hN hgO using hcon
  have hv : ∀ (e : ℕ) i k, Valued.v (((g e).val - 1) i k) ≤ WithZero.exp (-(e : ℤ)) := by
    intro e i k
    refine (v_le_of_inId w (e' e) _ (hN e i k)).trans ?_
    rw [WithZero.exp_le_exp]
    have := he e
    omega
  have ha : Filter.Tendsto (fun e => (g e).val) Filter.atTop (𝓝 1) := tendsto_mat_of_v_le w _ hv
  have hb : Filter.Tendsto (fun e => ((g e)⁻¹).val) Filter.atTop (𝓝 1) :=
    tendsto_mat_of_v_le w _ fun e => v_inv_sub_one_le w (g e) (hgK e) _ (hv e)
  have ht : Filter.Tendsto g Filter.atTop (𝓝 1) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    exact ha.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hb)
  obtain ⟨e, hE⟩ := (ht.eventually (hO.mem_nhds h1)).exists
  exact hgO e hE
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PProjLev
section
open NumberField IsDedekindDomain GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl

private theorem inId_zero {E : Type} [Field E] [NumberField E] (w : Plc E) (𝔟 : Ideal (𝓞 E)) : InId w 𝔟 0 :=
  ⟨0, zero_mem _, rfl⟩

private theorem nat_not_mem {E : Type} [Field E] [NumberField E] (w : Plc E) {q q' : ℕ} (hq : q.Prime) (hq' : q'.Prime)
    (hne : q' ≠ q) (h : (q' : 𝓞 E) ∈ w.asIdeal) : (q : 𝓞 E) ∉ w.asIdeal := by
  intro h2
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hq').2 hne.symm)
  have h1 : (a : 𝓞 E) * (q : 𝓞 E) + (b : 𝓞 E) * (q' : 𝓞 E) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hab
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (h1 ▸ add_mem (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_left _ _ h)))

private theorem pow_not_mem {E : Type} [Field E] [NumberField E] (w : Plc E) {q : ℕ} (h : (q : 𝓞 E) ∉ w.asIdeal) (e : ℕ) :
    ((q ^ e : ℕ) : 𝓞 E) ∉ w.asIdeal := by
  push_cast
  exact fun h2 => h (w.isPrime.mem_of_pow_mem _ h2)

theorem UpperTheory.Gal.Int.Geo.Pl.projLev_of :
    Dict → PrimeProj → LevBasic → InIdUnit → ProjLev := by
  intro hD hP hL hU E _ _ _ A n p _ S F N v σ q' k hq' hne K₁ hK₁ u hu
  obtain ⟨π, hπ⟩ := hP E n q' hq'
  obtain ⟨g, rfl⟩ := F.surj u
  have hq := σ.atp.prime
  have hNpos : N.1 ≠ 0 := by have := N.2.1; omega
  have hN0 : (N.1 : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hNpos
  obtain ⟨hu1, hu2⟩ := (σ.isLev (F.j g)).1 hu
  have hb : Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} * σ.𝔞 ≠ ⊥ := fun h => hN0 (by
    have := σ.mem
    rw [h] at this
    simpa using this)
  have hg3 := ((hD E A n p S F g).2.2.1 _ hb).1 hu2
  have hg2 := (hD E A n p S F g).2.1.1 hu1
  obtain ⟨-, -, -, -, e, he⟩ := σ.lv
  have hqe : ((σ.q ^ e : ℕ) : 𝓞 E) ∈ σ.𝔞 := by
    have h1 : (σ.q : 𝓞 E) ∈ uId S.D σ.q σ.r := Ideal.subset_span (Set.mem_insert _ _)
    have h2 := Ideal.pow_mem_pow h1 e
    push_cast
    exact he h2
  have hxK1 : F.j (π g) ∈ S.L.KN 1 := (hD E A n p S F (π g)).2.1.2 (fun w hw => by
    by_cases h : (q' : 𝓞 E) ∈ w.asIdeal
    · rw [(hπ g w).1 h]; exact hg2 w hw
    · rw [(hπ g w).2 h, mul_one, mul_inv_cancel]; exact one_mem _)
  have hNb : Ideal.span {(N.1 : 𝓞 E)} ≠ ⊥ := by simpa using hN0
  have hxN : F.j (π g) ∈ S.L.KN N.1 := by
    have lev := (hL p S.D S.G S.L).2.2.1 N.1
    refine (lev _).2 ⟨hxK1, ?_⟩
    refine ((hD E A n p S F (π g)).2.2.1 _ hNb).2 fun w hw i l => ?_
    by_cases h : (q' : 𝓞 E) ∈ w.asIdeal
    · have hc : F.cmp w (π g) = F.cmp w g := by simp only [Frame.cmp, (hπ g w).1 h]
      rw [hc]
      have hqw := nat_not_mem w hq hq' hne h
      have h1 := hg3 w hw i l
      rw [hU E w _ _ ⟨_, hqe, pow_not_mem w hqw e⟩] at h1
      have hspan : Ideal.span {(N.1 : 𝓞 E)} = Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} *
          Ideal.span {((σ.q ^ N.1.factorization σ.q : ℕ) : 𝓞 E)} := by
        rw [Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul, Nat.mul_comm,
          Nat.ordProj_mul_ordCompl_eq_self]
      rw [hspan, hU E w _ _ ⟨_, Ideal.mem_span_singleton_self _, pow_not_mem w hqw _⟩]
      exact h1
    · have hc : F.cmp w (π g) = 1 := by
        simp only [Frame.cmp, (hπ g w).2 h, mul_one, mul_inv_cancel, Units.val_one]
      rw [hc, sub_self]
      exact inId_zero w _
  refine ⟨F.j (π g), hxN, ?_⟩
  rw [← map_inv, ← map_mul]
  have hmul : ∀ w : Plc E, UpperTheory.Gal.CertificateRingHomMap.comp w ((π g)⁻¹ * g) = (UpperTheory.Gal.CertificateRingHomMap.comp w (π g))⁻¹ * UpperTheory.Gal.CertificateRingHomMap.comp w g := fun w => by
    rw [map_mul, map_inv]
  have hspan2 : Ideal.span {((ordCompl[σ.q] N.1 * q' ^ k : ℕ) : 𝓞 E)} * σ.𝔞 =
      (Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} * σ.𝔞) * Ideal.span {((q' ^ k : ℕ) : 𝓞 E)} := by
    rw [Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton]
    ring
  have hq'0 : ((q' ^ k : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hq'.ne_zero)
  have hBot : Ideal.span {((ordCompl[σ.q] N.1 * q' ^ k : ℕ) : 𝓞 E)} * σ.𝔞 ≠ ⊥ := by
    rw [hspan2]
    exact mul_ne_zero hb (by simpa using hq'0)
  refine (hK₁ _).2 ⟨?_, ?_⟩
  · rw [map_mul, map_inv]
    exact mul_mem (inv_mem hxK1) hu1
  · refine ((hD E A n p S F _).2.2.1 _ hBot).2 fun w hw i l => ?_
    by_cases h : (q' : 𝓞 E) ∈ w.asIdeal
    · have hc : F.cmp w ((π g)⁻¹ * g) = 1 := by
        simp only [Frame.cmp, hmul, (hπ g w).1 h, inv_mul_cancel, mul_one, mul_inv_cancel, Units.val_one]
      rw [hc, sub_self]
      exact inId_zero w _
    · have hc : F.cmp w ((π g)⁻¹ * g) = F.cmp w g := by
        simp only [Frame.cmp, hmul, (hπ g w).2 h, inv_one, one_mul]
      rw [hc, hspan2, hU E w _ _ ⟨_, Ideal.mem_span_singleton_self _, pow_not_mem w h k⟩]
      exact hg3 w hw i l
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PStabOf
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL satEig)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc GLw AfQ sim mat comp rat loc lev SameK IsCen Shape IsForm IsKap mOf)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Int.Geo.Pl

private def iT {R : Type} [CommRing R] {n : ℕ} (g : GL (Fin n) R) : GL (Fin n) R :=
  ⟨(g⁻¹).valᵀ, g.valᵀ, by rw [← transpose_mul, Units.mul_inv, transpose_one], by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩

private theorem iT_one {R : Type} [CommRing R] {n : ℕ} : iT (1 : GL (Fin n) R) = 1 := Units.ext (by simp [iT])

private theorem iT_cont {R : Type} [CommRing R] [TopologicalSpace R] {n : ℕ} : Continuous (iT : GL (Fin n) R → GL (Fin n) R) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

private theorem iT_mem {E : Type} [Field E] [NumberField E] {n : ℕ} {w : Plc E} {g : GLw n w} (h : g ∈ KGL w (n := n)) : iT g ∈ KGL w (n := n) := by
  rw [GlobalTheory.HenQ.Basic.mem_KGL_iff] at h ⊢
  exact ⟨fun i j => h.2 j i, fun i j => h.1 j i⟩

private theorem kgl_open {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Plc E) : IsOpen (KGL w (n := n) : Set (GLw n w)) := by
  have h : IsOpen ((w.adicCompletionIntegers E : ValuationSubring _) : Set (w.adicCompletion E)) := Valued.isOpen_valuationSubring _
  have : (KGL w (n := n) : Set (GLw n w)) = (⋂ i, ⋂ j, (fun g : GLw n w => g.val i j) ⁻¹' ((w.adicCompletionIntegers E : ValuationSubring _) : Set (w.adicCompletion E))) ∩
      ⋂ i, ⋂ j, (fun g : GLw n w => (g⁻¹).val i j) ⁻¹' ((w.adicCompletionIntegers E : ValuationSubring _) : Set (w.adicCompletion E)) := by
    ext g
    simp only [SetLike.mem_coe, GlobalTheory.HenQ.Basic.mem_KGL_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [this]
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h.preimage (Units.continuous_val.matrix_elem i j)).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h.preimage (Units.continuous_coe_inv.matrix_elem i j))

private theorem comp_th {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}
    (F : Frame S) (w : Plc E) (k : GUf E n) : comp w (F.th k) = iT (comp w k) := by
  refine Units.ext ?_
  have h1 : (comp w k)⁻¹ = GeneralLinearGroup.map (pLoc E w) (mat k)⁻¹ := (map_inv _ _).symm
  show (mat (F.th k)).val.map (pLoc E w) = ((comp w k)⁻¹).valᵀ
  rw [F.th_mat, h1]
  rfl

theorem stabOf_of (hN : NearNbhd) (hP : PrimeProj) (hD : Dict) : StabOf := by
  intro E _ _ _ A n p hp S F x U w₀ Up V hoff
  have hoff' : ∀ u ∈ V.S, (p : 𝓞 E) ∉ u.asIdeal := by first | exact hoff.1 | exact hoff
  have hcof := Filter.eventually_cofinite.1 F.a_cof
  have hc : ∀ u : Plc E, Continuous fun g : GLw n u => (F.a u)⁻¹ * g * F.a u := fun u =>
    (continuous_const.mul continuous_id).mul continuous_const
  have hO : ∀ u : Plc E, ∃ e : ℕ, ∀ e', e ≤ e' → ∀ g ∈ KGL u (n := n), Near1 u e' g →
      (F.a u)⁻¹ * g * F.a u ∈ KGL u (n := n) ∧ (u ∈ V.S → iT ((F.a u)⁻¹ * g * F.a u) ∈ V.Kw u) := fun u => by
    refine hN E n u (((fun g : GLw n u => (F.a u)⁻¹ * g * F.a u) ⁻¹' (KGL u (n := n) : Set (GLw n u))) ∩
      {g | u ∈ V.S → iT ((F.a u)⁻¹ * g * F.a u) ∈ V.Kw u}) (((kgl_open u).preimage (hc u)).inter ?_) ⟨?_, fun _ => ?_⟩
    · by_cases hu : u ∈ V.S
      · simp only [hu, true_imp_iff]
        exact (V.shape.opn u hu).preimage (iT_cont.comp (hc u))
      · simp [hu]
    · simp [Subgroup.one_mem]
    · simp [iT_one, Subgroup.one_mem]
  choose e he using hO
  have hJ : IsOpen (V.J : Set (GLw n w₀)) := V.Kw0 ▸ V.shape.opn w₀ V.shape.mem
  obtain ⟨e₀, he₀⟩ := hN E n w₀ ((fun g : GLw n w₀ => iT ((F.a w₀)⁻¹ * g * F.a w₀)) ⁻¹' (Subtype.val '' {k : V.J | V.χ k = 1}))
    ((hJ.isOpenMap_subtype_val _ V.ker_open).preimage (iT_cont.comp (hc w₀))) ⟨1, map_one _, by simp [iT_one]⟩
  have hT : ∀ u ∈ V.S ∪ hcof.toFinset, (p : 𝓞 E) ∉ u.asIdeal ∧ (u ∈ V.S ∨ F.a u ∉ KGL u (n := n)) := fun u hu => by
    rw [Finset.mem_union, Set.Finite.mem_toFinset] at hu
    exact ⟨hu.elim (hoff' u) fun h h' => h (F.a_int u p hp.out S.good h'), hu⟩
  refine ⟨V.S ∪ hcof.toFinset, (V.S ∪ hcof.toFinset).sup e + e₀, hT, fun k' hk hn => ?_⟩
  obtain ⟨π, hπ⟩ := hP E n p hp.out
  have hK := (hD E A n p S F k').2.1.1 hk
  have hj : F.j (k' * (π k')⁻¹) = F.j k' := by
    rw [map_mul, map_inv, (F.ker _).2 fun w hw => (hπ k' w).2 hw, inv_one, mul_one]
  have h1 : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (k' * (π k')⁻¹) = 1 := fun w hw => by
    rw [map_mul, map_inv, (hπ k' w).1 hw, mul_inv_cancel]
  have h2 : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal →
      comp w (k' * (π k')⁻¹) = (F.a w)⁻¹ * (F.a w * comp w k' * (F.a w)⁻¹) * F.a w := fun w hw => by
    rw [map_mul, map_inv, (hπ k' w).2 hw]; group
  have h3 := fun u hu => he u _ ((Finset.le_sup (f := e) hu).trans (Nat.le_add_right _ e₀)) _ (hK u (hT u hu).1) (hn u hu)
  have h4 : ∀ w : Plc E, comp w (F.th (k' * (π k')⁻¹)) ∈ KGL w (n := n) := fun w => by
    rw [comp_th]
    refine iT_mem ?_
    by_cases hw : (p : 𝓞 E) ∈ w.asIdeal
    · rw [h1 w hw]; exact Subgroup.one_mem _
    rw [h2 w hw]
    by_cases hu : w ∈ V.S ∪ hcof.toFinset
    · exact (h3 w hu).1
    · rw [Finset.mem_union, Set.Finite.mem_toFinset, not_or, Set.mem_setOf_eq, not_not] at hu
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu.2) (hK w hw)) hu.2
  have hw₀ : w₀ ∈ V.S ∪ hcof.toFinset := Finset.mem_union_left _ V.shape.mem
  obtain ⟨y, hy, hy'⟩ := he₀ _ (Nat.le_add_left _ _) _ (hK w₀ (hT w₀ hw₀).1) (hn w₀ hw₀)
  have h5 : comp w₀ (F.th (k' * (π k')⁻¹)) = y := by rw [comp_th, h2 w₀ (hT w₀ hw₀).1, hy']
  refine ⟨_, hj, CertificateRingHomMap.mem_lev.2 ⟨CertificateRingHomMap.pIntSim_of E n S.facts.pos _ h4, fun w hw => ?_, fun w _ _ => h4 w⟩, h5 ▸ y.2, ?_⟩
  · have hu := Finset.mem_union_left hcof.toFinset hw
    rw [comp_th, h2 w (hT w hu).1]
    exact (h3 w hu).2 hw
  · rw [← hy]
    exact congrArg _ (Subtype.ext h5)

end UpperTheory.Gal.Int.Geo.Pl
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.SpanLePow
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL satEig)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc GLw AfQ sim mat comp rat loc lev SameK IsCen Shape IsForm IsKap mOf)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Int.Geo.Pl

private theorem prime_under {E : Type} [Field E] [NumberField E] (u : Plc E) : ∃ l : ℕ, l.Prime ∧ (l : 𝓞 E) ∈ u.asIdeal := by
  haveI := u.isPrime
  haveI : Finite (𝓞 E ⧸ u.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ u.ne_bot
  refine ⟨ringChar (𝓞 E ⧸ u.asIdeal), CharP.char_is_prime (𝓞 E ⧸ u.asIdeal) _, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
  rw [map_natCast]
  exact (ringChar.spec _ _).2 dvd_rfl

private theorem span_le_pow {R : Type} [CommRing R] {I : Ideal R} {l m e : ℕ} (hl : (l : R) ∈ I) (h : l ^ e ∣ m) :
    Ideal.span {(m : R)} ≤ I ^ e := by
  obtain ⟨c, rfl⟩ := h
  rw [Ideal.span_singleton_le_iff_mem, Nat.cast_mul, Nat.cast_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hl e)

private theorem pow_le_prod {R ι : Type} [CommRing R] (T : Finset ι) (f : ι → Ideal R) (I : Ideal R) (e : ℕ) (h : ∀ u ∈ T, I ≤ f u) :
    I ^ (e * T.card) ≤ ∏ u ∈ T, f u ^ e := by
  rw [pow_mul, ← Finset.prod_const]
  exact Finset.prod_le_prod' fun u hu => Ideal.pow_right_mono (h u hu) e

private theorem prod_le_one {R ι : Type} [CommRing R] (T : Finset ι) (f : ι → Ideal R) (u : ι) (hu : u ∈ T) : ∏ u ∈ T, f u ≤ f u :=
  Ideal.le_of_dvd (Finset.dvd_prod_of_mem f hu)

theorem siteEx_of (hS : Sides) (hD : Dict) (hL : LevBasic) (hSt : StabOf) : SiteEx := by
  intro E _ _ _ A n p hp S F x U w₀ Up V hx hoff Q q hQ c hc hcp
  obtain ⟨T, e, hT, hst⟩ := hSt E A n p S F x U w₀ Up V hoff
  have key : ∀ (𝔟 : Ideal (𝓞 E)) (K : Subgroup S.G.GAf), 𝔟 ≠ ⊥ → (∀ u ∈ T, 𝔟 ≤ u.asIdeal ^ e) → IsLev S.L 𝔟 K →
      ∀ k ∈ K, Stab F V k := fun 𝔟 K h0 hle hK k hk => by
    obtain ⟨k', rfl⟩ := F.surj k
    obtain ⟨h1, h2⟩ := (hK _).1 hk
    refine hst k' h1 fun u hu i j => ?_
    obtain ⟨z, hz, hz'⟩ := ((hD E A n p S F k').2.2.1 𝔟 h0).1 h2 u (hT u hu).1 i j
    exact ⟨z, Ideal.map_mono (hle u hu) hz, hz'⟩
  choose l hl hlu using fun u : Plc E => prime_under u
  obtain ⟨t, ht, htp⟩ := Nat.exists_infinite_primes (Q.sup q + p + 3)
  have hr : ∀ q₀ : ℕ, ∃ r : ℤ, ∀ w ∈ Q, q w = q₀ → (q₀ : ℤ) ∣ r ^ 2 - A.tr * r + A.nm ∧ A.ω - (r : 𝓞 E) ∈ w.asIdeal := fun q₀ => by
    by_cases h : ∃ w ∈ Q, q w = q₀
    · obtain ⟨w', hw', rfl⟩ := h
      obtain ⟨a1, -, a3, a4, -, -⟩ := hQ w' hw'
      obtain ⟨-, -, -, -, -, ⟨r, hr, hω⟩, h7⟩ := hS E A x hx _ a1 a3.1 w' a4
      exact ⟨r, fun w hw h => ⟨hr, ((h7 r hω w).1 ((hQ w hw).2.2.2.2.2 w' hw' h)).2⟩⟩
    · exact ⟨0, fun w hw h' => (h ⟨w, hw, h'⟩).elim⟩
  choose r hr using hr
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = (∏ u ∈ T, l u) * ∏ w ∈ Q, q w := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = c * t * P ^ (e * T.card + e + 1) := ⟨_, rfl⟩
  have hP0 : 0 < P := hP ▸ Nat.mul_pos (Finset.prod_pos fun u _ => (hl u).pos) (Finset.prod_pos fun w hw => (hQ w hw).1.pos)
  have hPp : P.Coprime p := hP ▸ Nat.Coprime.mul_left
    (Nat.Coprime.prod_left fun u hu => (Nat.coprime_primes (hl u) hp.out).2 fun h => (hT u hu).1 (h ▸ hlu u))
    (Nat.Coprime.prod_left fun w hw => (Nat.coprime_primes (hQ w hw).1 hp.out).2 (hQ w hw).2.1)
  have hM0 : 0 < M := hM ▸ Nat.mul_pos (Nat.mul_pos hc htp.pos) (pow_pos hP0 _)
  have htM : t ∣ M := hM ▸ (dvd_mul_left t c).mul_right _
  have hMp : M.Coprime p := hM ▸ (hcp.mul_left ((Nat.coprime_primes htp hp.out).2 (by omega))).mul_left (hPp.pow_left _)
  have hpow : ∀ d k : ℕ, d ∣ P → k ≤ e * T.card + e + 1 → d ^ k ∣ M := fun d k hd hk =>
    hM ▸ ((pow_dvd_pow_of_dvd hd k).trans (pow_dvd_pow P hk)).mul_left _
  have hlP : ∀ u ∈ T, l u ∣ P := fun u hu => hP ▸ (Finset.dvd_prod_of_mem l hu).mul_right _
  have hqP : ∀ w ∈ Q, q w ∣ P := fun w hw => hP ▸ (Finset.dvd_prod_of_mem q hw).mul_left _
  have hM3 : 3 ≤ M := le_trans (by omega) (Nat.le_of_dvd hM0 htM)
  obtain ⟨L1, -, L3, -⟩ := hL p S.D S.G S.L
  let 𝔞 : ℕ → Ideal (𝓞 E) := fun q₀ => ∏ u ∈ T.filter (fun u => (q₀ : 𝓞 E) ∈ u.asIdeal), u.asIdeal ^ e
  have main : ∀ w ∈ Q, ∃ σ : Site S ⟨M, hM3, hMp⟩ w, σ.q = q w ∧ σ.r = r (q w) ∧ σ.𝔞 = 𝔞 (q w) ∧ ∀ k ∈ σ.K₀, Stab F V k := by
    intro w hw
    obtain ⟨a1, a2, a3, a4, a5, -⟩ := hQ w hw
    obtain ⟨r1, r2⟩ := hr _ w hw rfl
    obtain ⟨-, -, s3, -, -, -, s7⟩ := hS E A x hx _ a1 a3.1 w a4
    have hS' : ∀ u ∈ T.filter (fun u => (q w : 𝓞 E) ∈ u.asIdeal), u ∈ V.S := fun u hu =>
      (hT u (Finset.mem_filter.1 hu).1).2.elim id fun h => (h (F.a_int u _ a1 a3 (Finset.mem_filter.1 hu).2)).elim
    obtain ⟨K, hK⟩ := L1 (Ideal.span {((ordCompl[q w] M : ℕ) : 𝓞 E)} * 𝔞 (q w))
    have hmem : ((M : ℕ) : 𝓞 E) ∈ Ideal.span {((ordCompl[q w] M : ℕ) : 𝓞 E)} * 𝔞 (q w) := by
      have h1 : e * (T.filter (fun u => (q w : 𝓞 E) ∈ u.asIdeal)).card ≤ M.factorization (q w) :=
        (a1.pow_dvd_iff_le_factorization hM0.ne').1 (hpow _ _ (hqP w hw)
          ((Nat.mul_le_mul_left e (Finset.card_filter_le _ _)).trans (by omega)))
      have h2 : ((ordProj[q w] M : ℕ) : 𝓞 E) ∈ 𝔞 (q w) := by
        refine pow_le_prod _ (fun u : Plc E => u.asIdeal) (Ideal.span {(q w : 𝓞 E)}) e
          (fun u hu => (Ideal.span_singleton_le_iff_mem _).2 (Finset.mem_filter.1 hu).2) ?_
        refine Ideal.pow_le_pow_right h1 ?_
        rw [Nat.cast_pow]
        exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _
      have h3 := Ideal.mul_mem_mul (Ideal.mem_span_singleton_self ((ordCompl[q w] M : ℕ) : 𝓞 E)) h2
      rwa [← Nat.cast_mul, Nat.mul_comm, Nat.ordProj_mul_ordCompl_eq_self] at h3
    have htq : ¬ q w ∣ t := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq a1 htp).1 h
      have := Finset.le_sup (f := q) hw
      omega
    refine ⟨⟨q w, r (q w), 𝔞 (q w), K, a3, atPrime_of S a1 a2 a3 r1 a4 r2, ⟨?_, (Nat.coprime_ordCompl a1 hM0.ne').symm,
      hMp.coprime_dvd_left (Nat.ordCompl_dvd _ _), ?_, ?_⟩, hK, hmem⟩, rfl, rfl, rfl, key _ K (fun h => ?_) (fun u hu => ?_) hK⟩
    · exact le_trans (by omega) (Nat.le_of_dvd (Nat.ordCompl_pos _ hM0.ne') (Nat.dvd_ordCompl_of_dvd_not_dvd htM htq))
    · refine Ideal.isCoprime_iff_sup_eq.1 (IsCoprime.prod_left fun u hu => IsCoprime.pow_left ?_)
      exact HeightOneSpectrum.isCoprime_of_ne u w fun h => a5.2.1 (h ▸ hS' u hu)
    · refine ⟨_, pow_le_prod _ (fun u : Plc E => u.asIdeal) _ e fun u hu => Ideal.span_le.2 ?_⟩
      have hq := (Finset.mem_filter.1 hu).2
      have := ((s7 _ r2 u).1 ((s3 u hq).resolve_right (a5.2.2.2.1 u (hS' u hu)))).2
      rintro y (rfl | rfl)
      exacts [hq, this]
    · rw [h, Ideal.mem_bot] at hmem
      exact hM0.ne' (Nat.cast_eq_zero.1 hmem)
    · by_cases hq : (q w : 𝓞 E) ∈ u.asIdeal
      · exact Ideal.mul_le_right.trans (prod_le_one _ (fun u : Plc E => u.asIdeal ^ e) u (Finset.mem_filter.2 ⟨hu, hq⟩))
      · refine Ideal.mul_le_left.trans (span_le_pow (hlu u) (Nat.dvd_ordCompl_of_dvd_not_dvd (hpow _ e (hlP u hu) (by omega)) fun h => hq ?_))
        rw [(Nat.prime_dvd_prime_iff_eq a1 (hl u)).1 (a1.dvd_of_dvd_pow h)]
        exact hlu u
  choose σ h1 h2 h3 h4 using main
  refine ⟨⟨M, hM3, hMp⟩, σ, hM ▸ (dvd_mul_right c t).mul_right _, key (Ideal.span {(M : 𝓞 E)}) _ ?_ (fun u hu => ?_) (L3 M),
    fun w hw => ⟨?_, h1 w hw, h4 w hw⟩, fun w hw w' hw' h => ?_⟩
  · rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hM0.ne'
  · exact span_le_pow (hlu u) (hpow _ _ (hlP u hu) (by omega))
  · simpa using hpow _ 1 (hqP w hw) (by omega)
  · rw [h1, h1] at h
    rw [h2, h2, h3, h3, h]
    exact ⟨rfl, rfl⟩

end UpperTheory.Gal.Int.Geo.Pl
end
end

