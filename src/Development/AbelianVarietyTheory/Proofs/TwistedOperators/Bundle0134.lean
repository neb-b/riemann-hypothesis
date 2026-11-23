module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0115
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0143
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0047
public import Formalism.LocalRingCardinality.DataParams
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParIffStepGap
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedCharSumsStrictConeVanishEach
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Formalism.JacquetSubsetSums.JacquetSubsetSum

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridParamRegularCardMinusCount
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links Finset
open GlobalTheory.SignedHC

namespace GlobalTheory.PiCounts

variable {G : GridData}

theorem a_injective (hg : 0 < G.ga) : Function.Injective G.a := by
  intro i j h
  have e := G.a_sub_a i j
  rw [h, sub_self] at e
  have hg' : (G.ga : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have : ((j : ℚ) - i) = 0 := by
    rcases mul_eq_zero.1 e.symm with h | h
    · exact h
    · exact absurd h hg'
  have : (j : ℚ) = i := by linarith
  exact_mod_cast this.symm

theorem a_anti {i j : ℕ} (h : i ≤ j) : G.a j ≤ G.a i := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · have : (0 : ℚ) ≤ G.ga := by positivity
    linarith [GlobalTheory.ChiGrid.a_add_le (G := G) h]

theorem card_tops (hg : 0 < G.ga) : G.tops.card = G.m + 1 := by
  rw [GridData.tops, card_image_of_injective _ (a_injective hg), card_range]

theorem card_cloudHalf : G.cloudHalf.card = G.k - 1 := by
  rw [GridData.cloudHalf, card_image_of_injOn, Nat.card_Icc]
  · omega
  · intro i hi j hj h
    have hi := mem_Icc.1 (mem_coe.1 hi)
    have hj := mem_Icc.1 (mem_coe.1 hj)
    have e : G.v i = G.v j := by
      have : (G.v i : ℚ) = G.v j := by simp only [GridData.vHalf] at h; linarith
      exact_mod_cast this
    rcases lt_trichotomy i j with h' | h' | h'
    · exact absurd e (G.v_anti i j hi.1 h' hj.2).ne'
    · exact h'
    · exact absurd e (G.v_anti j i hj.1 h' hi.2).ne

theorem card_Cs' (hm : G.NearMid) (hs : 1 ≤ G.s) (hg : G.s < G.ga) {i : ℕ} (hi : i ≤ G.m) :
    ((Icc (G.m - i + 1) G.m).biUnion G.blockC').card = i * (G.s - 1) := by
  rw [card_biUnion]
  · have : ∀ u ∈ Icc (G.m - i + 1) G.m, (G.blockC' u).card = G.s - 1 := fun u _ => card_block _ _
    rw [sum_congr rfl this, sum_const, Nat.card_Icc, smul_eq_mul]
    congr 1
    omega
  · intro u hu v hv huv
    have hu := mem_Icc.1 (mem_coe.1 hu)
    have hv := mem_Icc.1 (mem_coe.1 hv)
    refine disjoint_left.2 fun x h1 h2 => ?_
    have b1 := GlobalTheory.ChiGrid.blockC'_between hm hs hg (by omega) hu.2 h1
    have b2 := GlobalTheory.ChiGrid.blockC'_between hm hs hg (by omega) hv.2 h2
    rcases lt_or_gt_of_ne huv with h | h <;>
      linarith [GlobalTheory.ChiGrid.a_add_le (G := G) h, b1.1, b1.2, b2.1, b2.2]

theorem card_entries_parPi (hm : G.NearMid) (hs : 1 ≤ G.s) (hg : G.s < G.ga) {i : ℕ} (hi : i ≤ G.m) :
    (GlobalTheory.SignedHC.entries (G.parPi i)).card = G.rankP i := by
  have hg0 : 0 < G.ga := by omega
  have d1 : Disjoint G.tops G.cloudHalf := disjoint_left.2 fun x h1 h2 => by
    obtain ⟨l, hl, rfl⟩ := GridData.mem_tops.1 h1
    linarith [GlobalTheory.ChiGrid.cloudHalf_lt h2, a_anti (G := G) hl]
  have d2 : Disjoint (G.tops ∪ G.cloudHalf) ((Icc (G.m - i + 1) G.m).biUnion G.blockC') :=
    disjoint_left.2 fun x h1 h2 => by
      obtain ⟨u, hu, h2⟩ := mem_biUnion.1 h2
      have hu := mem_Icc.1 hu
      have b := GlobalTheory.ChiGrid.blockC'_between hm hs hg (by omega) hu.2 h2
      rcases mem_union.1 h1 with h1 | h1
      · obtain ⟨l, -, rfl⟩ := GridData.mem_tops.1 h1
        rcases lt_or_ge l u with h | h
        · linarith [GlobalTheory.ChiGrid.a_add_le (G := G) h, b.2]
        · linarith [a_anti (G := G) h, b.1]
      · linarith [GlobalTheory.ChiGrid.cloudHalf_lt h1, a_anti (G := G) hu.2, b.1]
  have := G.two_le_k
  rw [GridData.entries_parPi, GridData.entries_lam, card_union_of_disjoint d2, card_union_of_disjoint d1,
    card_tops hg0, card_cloudHalf, card_Cs' hm hs hg hi, GridData.rankP, G.n_eq]
  omega

theorem card_parPi_le {i : ℕ} (hg : 0 < G.ga) : (G.parPi i).card ≤ (G.m + 1) + (G.k - 1) +
    ((Icc (G.m - i + 1) G.m).biUnion G.blockC').card := by
  rw [GridData.parPi]
  refine (card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · exact card_image_le.trans (card_range _).le
  · exact card_image_le.trans card_cloudHalf.le
  · exact card_image_le

theorem card_parPi (hm : G.NearMid) (hs : 1 ≤ G.s) (hg : G.s < G.ga) {i : ℕ} (hi : i ≤ G.m) :
    (G.parPi i).card = G.rankP i := by
  refine le_antisymm ?_ ((card_entries_parPi hm hs hg hi).symm.le.trans card_image_le)
  have := G.two_le_k
  refine (card_parPi_le (by omega)).trans ?_
  rw [card_Cs' hm hs hg hi, GridData.rankP, G.n_eq]
  omega

theorem isRegular_parPi (hm : G.NearMid) (hs : 1 ≤ G.s) (hg : G.s < G.ga) {i : ℕ} (hi : i ≤ G.m) :
    IsRegular (G.parPi i) :=
  isRegular_iff_card.2 ((card_entries_parPi hm hs hg hi).trans (card_parPi hm hs hg hi).symm)

theorem nMinus_parPi (hg : 0 < G.ga) (i : ℕ) : nMinus (G.parPi i) = (G.m - i + 1) / 2 := by
  have : (G.parPi i).filter (fun x => x.2 = false) =
      (range ((G.m - i + 1) / 2)).image fun c => (G.a (G.m - i - 1 - 2 * c), false) := by
    ext ⟨x, s⟩
    simp only [mem_filter, GridData.mem_parPi, mem_image, mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨l, h1, h2, h3⟩ | ⟨-, h⟩ | ⟨l, -, -, -, h⟩, rfl⟩
      · have h5 : ¬ (G.m - i ≤ l ∨ Even (G.m - i - l)) := by simpa using h3.symm
        rw [Nat.even_iff] at h5
        refine ⟨(G.m - i - l - 1) / 2, by omega, ?_, rfl⟩
        rw [show G.m - i - 1 - 2 * ((G.m - i - l - 1) / 2) = l by omega, h2]
      · simp at h
      · simp at h
    · rintro ⟨c, hc, rfl, rfl⟩
      refine ⟨Or.inl ⟨G.m - i - 1 - 2 * c, by omega, rfl, ?_⟩, rfl⟩
      symm; rw [decide_eq_false_iff_not, Nat.even_iff]; omega
  rw [nMinus, this, card_image_of_injOn, card_range]
  intro c hc c' hc' h
  simp only [coe_range, Set.mem_Iio] at hc hc'
  have h1 := a_injective hg (congrArg Prod.fst h)
  omega

end GlobalTheory.PiCounts

namespace GlobalTheory.Grid

theorem parPi_counts : ∀ (D : D7), HostHyp D → ∀ (τ : D.what₂.Tau) (i : ℕ), i ≤ D.R.m →
    GlobalTheory.SignedHC.IsRegular ((GlobalTheory.Grid.grid D τ).parPi i) ∧ ((GlobalTheory.Grid.grid D τ).parPi i).card = GlobalTheory.Grid.rkP D i ∧
      GlobalTheory.SignedHC.nMinus ((GlobalTheory.Grid.grid D τ).parPi i) = (D.R.m - i + 1) / 2 := by
  intro D _ τ i hi
  have hg : (grid D τ).s < (grid D τ).ga := by
    have := (isLeast_gap D).1.2.1
    show sLen D < gap D
    omega
  have hs : 1 ≤ (grid D τ).s := by show 1 ≤ D.R.r + 6; omega
  have hm := grid_nearMid D τ
  have hi' : i ≤ (grid D τ).m := hi
  refine ⟨GlobalTheory.PiCounts.isRegular_parPi hm hs hg hi', ?_, GlobalTheory.PiCounts.nMinus_parPi (by omega) i⟩
  exact (GlobalTheory.PiCounts.card_parPi hm hs hg hi').trans rfl

end GlobalTheory.Grid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarModulusOfUnitCompletionsAtPlacesEqProdNorm
section
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct Pointwise

namespace GlobalTheory.ModuPiLocal

theorem distribHaarChar_pi {ι : Type} [Fintype ι] (A : ι → Type) [∀ i, CommRing (A i)]
    [∀ i, TopologicalSpace (A i)] [∀ i, IsTopologicalRing (A i)] [∀ i, LocallyCompactSpace (A i)]
    [∀ i, T2Space (A i)] [∀ i, SecondCountableTopology (A i)] (u : (∀ i, A i)ˣ) :
    distribHaarChar (∀ i, A i) u = ∏ i, distribHaarChar (A i) (Units.map (Pi.evalRingHom A i).toMonoidHom u) := by
  classical
  letI : ∀ i, MeasurableSpace (A i) := fun i => borel (A i)
  haveI : ∀ i, BorelSpace (A i) := fun i => ⟨rfl⟩
  let μ : ∀ i, Measure (A i) := fun i => Measure.addHaar
  let S : ∀ i, TopologicalSpace.PositiveCompacts (A i) := fun i => Classical.choice inferInstance
  have h0 : ∀ i, μ i (S i : Set (A i)) ≠ 0 := fun i =>
    (Measure.measure_pos_of_nonempty_interior (μ i) (S i).interior_nonempty).ne'
  have h1 : ∀ i, μ i (S i : Set (A i)) ≠ ⊤ := fun i => (S i).isCompact.measure_lt_top.ne
  have hp : ∀ T : ∀ i, Set (A i), (Measure.pi μ) (Set.univ.pi T) = ∏ i, μ i (T i) := fun T =>
    Measure.pi_pi _ _
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := Measure.pi μ)
    (s := Set.univ.pi fun i => (S i : Set (A i)))
    (by rw [hp]; exact Finset.prod_ne_zero_iff.2 fun i _ => h0 i)
    (by rw [hp]; exact ENNReal.prod_ne_top fun i _ => h1 i) ?_
  have e : u • (Set.univ.pi fun i => (S i : Set (A i))) =
      Set.univ.pi fun i => Units.map (Pi.evalRingHom A i).toMonoidHom u • (S i : Set (A i)) := by
    ext x
    simp only [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_pi, Set.mem_univ, forall_true_left]
    refine forall_congr' fun i => ?_
    rw [← map_inv]
    rfl
  rw [e, hp, hp]
  push_cast
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [distribHaarChar_mul]

end GlobalTheory.ModuPiLocal

namespace GlobalTheory.ModuPiLocal

theorem modu_sPart : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (x : SPart F S), IsUnit x → (modu (SPart F S) x : ℝ) = ∏ v : S, ‖x v‖ := by
  intro F _ _ S x hx
  rw [modu, dite_eq_left hx, distribHaarChar_pi (fun v : S => Fv F v.1), NNReal.coe_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hv : IsUnit (x v) := (Pi.isUnit_iff.1 hx) v
  have h := GlobalTheory.GaugeProdFormula.modu_finite F v.1 (x v) hv.ne_zero
  rw [modu, dite_eq_left hv] at h
  rw [← h]
  congr 2
  ext
  rfl

end GlobalTheory.ModuPiLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterInfiniteOrderAtSplit
section
open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.SplitValue

open WithZero GlobalTheory.CharVal GlobalTheory.Formalism.L2.Col.HostOk

theorem val_map_eq_one {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) {w : HeightOneSpectrum (𝓞 E)}
    (hN : Ideal.absNorm w.asIdeal = p) (hsq : ((p : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2) {z : E}
    (hz : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ w → Q.valuation E z = 1) (φ : E →+* E) (hφ : φ ≠ RingHom.id E) :
    w.valuation E (φ z) = 1 := by
  obtain ⟨Q, hQ⟩ := exists_pull φ w
  refine val_emb_eq_one hQ (hz Q fun e => hφ ?_)
  subst e
  exact GlobalTheory.ringHom_eq_of_comap_eq_unramified_degree_one E E φ (RingHom.id E) Q Q p hp hN hsq hQ (fun r => Iff.rfl)

theorem not_isOfFinOrder_val : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (n : D.R.Psi → ℤ) (p : ℕ), (∀ v, χ.TameAt v) → χ.HasInf (Formalism.L2.Host.embPsi D.host) n → (∀ g, n g ≠ 0) → SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal → ¬ IsOfFinOrder (χ.val w) := by
  intro D χ n p ht hinf hn hp w hw hfin
  classical
  obtain ⟨hN, hsq⟩ := hp.2 w hw
  obtain ⟨M, z, hM, h1, h2, h3⟩ := GlobalTheory.TamePow.exists_pow_locK_mul_inf D.host.E χ
    (GlobalTheory.Mem.UnrAe.unr_ae_and_level _ χ).1.toFinset (GlobalTheory.HeckeProduct.hchar_productRule _ χ)
    (fun v hv => by simpa using hv) ht w (Formalism.L2.Host.unif w)
  obtain ⟨a, ha, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  have h4 : χ.inf z ^ a = 1 := by
    have := congrArg (· ^ a) h3
    simp only [mul_pow, one_pow] at this
    rw [← pow_mul, mul_comm M a, pow_mul] at this
    change χ.val w ^ a = 1 at hpow
    unfold Formalism.L2.Host.HChar.val at hpow
    rwa [hpow, one_pow, one_mul] at this
  have h5 : ((χ.inf z : ℂˣ) : ℂ) ^ 2 =
      D.host.φ₀ (∏ g : D.R.Psi, (D.host.sigmaOf g z / D.host.sigmaOf g (D.host.conj z)) ^ n g) := by
    rw [hinf z, map_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun g _ => ?_
    rw [map_zpow₀, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    congr 1
    have e : D.host.φ₀ (D.host.sigmaOf g (D.host.conj z)) = starRingEnd ℂ (D.host.φ₀ (D.host.sigmaOf g z)) := by
      rw [sigma_conj]
      exact D.host.conjE_apply D.host.φ₀ _
    have e' : Formalism.L2.Host.embPsi D.host g z = D.host.φ₀ (D.host.sigmaOf g z) := rfl
    have h0 : D.host.φ₀ (D.host.sigmaOf g z) ≠ 0 := by simp
    rw [map_div₀, e, e', div_pow, div_eq_div_iff (pow_ne_zero _ (by simpa using h0)) (by simpa using h0), sq, mul_assoc,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have h6 : (∏ g : D.R.Psi, (D.host.sigmaOf g z / D.host.sigmaOf g (D.host.conj z)) ^ n g) ^ a = 1 := by
    apply D.host.φ₀.injective
    rw [map_pow, ← h5, ← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, h4, map_one]
    simp
  have h7 := unit_of_pow (w := w) ha (by rw [h6, map_one])
  have hc : ∀ g : D.R.Psi, w.valuation _ (D.host.sigmaOf g (D.host.conj z)) = 1 := by
    intro g
    refine val_map_eq_one hp.1 hN hsq h2
      ((D.host.sigmaOf g : D.host.E →+* D.host.E).comp (D.host.conj : D.host.E →+* D.host.E)) fun e => ?_
    have := RingHom.congr_fun e D.host.sqrtMinusD
    change D.host.sigmaOf g (D.host.conj D.host.sqrtMinusD) = D.host.sqrtMinusD at this
    rw [conj_b, map_neg, sigmaOf_b] at this
    exact b_ne D.host this.symm
  have hone : D.host.sigmaOf ((1 : D.R.Psi) : D.R.GG) = 1 :=
    map_one (D.host.gal).symm
  have hg : ∀ g : D.R.Psi, g ≠ 1 → w.valuation _ (D.host.sigmaOf g z) = 1 := by
    intro g hg
    refine val_map_eq_one hp.1 hN hsq h2 (D.host.sigmaOf g : D.host.E →+* D.host.E) fun e => hg ?_
    have e1 : D.host.sigmaOf g = D.host.sigmaOf ((1 : D.R.Psi) : D.R.GG) := by
      rw [hone]
      exact AlgEquiv.ext fun x => RingHom.congr_fun e x
    exact Subtype.ext ((D.host.gal).symm.injective e1)
  rw [map_prod, Finset.prod_eq_single 1 (fun g _ h => by rw [map_zpow₀, map_div₀, hg g h, hc g, div_one, one_zpow])
    (by simp), map_zpow₀, map_div₀, hc, div_one, hone, AlgEquiv.one_apply, h1, val_unif, ← exp_nsmul, ← exp_zsmul,
    ← exp_zero, exp_inj] at h7
  simp only [nsmul_eq_mul, smul_eq_mul, mul_eq_zero] at h7
  rcases h7 with h | h | h
  · exact hn 1 h
  · omega
  · omega

end GlobalTheory.SplitValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianParamOppositeSignEntriesDistGeGap
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR.Links Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift (NcGapGt NcGapGe minSig lamS lamT StepGap)
open GlobalTheory.Chain.ItPairCompare

namespace GlobalTheory.Chain.ParOfSizes

section HC

variable {R : Ranks} (P : HCParam R) {h₀ : ℝ}

theorem b_le_of_le {i j : Fin R.m} (h : i.1 ≤ j.1) : P.b i ≤ P.b j := by
  rcases h.lt_or_eq with hlt | heq
  ·
    have h1 := gap_of_lt P hlt
    have h2 := gap_of_le P (le_refl i.1)
    have ht : (0 : ℚ) ≤ R.t := Nat.cast_nonneg _
    linarith
  · exact le_of_eq (congrArg P.b (Fin.ext heq))

theorem le_b_sub (hg : ∀ (i : ℕ) (h : i + 1 < R.m), h₀ ≤ ((P.b ⟨i + 1, h⟩ - P.b ⟨i, by omega⟩ : ℚ) : ℝ))
    {i j : Fin R.m} (h : i.1 < j.1) : h₀ ≤ ((P.b j - P.b i : ℚ) : ℝ) := by
  have hi : i.1 + 1 < R.m := by omega

  have hstep := hg i.1 hi
  have hmono : P.b ⟨i.1 + 1, hi⟩ ≤ P.b j := b_le_of_le P (show i.1 + 1 ≤ j.1 by omega)
  have hq : (P.b ⟨i.1 + 1, hi⟩ - P.b ⟨i.1, by omega⟩ : ℚ) ≤ P.b j - P.b i := by
    have e : (⟨i.1, by omega⟩ : Fin R.m) = i := Fin.ext rfl
    rw [e]
    linarith
  exact hstep.trans (by exact_mod_cast hq)

theorem hermitianParam_oppositeSign_entries_dist_ge_gap (hg : ∀ (i : ℕ) (h : i + 1 < R.m), h₀ ≤ ((P.b ⟨i + 1, h⟩ - P.b ⟨i, by omega⟩ : ℚ) : ℝ))
    (j : ℕ) (x y : Idx R j) (hx : sgn R j x = false) (hy : sgn R j y = true) :
    h₀ ≤ |((val P j x - val P j y : ℚ) : ℝ)| := by
  rw [← Rat.cast_abs]
  rcases x with a | i | a
  · simp [sgn] at hx
  · simp only [sgn, decide_eq_false_iff_not, not_or, not_le] at hx
    obtain ⟨hij, hodd⟩ := hx
    have hi1 : i.1 - 1 < R.m := by omega
    rcases y with c | i2 | ⟨⟨i2, hi2⟩, a⟩
    ·
      have h1 := neg_b_lt_v P c ⟨i.1 - 1, hi1⟩
      have h2 := le_b_sub P hg (i := ⟨i.1 - 1, hi1⟩) (j := i) (show i.1 - 1 < i.1 by omega)
      refine h2.trans (Rat.cast_le.mpr ?_)
      simp only [val]
      rw [abs_sub_comm]
      exact le_abs.mpr (Or.inl (by linarith))
    · simp only [sgn, decide_eq_true_eq] at hy
      rcases lt_trichotomy i2.1 i.1 with h2 | h2 | h2
      · refine (le_b_sub P hg h2).trans (Rat.cast_le.mpr ?_)
        simp only [val]
        rw [abs_sub_comm]
        exact le_abs.mpr (Or.inl (by linarith))
      · exfalso
        rw [h2] at hy
        rcases hy with hy | hy
        · omega
        · exact hodd hy
      · refine (le_b_sub P hg h2).trans (Rat.cast_le.mpr ?_)
        simp only [val]
        exact le_abs.mpr (Or.inl (by linarith))
    ·
      have hi3 : i2.1 + 1 < R.m := by omega
      have g1 := gap_of_lt P (i := i2) (j := ⟨i2.1 + 1, hi3⟩) (show i2.1 < i2.1 + 1 by omega)
      have g2 := le_b_sub P hg (i := ⟨i2.1 + 1, hi3⟩) (j := i) (show i2.1 + 1 < i.1 by omega)
      have ha0 : (0 : ℚ) ≤ (a.1 : ℚ) := Nat.cast_nonneg _
      have ha1 : (a.1 : ℚ) + 1 ≤ R.t := by exact_mod_cast a.2
      refine g2.trans (Rat.cast_le.mpr ?_)
      simp only [val]
      rw [abs_sub_comm]
      exact le_abs.mpr (Or.inl (by linarith))
  · simp [sgn] at hx

theorem le_val_sub (hg : ∀ (i : ℕ) (h : i + 1 < R.m), h₀ ≤ ((P.b ⟨i + 1, h⟩ - P.b ⟨i, by omega⟩ : ℚ) : ℝ))
    (j : ℕ) (c : ℚ) (x y : Idx R j) (h : sgn R j x ≠ sgn R j y) :
    h₀ ≤ |(((val P j x + c) - (val P j y + c) : ℚ) : ℝ)| := by
  rw [add_sub_add_right_eq_sub]
  by_cases hx : sgn R j x = false
  · have hy : sgn R j y = true := by
      cases hy' : sgn R j y
      · exact absurd (hx.trans hy'.symm) h
      · rfl
    exact hermitianParam_oppositeSign_entries_dist_ge_gap P hg j x y hx hy
  · have hx' : sgn R j x = true := by simpa using hx
    have hy : sgn R j y = false := by
      cases hy' : sgn R j y
      · rfl
      · exact absurd (hx'.trans hy'.symm) h
    rw [← neg_sub, Rat.cast_neg, abs_neg]
    exact hermitianParam_oppositeSign_entries_dist_ge_gap P hg j y x hy hx'

end HC

end GlobalTheory.Chain.ParOfSizes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePlaceRelativeNormLeMaxEmbeddingPow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix NumberField IsDedekindDomain
open scoped NNReal TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormInf

theorem infPlace_norm_le {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : InfinitePlace F) (y : E) (c : ℝ≥0) (h : ∀ τ : GlobalTheory.AdelicU.EmbOver E w, ‖τ.1 y‖₊ ≤ c) :
    w (Algebra.norm F y) ≤ (c : ℝ) ^ Module.finrank F E := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  rw [← InfinitePlace.norm_embedding_eq]
  have e : w.embedding (Algebra.norm F y) = ∏ σ : E →ₐ[F] ℂ, σ y := Algebra.norm_eq_prod_embeddings F ℂ y
  rw [e, norm_prod, ← AlgHom.card F E ℂ]
  calc ∏ σ : E →ₐ[F] ℂ, ‖σ y‖ ≤ ∏ _σ : E →ₐ[F] ℂ, (c : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun σ _ => by
          exact_mod_cast h ⟨σ.toRingHom, RingHom.ext σ.commutes⟩
    _ = (c : ℝ) ^ Fintype.card (E →ₐ[F] ℂ) := by rw [Finset.prod_const, Finset.card_univ]

theorem main : ∀ (D : D7) (w : InfinitePlace D.host.F) (y : D.host.E) (c : ℝ≥0), (∀ τ : GlobalTheory.AdelicU.EmbOver D.host.E w, ‖τ.1 y‖₊ ≤ c) → w (Algebra.norm D.host.F y) ≤ (c : ℝ) ^ Module.finrank D.host.F D.host.E :=
  fun D w y c h => infPlace_norm_le w y c h

end GlobalTheory.NormInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenEmbeddingPairOfTuplesToTupleOfPairs
section
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory.ModuLR

theorem zipHom_isOpenEmbedding : ∀ (κ X Y : Type) [Fintype κ] [AddCommGroup X] [TopologicalSpace X]
    [AddCommGroup Y] [TopologicalSpace Y], IsOpenEmbedding (zipHom κ X Y) := by
  intro κ X Y _ _ _ _ _
  let e : ((κ → X) × (κ → Y)) ≃ₜ (κ → X × Y) :=
    { toFun := fun p i => (p.1 i, p.2 i)
      invFun := fun q => (fun i => (q i).1, fun i => (q i).2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_pi fun i =>
        ((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd)
      continuous_invFun :=
        (continuous_pi fun i => continuous_fst.comp (continuous_apply i)).prodMk
          (continuous_pi fun i => continuous_snd.comp (continuous_apply i)) }
  exact e.isOpenEmbedding

end GlobalTheory.ModuLR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedCharSumsStrictConeVanishEachStatement
section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_char_sums_strict_cone_vanish_each : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (r n : ℕ) (E : Fin n → Multiset ((Fin r → kˣ) →* ℂˣ)) (c : Fin n → ℂ), (∀ i, ∀ χ ∈ E i, ∀ t ∈ torusO k (Fin r), χ t = 1) → (∀ t ∈ IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.strictCone ϖ r, ∑ i, c i * IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.charSum (E i) t = 0) → ∀ [DecidableEq ((Fin r → kˣ) →* ℂˣ)] (χ : (Fin r → kˣ) →* ℂˣ), ∑ i, c i * ((E i).count χ : ℂ) = 0 := by
  first | exact @GlobalTheory.ConeCount.sum_count_eq_zero | exact GlobalTheory.ConeCount.sum_count_eq_zero | (intros; apply GlobalTheory.ConeCount.sum_count_eq_zero <;> assumption)
end

