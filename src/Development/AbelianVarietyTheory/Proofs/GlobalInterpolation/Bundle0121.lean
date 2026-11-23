module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDualBasisOfUnimodularLatticeAtPrime
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0117
public import Formalism.GL3MeanSquares.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0069
public import Development.AutomorphicArithmetic.ShortNorms.Primes
public import Development.AutomorphicArithmetic.ShortNorms.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSummableMajorantRationalVectorsLocallyUnif
section
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

noncomputable section
namespace GlobalTheory.SumMaj
open scoped Classical
variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem re_add (x y : Ainf F) (w : InfinitePlace F) : re (x + y) w = re x w + re y w := by
  show (InfinitePlace.Completion.extensionEmbedding w (x w + y w)).re = _
  rw [map_add (f := _), Complex.add_re]; rfl

theorem abs_re_algebraMap (hF : IsTotallyReal F) (x : F) (w : InfinitePlace F) :
    |re (algebraMap F (Ainf F) x) w| = w x := by
  unfold re
  have hw : w.IsReal := hF.isReal w
  rw [InfiniteAdeleRing.algebraMap_apply]
  rw [InfinitePlace.Completion.extensionEmbedding_coe]
  rw [← InfinitePlace.embedding_of_isReal_apply hw, Complex.ofReal_re]
  first
  | (rw [← Real.norm_eq_abs]; exact InfinitePlace.norm_embedding_of_isReal hw x)
  | simpa [Real.norm_eq_abs] using InfinitePlace.norm_embedding_of_isReal hw x

theorem sz_nonneg (u : Fin N → AF F) : 0 ≤ sz u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem sz_sub_le (u y : Fin N → AF F) : sz u - sz y ≤ sz (u + y) := by
  unfold sz
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun w _ => ?_
  have h : re (inf (u + y) l) w = re (inf u l) w + re (inf y l) w := by
    rw [← re_add]; congr 1
  rw [h]
  have := abs_sub_abs_le_abs_sub (re (inf u l) w) (-(re (inf y l) w))
  simpa [abs_neg, sub_neg_eq_add] using this

theorem continuous_sz : Continuous (sz : (Fin N → AF F) → ℝ) := by
  unfold sz
  refine continuous_finsetSum _ fun l _ => continuous_finsetSum _ fun w _ => ?_
  have h1 : Continuous fun u : Fin N → AF F => inf u l := by
    show Continuous fun u : Fin N → AF F => (u l).1
    exact continuous_fst.comp (continuous_apply l)
  have h2 : Continuous fun x : Ainf F => re x w :=
    Complex.continuous_re.comp ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      (continuous_apply w))
  exact continuous_abs.comp (h2.comp h1)

theorem continuous_fin : Continuous (fin : (Fin N → AF F) → Fin N → Af F) := by
  refine continuous_pi fun l => ?_
  show Continuous fun u : Fin N → AF F => (u l).2
  exact continuous_snd.comp (continuous_apply l)

theorem fin_add (u y : Fin N → AF F) : fin (u + y) = fin u + fin y := by
  funext l; simp [fin, map_add (f := _)]

theorem inf_rat (ξ : Fin N → F) (l : Fin N) : inf (rat ξ) l = algebraMap F (Ainf F) (ξ l) := by
  simp [inf, rat]

theorem fin_rat (ξ : Fin N → F) (l : Fin N) : fin (rat ξ) l = algebraMap F (Af F) (ξ l) := by
  simp [fin, rat]

theorem norm_le_sz (hF : IsTotallyReal F) (ξ : Fin N → F) :
    ‖(fun l => mixedEmbedding F (ξ l))‖ ≤ sz (rat ξ) := by
  refine (pi_norm_le_iff_of_nonneg (sz_nonneg _)).2 fun l => ?_
  classical
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun w _ => ?_
  rw [mixedEmbedding.normAtPlace_apply]
  unfold sz
  calc w (ξ l) = |re (inf (rat ξ) l) w| := by rw [inf_rat, abs_re_algebraMap hF]
    _ ≤ ∑ w', |re (inf (rat ξ) l) w'| :=
        Finset.single_le_sum (f := fun w' => |re (inf (rat ξ) l) w'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ w)
    _ ≤ _ := Finset.single_le_sum (f := fun l' => ∑ w', |re (inf (rat ξ) l') w'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ l)

theorem finrank_le_of_discrete {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] : Module.finrank ℤ L ≤ Module.finrank ℝ E := by
  let E' := Submodule.span ℝ (L : Set E)
  let L' : Submodule ℤ E' := ZLattice.comap ℝ L E'.subtype
  haveI : DiscreteTopology L' :=
    ZLattice.comap_discreteTopology _ _ (by fun_prop) Subtype.val_injective
  haveI : IsZLattice ℝ L' :=
    ⟨Submodule.map_injective_of_injective E'.subtype_injective (by simp [E', L'])⟩
  let e : L' ≃ₗ[ℤ] L := Submodule.comapSubtypeEquivOfLe (p := L) (q := E'.restrictScalars ℤ)
    Submodule.subset_span
  rw [← e.finrank_eq, ZLattice.rank ℝ L']
  exact Submodule.finrank_le E'

end GlobalTheory.SumMaj

namespace GlobalTheory.SumMaj
open scoped Classical

theorem summable_majorant : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F →
    ∀ K : Set (Fin N → Af F), IsCompact K → ∃ k : ℕ, ∀ ω : Set (Fin N → AF F), IsCompact ω →
      ∃ c : (Fin N → F) → ℝ, Summable c ∧ (∀ ξ, 0 ≤ c ξ) ∧
        ∀ ξ, ∀ y ∈ ω, fin (rat ξ + y) ∈ K → 1 ≤ c ξ * (1 + sz (rat ξ + y)) ^ k := by
  intro F _ _ N hF K hK
  refine ⟨Module.finrank ℝ (Fin N → mixedEmbedding.mixedSpace F) + 1, fun ω hω => ?_⟩
  set k := Module.finrank ℝ (Fin N → mixedEmbedding.mixedSpace F) + 1 with hk
  obtain ⟨B, hB⟩ := hω.bddAbove_image (continuous_sz (F := F) (N := N)).continuousOn
  set B0 := max B 0 with hB0
  have hB0n : 0 ≤ B0 := le_max_right _ _
  have hszB : ∀ y ∈ ω, sz y ≤ B0 := fun y hy => (hB ⟨y, hy, rfl⟩).trans (le_max_left _ _)
  set K' : Set (Fin N → Af F) := (fun p : (Fin N → Af F) × (Fin N → Af F) => p.1 - p.2) '' (K ×ˢ (fin '' ω))
    with hK'
  have hK'c : IsCompact K' :=
    (hK.prod (hω.image continuous_fin)).image (continuous_fst.sub continuous_snd)
  obtain ⟨M, hM0, hM⟩ := GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact F hK'c
  set S : Set (Fin N → F) := {ξ | fin (rat ξ) ∈ K'} with hS
  set c : (Fin N → F) → ℝ := S.indicator fun ξ => (1 + B0) ^ k / (1 + sz (rat ξ)) ^ k with hc
  have hc0 : ∀ ξ, 0 ≤ c ξ := fun ξ =>
    Set.indicator_nonneg (fun ξ _ => div_nonneg (pow_nonneg (by linarith) _)
      (pow_nonneg (by linarith [sz_nonneg (rat ξ)]) _)) ξ
  refine ⟨c, ?_, hc0, fun ξ y hy hξ => ?_⟩
  · haveI := GlobalTheory.WeilM.discreteTopology_denomLattice F (Fin N) hM0
    set L := GlobalTheory.WeilM.denomLattice F (Fin N) M with hL
    have memL : ∀ ξ ∈ S, (fun i => mixedEmbedding F (ξ i)) ∈ L := by
      intro ξ hξ i
      obtain ⟨y, hy⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((M : F) * ξ i)
        fun v => by
          rw [map_mul, map_natCast]
          have := hM _ hξ i v
          rwa [fin_rat] at this
      refine ⟨y, ?_⟩
      have h2 := congrArg (mixedEmbedding F) hy
      rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
      exact h2.symm
    let j : S → L := fun ξ => ⟨_, memL ξ.1 ξ.2⟩
    have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    have hkL : Module.finrank ℤ L < k := Nat.lt_succ_of_le (finrank_le_of_discrete L)
    have hg : Summable fun z : L => ((1 + ‖z‖) ^ k)⁻¹ := by
      refine Summable.of_norm_bounded_eventually (ZLattice.summable_norm_pow_inv L k hkL) ?_
      refine (Set.finite_singleton (0 : L)).subset fun z hz => ?_
      by_contra h0
      apply hz
      show ‖((1 + ‖z‖) ^ k)⁻¹‖ ≤ ‖z‖⁻¹ ^ k
      have hz0 : 0 < ‖z‖ := norm_pos_iff.2 h0
      rw [Real.norm_of_nonneg (inv_nonneg.2 (pow_nonneg (by positivity) _)), inv_pow]
      exact inv_anti₀ (pow_pos hz0 _) (pow_le_pow_left₀ hz0.le (by linarith) _)
    refine ((Subtype.val_injective (p := fun ξ => ξ ∈ S)).summable_iff ?_).1 ?_
    · intro ξ hξ
      have : ξ ∉ S := fun h => hξ ⟨⟨ξ, h⟩, rfl⟩
      exact Set.indicator_of_notMem this _
    · refine Summable.of_nonneg_of_le (fun ξ => hc0 _) (fun ξ => ?_) ((hg.comp_injective hj).mul_left ((1 + B0) ^ k))
      show c ξ.1 ≤ (1 + B0) ^ k * ((1 + ‖j ξ‖) ^ k)⁻¹
      rw [hc, Set.indicator_of_mem ξ.2, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by linarith) _)
      have hn : ‖j ξ‖ ≤ sz (rat ξ.1) := norm_le_sz hF ξ.1
      exact inv_anti₀ (pow_pos (by positivity) _) (pow_le_pow_left₀ (by positivity) (by linarith) _)
  · have hS' : ξ ∈ S := by
      refine ⟨(fin (rat ξ + y), fin y), ⟨hξ, y, hy, rfl⟩, ?_⟩
      simp [fin_add]
    rw [hc, Set.indicator_of_mem hS']
    have hs0 := sz_nonneg (rat ξ)
    have ht0 := sz_nonneg (rat ξ + y)
    have hst := sz_sub_le (rat ξ) y
    have hy0 := hszB y hy
    have key : 1 + sz (rat ξ) ≤ (1 + B0) * (1 + sz (rat ξ + y)) := by nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos (by linarith) _), one_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) key _

end GlobalTheory.SumMaj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MomentMeasureNormLeOneIffLatticeIntegral
section
open GlobalTheory.MomN Formalism.L2.Ker.JMB
open scoped ComplexConjugate

noncomputable section
namespace GlobalTheory.MomN.Bridge

variable {g : ℕ}

theorem im_hf_int (S : Setup g) (hOk : S.Ok) (x y : Fin g → ℂ) (hx : x ∈ S.La) (hy : y ∈ S.La) :
    ∃ z : ℤ, (hf S.Hm x y).im = z := by
  obtain ⟨hdp, -, -, -, -, -, hbeta, -⟩ := hOk
  obtain ⟨u, v, huv⟩ := hbeta x hx y hy
  have h := congrArg Complex.im huv
  simp [beta, w0, rtd, Complex.mul_im] at h
  have hd : (0 : ℝ) < Real.sqrt S.d := Real.sqrt_pos.2 (by exact_mod_cast hdp.pos)
  refine ⟨v, ?_⟩
  field_simp at h
  nlinarith [h]

theorem hf_smul_left (Hm : Matrix (Fin g) (Fin g) ℂ) (s : ℕ) (x t : Fin g → ℂ) :
    hf Hm ((s : ℂ) • x) t = hf Hm x ((s : ℂ) • t) := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hf_zero_right (Hm : Matrix (Fin g) (Fin g) ℂ) (x : Fin g → ℂ) : hf Hm x 0 = 0 := by
  simp [hf]

theorem opW_zero (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (G : (Fin g → ℂ) → ℂ) : opW d Hm 0 G = G := by
  funext z
  simp [opW, opU, beta, hf]

variable {q : ℕ} [Fact q.Prime]

theorem lamA_eq (ι : ℂ ≃+* ℂ_[q]) (lam : Qbar →+* ℂ_[q]) (hι : ∀ z : Qbar, ι (z : ℂ) = lam z) (x : ℂ) (hx : x ∈ Qbar) :
    lamA lam x = ι x := by
  unfold lamA
  rw [dite_eq_left hx, ← hι ⟨x, hx⟩]

theorem natCast_mem_Qbar (s : ℕ) : (s : ℂ) ∈ Qbar := (algebraicClosure ℚ ℂ).natCast_mem s

theorem lamA_nat (ι : ℂ ≃+* ℂ_[q]) (lam : Qbar →+* ℂ_[q]) (hι : ∀ z : Qbar, ι (z : ℂ) = lam z) (s : ℕ) :
    lamA lam (s : ℂ) = (s : ℂ_[q]) := by
  rw [lamA_eq ι lam hι _ (natCast_mem_Qbar s), map_natCast]

end GlobalTheory.MomN.Bridge

namespace GlobalTheory.MomN.Bridge
variable {g : ℕ} {q : ℕ} [Fact q.Prime]

theorem jet_trivialTorsion_eq_latticeMomentIntegral (ι : ℂ ≃+* ℂ_[q]) (lam : Qbar →+* ℂ_[q]) (hι : ∀ z : Qbar, ι (z : ℂ) = lam z)
    (δ₀ : ℂ) (Ω : ℂ_[q]) (S : Setup g) (hOk : S.Ok) {r : ℕ} (b : Fin r → Fin g → ℂ) (hbLa : ∀ i, b i ∈ S.La)
    (t : Fin g → ℂ) (ht : S.PrimeTo q t) (G : (Fin g → ℂ) → ℂ) (μ : C(Fin r → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q])
    (hM : MomentProperty lam Ω δ₀ S b (fun _ : Fin 1 => t) μ G)
    (k : ℕ) (ys : Fin k → Fin g → ℂ) (hys : ∀ j, ys j ∈ S.La) (f : C(Fin r → ℤ_[q], ℂ_[q]))
    (hf' : ∀ a, f a = ∏ j, pairD lam Ω S.d S.Hm b (ys j) a) :
    ι (iteratedFDeriv ℂ k G 0 fun j => δ₀⁻¹ • ys j) = μ f := by
  obtain ⟨s, hs0, -, hst⟩ := ht
  have hid : IsIdem lam S.d 0 (s : ℂ) := by
    refine ⟨⟨s, 0, by simp⟩, ?_, ?_⟩
    · rw [lamA_nat ι lam hι]
      simp only [CharP.cast_eq_zero, neg_zero, zpow_zero]
      rw [← Nat.cast_pred hs0]
      exact IsUltrametricDist.norm_natCast_le_one ℂ_[q] _
    · rw [map_natCast, lamA_nat ι lam hι]
      simpa using IsUltrametricDist.norm_natCast_le_one ℂ_[q] s
  have hint : ∀ (l : Fin 1) (i : Fin r), ∃ z : ℤ, (hf S.Hm ((s : ℂ) • b i) t).im = z := by
    intro _ i
    rw [hf_smul_left]
    exact im_hf_int S hOk _ _ (hbLa i) hst
  let y0 : Fin r → Fin (q ^ 0) := fun _ => ⟨0, by simp⟩
  have hlift : liftY q 0 (s : ℂ) b y0 = 0 := by simp [liftY, y0]
  have hdir : ∀ j, S.AlgDir (ys j) := by
    intro j
    refine ⟨1, fun _ => 1, fun _ => ys j, fun _ => (algebraicClosure ℚ ℂ).one_mem, fun _ => hys j, by simp⟩
  have hf2 : ∀ a, f a = lamA lam (kap S.Hm (vecA 0 b a) (liftY q 0 (s : ℂ) b y0)) *
      ∏ j, pairD lam Ω S.d S.Hm b (ys j) a := by
    intro a
    rw [hlift, hf' a]
    have : kap S.Hm (vecA (q := q) 0 b a) 0 = ((1 : ℕ) : ℂ) := by simp [kap, hf_zero_right]
    rw [this, lamA_nat ι lam hι]; simp
  obtain ⟨hQ, heq⟩ := hM 0 0 (s : ℂ) hid le_rfl hint y0 k ys hdir f hf2
  rw [hlift, opW_zero] at hQ heq
  rw [← heq, lamA_eq ι lam hι _ hQ]
  rfl

end GlobalTheory.MomN.Bridge

namespace GlobalTheory.MomN.Bridge
variable {g : ℕ} {q : ℕ} [Fact q.Prime]

theorem pairD_dual (ι : ℂ ≃+* ℂ_[q]) (lam : Qbar →+* ℂ_[q]) (hι : ∀ z : Qbar, ι (z : ℂ) = lam z) (Ω : ℂ_[q])
    (S : Setup g) {r : ℕ} (b : Fin r → Fin g → ℂ) (s' : ℕ) (c : Fin r → Fin g → ℂ)
    (hcb : ∀ i j, beta S.d S.Hm (c j) (b i) = if i = j then (s' : ℂ) else 0) (j : Fin r) (a : Fin r → ℤ_[q]) :
    pairD lam Ω S.d S.Hm b (c j) a = Ω⁻¹ * ((s' : ℂ_[q]) * zc (a j)) := by
  unfold pairD
  congr 1
  have : ∀ i, zc (a i) * lamA lam (beta S.d S.Hm (c j) (b i)) = if i = j then (s' : ℂ_[q]) * zc (a j) else 0 := by
    intro i
    rw [hcb]
    split_ifs with h
    · subst h; rw [lamA_nat ι lam hι]; ring
    · rw [show (0 : ℂ) = ((0 : ℕ) : ℂ) by simp, lamA_nat ι lam hι]; simp
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_ite_eq']
  simp

theorem isMom_dual (ι : ℂ ≃+* ℂ_[q]) (lam : Qbar →+* ℂ_[q]) (hι : ∀ z : Qbar, ι (z : ℂ) = lam z)
    (δ₀ : ℂ) (hδ : δ₀ ≠ 0) (Ω : ℂ_[q]) (hΩ : Ω ≠ 0) (S : Setup g) (hOk : S.Ok) {r : ℕ} (b : Fin r → Fin g → ℂ)
    (hbLa : ∀ i, b i ∈ S.La) (t : Fin g → ℂ) (ht : S.PrimeTo q t) (G : (Fin g → ℂ) → ℂ)
    (μ : C(Fin r → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q]) (hM : MomentProperty lam Ω δ₀ S b (fun _ : Fin 1 => t) μ G)
    (s' : ℕ) (hs' : s' ≠ 0) (c : Fin r → Fin g → ℂ) (hcLa : ∀ j, c j ∈ S.La)
    (hcb : ∀ i j, beta S.d S.Hm (c j) (b i) = if i = j then (s' : ℂ) else 0) :
    IsMom ι (fun j => (ι.symm (Ω / ι δ₀) / (s' : ℂ)) • c j) G μ := by
  intro k j f hf
  have hs'q : (s' : ℂ_[q]) ≠ 0 := Nat.cast_ne_zero.2 hs'
  have hιδ : ι δ₀ ≠ 0 := by simpa using hδ
  let f' : C(Fin r → ℤ_[q], ℂ_[q]) := ((Ω⁻¹ * s') ^ k) • f
  have hf' : ∀ a, f' a = ∏ l, pairD lam Ω S.d S.Hm b (c (j l)) a := by
    intro a
    simp only [f', ContinuousMap.smul_apply, smul_eq_mul, hf a, pairD_dual ι lam hι Ω S b s' c hcb,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
    rw [mul_assoc]; rfl
  have hA := jet_trivialTorsion_eq_latticeMomentIntegral ι lam hι δ₀ Ω S hOk b hbLa t ht G μ hM k (fun l => c (j l)) (fun l => hcLa _) f' hf'
  have e1 : (iteratedFDeriv ℂ k G 0 fun l => δ₀⁻¹ • c (j l)) = δ₀⁻¹ ^ k • iteratedFDeriv ℂ k G 0 fun l => c (j l) := by
    rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have e2 : (iteratedFDeriv ℂ k G 0 fun l => (ι.symm (Ω / ι δ₀) / (s' : ℂ)) • c (j l)) =
      (ι.symm (Ω / ι δ₀) / (s' : ℂ)) ^ k • iteratedFDeriv ℂ k G 0 fun l => c (j l) := by
    rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [e1, smul_eq_mul, map_mul, map_pow, map_inv₀] at hA
  simp only [f', ContinuousLinearMap.map_smul, smul_eq_mul] at hA
  rw [e2, smul_eq_mul, map_mul, map_pow, map_div₀, RingEquiv.apply_symm_apply, map_natCast]
  set J := ι (iteratedFDeriv ℂ k G 0 fun l => c (j l))
  have hJ : J = (ι δ₀) ^ k * ((Ω⁻¹ * s') ^ k * μ f) := by
    rw [← hA, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hιδ, one_pow, one_mul]
  rw [hJ, ← mul_assoc, ← mul_assoc, ← mul_pow, ← mul_pow]
  have h1 : Ω / ι δ₀ / (s' : ℂ_[q]) * ι δ₀ * (Ω⁻¹ * s') = 1 := by field_simp
  rw [h1, one_pow, one_mul]

end GlobalTheory.MomN.Bridge

namespace GlobalTheory.MomN.Bridge
variable {q : ℕ} [Fact q.Prime]

theorem exists_zc_inv (s : ℕ) (hs : Nat.Coprime s q) : ∃ u : ℤ_[q], zc u = ((s : ℂ_[q]))⁻¹ := by
  have hn : ‖(s : ℤ_[q])‖ = 1 := by
    rw [PadicInt.norm_def, PadicInt.coe_natCast, Padic.norm_natCast_eq_one_iff]; exact hs.symm
  refine ⟨(s : ℤ_[q]).inv, ?_⟩
  have hm : (s : ℤ_[q]) * (s : ℤ_[q]).inv = 1 := PadicInt.mul_inv hn
  have h2 : zc (s : ℤ_[q]) * zc (s : ℤ_[q]).inv = 1 := by
    simp only [zc]
    rw [← map_mul, ← PadicInt.coe_mul, hm, PadicInt.coe_one, map_one]
  rw [show zc (s : ℤ_[q]) = (s : ℂ_[q]) by simp [zc]] at h2
  exact eq_inv_of_mul_eq_one_right h2

end GlobalTheory.MomN.Bridge

namespace GlobalTheory.MomN


open Bridge in
theorem norm_le_one_iff_latInt : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (lam : Qbar →+* ℂ_[q]) (δ₀ : ℂ) (Ω : ℂ_[q])
    (g : ℕ) (S : Setup g) (r : ℕ) (b : Fin r → Fin g → ℂ) (t : Fin g → ℂ) (G : (Fin g → ℂ) → ℂ)
    (μ : C(Fin r → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q]), (∀ z : Qbar, ι (z : ℂ) = lam z) → δ₀ ≠ 0 → ‖Ω‖ = 1 → S.Ok →
    GlobalTheory.MomOne.Split S.d q → S.NNBasis q b → S.PrimeTo q t → ContDiff ℂ ⊤ G →
    MomentProperty lam Ω δ₀ S b (fun _ : Fin 1 => t) μ G → (‖μ‖ ≤ 1 ↔ LatInt ι (Ω / ι δ₀) S.La.toAddSubgroup G) := by
  intro q _ ι lam δ₀ Ω g S r b t G μ hι hδ hΩ hOk hsplit hb ht _ hM
  have hΩ0 : Ω ≠ 0 := by rintro rfl; simp at hΩ
  obtain ⟨s', c, hs'q, hcLa, hcb, hsp⟩ := _root_.GlobalTheory.MomDual.dual_basis q g S r b hOk hb
  have hs'0 : s' ≠ 0 := by
    rintro rfl
    exact (Fact.out : q.Prime).one_lt.ne' (Nat.coprime_zero_left q |>.1 hs'q)
  have hmom := isMom_dual ι lam hι δ₀ hδ Ω hΩ0 S hOk b hb.1 t ht G μ hM s' hs'0 c hcLa hcb
  obtain ⟨hdp, hd16, -, -, -, -, hbeta, -⟩ := hOk
  constructor
  · intro hμ
    have hM' : MomInt ι (fun j => ι.symm (Ω / ι δ₀) • ((s' : ℂ)⁻¹ • c j)) G := by
      refine ⟨μ, hμ, ?_⟩
      have e : (fun j => ι.symm (Ω / ι δ₀) • ((s' : ℂ)⁻¹ • c j)) =
          fun j => (ι.symm (Ω / ι δ₀) / (s' : ℂ)) • c j := by
        funext j; simp only [smul_smul, div_eq_mul_inv]
      rw [e]; exact hmom
    refine _root_.GlobalTheory.MomN.latInt_of_span q ι (Fin g → ℂ) S.d (Ω / ι δ₀) S.La.toAddSubgroup (Fin r) (fun j => (s' : ℂ)⁻¹ • c j) G
      hdp hd16 hsplit ?_ hM'
    intro x hx
    rw [Submodule.mem_toAddSubgroup] at hx
    refine ⟨1, Nat.coprime_one_left q, fun i => beta S.d S.Hm x (b i), fun i => ?_, ?_⟩
    · obtain ⟨u, v, huv⟩ := hbeta x hx (b i) (hb.1 i)
      exact ⟨u, v, huv⟩
    · have hs'C : (s' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hs'0
      rw [Nat.cast_one, one_smul]
      calc x = (s' : ℂ)⁻¹ • ((s' : ℂ) • x) := by rw [smul_smul, inv_mul_cancel₀ hs'C, one_smul]
        _ = ∑ i, beta S.d S.Hm x (b i) • (s' : ℂ)⁻¹ • c i := by
          rw [hsp x hx, Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul, smul_smul, mul_comm]
  · intro hL
    have h1 := hL (Fin r) c (fun j => by simpa using hcLa j)
    obtain ⟨u, hu⟩ := exists_zc_inv s' hs'q
    have h2 := GlobalTheory.MomN.momInt_push q ι (Fin g → ℂ) (Fin r) (Fin r) (fun i => ι.symm (Ω / ι δ₀) • c i)
      (fun i => (ι.symm (Ω / ι δ₀) / (s' : ℂ)) • c i) (fun i j => if i = j then (s' : ℂ)⁻¹ else 0)
      (fun i j => if i = j then u else 0) G ?_ ?_ h1
    · obtain ⟨μ', hμ', hmom'⟩ := h2
      have he := GlobalTheory.MomN.measure_eq_of_moments q (Fin r) μ μ'
        (fun k j f hf => by rw [← hmom k j f hf, ← hmom' k j f hf])
      rw [he]; exact hμ'
    · intro i j
      split_ifs
      · rw [map_inv₀, map_natCast, ← hu]; rfl
      · simp [GlobalTheory.MomOne.zc]
    · intro i
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
      simp only [if_true]
      rw [smul_smul, div_eq_mul_inv, mul_comm]

end GlobalTheory.MomN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesAndLevelPrimeUnconditional
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem normOne_pair_form {d M p : ℕ} (h : GlobalTheory.Mem.An.NormOne d M p) : GlobalTheory.EX.NormOne d M p := by
  obtain ⟨A, B, h1, h2, h3⟩ := h
  exact ⟨(A, B), h1, h2, h3⟩

theorem normPrimes_unconditional : NormPrimes := by
  intro eps he0 he1
  obtain ⟨x0, hx0⟩ := UpperTheory.T3.normPrimesN UpperTheory.T3.shortNorm eps he0
  refine ⟨x0, fun s R N d hs hx hR hq => ?_⟩
  have hk : (1 : ℝ) ≤ R.k := by
    have := R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ R.k)
  have hb : 0 < s.b := Real.exp_pos _
  have hY : 0 < ((R.k : ℝ) * s.b) ^ 8 := by positivity
  have hlog : 8 * s.x ^ eps ≤ Real.log (((R.k : ℝ) * s.b) ^ 8) := by
    rw [Real.log_pow, Real.log_mul (by linarith) hb.ne']
    have h1 : Real.log s.b = s.x ^ eps := by
      rw [← hs]; exact Real.log_exp _
    have h2 := Real.log_nonneg hk
    push_cast
    linarith
  refine (hx0 s.x hx N d (hs ▸ hq) _ hY hlog).trans ?_
  refine Nat.cast_le.mpr (Finset.card_le_card fun g hg => ?_)
  simp only [GlobalTheory.Mem.An.normPrimes, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hg ⊢
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hg
  exact ⟨Nat.lt_succ_of_le h2, h3, (Nat.lt_of_floor_lt h1).le, normOne_pair_form h4⟩

theorem levelPrime_unconditional : LevelPrime := by
  intro eps c he0 he1 hc
  obtain ⟨x0, hx0⟩ := UpperTheory.T3.levelPrimeN UpperTheory.T3.shortNorm eps he0 he1 c 9 hc (by norm_num)
  obtain ⟨x1, hx1⟩ := rank_basic_bounds eps he0 he1
  refine ⟨max x0 x1, fun s R N d g0 g1 Ts hs hx hR hq hg0 hg1 hb0 hb1 hTs hlog => ?_⟩
  obtain ⟨hf, -, hr, hkr, -, -, -, -, -, -, -, -, -, -, -, hm, -⟩ :=
    hx1 s R hs (le_trans (le_max_right _ _) hx) hR
  have hx1' := s.one_lt_alt
  have hxp : 0 < s.x := by linarith
  have hn : 1 ≤ R.n := R.toFrame.ord_pos
  have hk : (1 : ℝ) ≤ R.k := by
    have := R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ R.k)
  have hf1 : (1 : ℝ) ≤ R.f := by
    exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ R.f)
  have hL : s.L = s.x ^ eps := by rw [← hs]; rfl
  have hg : ∀ g : ℕ, 1 ≤ g → (g : ℝ) ≤ s.b ^ 9 → Real.log g ≤ 9 * s.x ^ eps := by
    intro g h1 h2
    have h3 : (0 : ℝ) < g := by exact_mod_cast h1
    refine (Real.log_le_log h3 h2).trans (le_of_eq ?_)
    rw [Real.log_pow, Scale.b, Real.log_exp, hL]
    norm_num
  have hm' : s.x ^ ((1 : ℝ) / 3) ≤ (R.m : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [hs]; linarith)).trans hm
  have hW1 : (1 : ℝ) ≤ (R.f : ℝ) * R.k := one_le_mul_of_one_le_of_one_le hf1 hk
  have hW2 : (R.f : ℝ) * R.k ≤ s.x ^ (12 : ℝ) := by
    have hk5 : (R.k : ℝ) ≤ s.x ^ (5 : ℝ) := (Nat.cast_le.mpr hkr).trans hr
    exact (rank_mul_le hxp (by linarith) hf hk5).trans
      (Real.rpow_le_rpow_of_exponent_le hx1'.le (by norm_num))
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := hx0 s.x (le_trans (le_max_left _ _) hx) N d g0 g1 R.m (hs ▸ hq)
    hg0 hg1 (hg g0 hg0 hb0) (hg g1 hg1 hb1) hm' _ Ts hW1 hW2 hTs (hL ▸ hlog)
  exact ⟨T, hT1, hT2.le, hT3, normOne_pair_form hT4⟩

theorem normPrimes_and_levelPrime_unconditional : NormPrimes ∧ LevelPrime :=
  ⟨normPrimes_unconditional, levelPrime_unconditional⟩

end GlobalTheory.EX
end

