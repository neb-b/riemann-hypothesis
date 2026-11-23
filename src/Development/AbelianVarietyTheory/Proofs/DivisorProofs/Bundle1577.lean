module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1146
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1513
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddnessConditionHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1553
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.ChiGrid Formalism.L2.DIV

namespace GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace VecEx

section Frames

variable {K : Type} [Field K] [NumberField K] {n : ℕ}


omit [NumberField K] in
theorem mem_colLat_iff (B : GL (Fin n) K) (x : Fin n → K) :
    x ∈ colLat B ↔ ∃ c : Fin n → 𝓞 K, (B : Matrix (Fin n) (Fin n) K) *ᵥ (fun j => (c j : K)) = x := by
  unfold colLat
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine exists_congr fun c => ?_
  have key : (∑ j, c j • fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a j) =
      (B : Matrix (Fin n) (Fin n) K) *ᵥ fun j => (c j : K) := by
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, Algebra.smul_def]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [key]

theorem isLattice_colLat (B : GL (Fin n) K) : Submodule.IsLattice K (colLat B) := by
  exact Submodule.IsLattice.of_fg K (Submodule.fg_span (Set.finite_range _))


omit [NumberField K] in
theorem form_frame [StarRing K] (G B : Matrix (Fin n) (Fin n) K) (hB : Bᴴ * G * B = 1) (c d : Fin n → K) :
    ∑ i, ∑ j, star ((B *ᵥ c) i) * G i j * (B *ᵥ d) j = ∑ i, star (c i) * d i := by
  have h1 : ∑ i, ∑ j, star ((B *ᵥ c) i) * G i j * (B *ᵥ d) j = star (B *ᵥ c) ⬝ᵥ (G *ᵥ (B *ᵥ d)) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  rw [h1, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hB,
    Matrix.one_mulVec]
  rfl

end Frames

variable {D : D7}

theorem isSelfDualC_colLat (V : HSp D) (B : GL (Fin V.rank) D.host.E)
    (hB : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * V.gram * B.1 = 1) : IsSelfDualC V (colLat B) := by
  classical
  have hB' : B.1ᴴ * V.gram * B.1 = 1 := hB
  refine ⟨isLattice_colLat B, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · obtain ⟨c, rfl⟩ := (mem_colLat_iff B x).1 hx
    obtain ⟨d, rfl⟩ := (mem_colLat_iff B y).1 hy
    rw [form_frame _ _ hB']
    have : ∑ i, star (c i : D.host.E) * (d i : D.host.E) ∈ Formalism.UG.intOE D.host.E :=
      sum_mem fun i _ => mul_mem (GlobalTheory.PlaceDatum.star_mem_intOE ⟨c i, rfl⟩) ⟨d i, rfl⟩
    exact this
  · have hy : B.1 *ᵥ ((B⁻¹).1 *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have : ∀ j, ∃ b : 𝓞 D.host.E, (b : D.host.E) = ((B⁻¹).1 *ᵥ y) j := fun j => by
      obtain ⟨b, hb⟩ := h _ ((mem_colLat_iff B _).2 ⟨Pi.single j 1, rfl⟩)
      refine ⟨b, ?_⟩
      rw [hb, ← hy, form_frame _ _ hB', hy, Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [Pi.single_eq_of_ne hij]
      · simp
    choose b hb using this
    exact (mem_colLat_iff B y).2 ⟨b, by rw [show (fun j => (b j : D.host.E)) = _ from funext hb, hy]⟩

variable {S T : HSp D} {ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem exists_nsmul_latO (hS : ΛS.FG) (hT : ΛT.FG) (hS' : Submodule.IsFullLattice D.host.E ΛS')
    (hT' : Submodule.IsFullLattice D.host.E ΛT') : ∃ c : ℕ, 0 < c ∧ ∀ u : WO S T, u.map (infPart D) = 0 →
      u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) →
      c • u ∈ latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  obtain ⟨K, hK, h⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO hS' hT'
  obtain ⟨N, hN, h'⟩ := GlobalTheory.PlaceDatum.exists_den_latO hS hT
  refine ⟨N * K, Nat.mul_pos hN hK, fun t ht hu => ?_⟩
  rw [mul_nsmul]
  refine h _ (Matrix.ext fun i j => ?_) fun i j => ?_
  · change infPart D (N • t i j) = 0
    rw [nsmul_eq_mul, RingHom.map_mul, show infPart D (t i j) = 0 from congrFun (congrFun ht i) j, mul_zero]
  · change toEAf D (N • t i j) ∈ _
    rw [nsmul_eq_mul, RingHom.map_mul, map_natCast]
    exact h' t hu i j

theorem isSBHalf_of_lattices (hS : Submodule.IsFullLattice D.host.E ΛS) (hT : Submodule.IsFullLattice D.host.E ΛT)
    (hS' : Submodule.IsFullLattice D.host.E ΛS') (hT' : Submodule.IsFullLattice D.host.E ΛT') {e : AE D}
    (he : infPart D e = 0) {Φ : WO S T → ℂ} (hΦ : IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ) :
    IsSBHalf e (latO S T ΛS' ΛT' fun _ => True) Φ := by
  obtain ⟨c, hc, h⟩ := exists_nsmul_latO hS.toIsLattice.fg hT.toIsLattice.fg hS' hT'
  obtain ⟨c', hc', h'⟩ := exists_nsmul_latO hS'.toIsLattice.fg hT'.toIsLattice.fg hS hT
  obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
  have hh : ∀ (m : ℕ) (u : WO S T), IsHalf e u → IsHalf e (m • u) := fun m u hu =>
    (GlobalTheory.PlaceModel.isHalf_iff S T).2 (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hu) m)
  refine ⟨h1, c' * (c * k), by positivity, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · rw [mul_nsmul, mul_nsmul]
    exact h2 _ (nsmul_mem (h' u (GlobalTheory.PlaceDatum.infPart_of_half he hu') hu) c) (hh _ _ (hh _ _ hu')) t
  · rw [mul_nsmul', mul_nsmul']
    exact nsmul_mem (h _ (GlobalTheory.PlaceDatum.infPart_of_half he (hh _ _ (h1 t ht))) (h3 t ht)) c'

theorem exists_isThetaAt_of_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {sS sT}
    (hS : Submodule.IsFullLattice D.host.E ΛS) (hT : Submodule.IsFullLattice D.host.E ΛT) (hS' : IsSelfDualC S ΛS')
    (hT' : IsSelfDualC T ΛT') {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {f₀ Φ : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT ΛS' ΛT' f₀) (hΦ : IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ) :
    ∃ f, IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS' ΛT' fun _ => True) 1 f₀ Φ f :=
  GlobalTheory.PlaceDatum.exists_isThetaAt hf.1 hS' hT' (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he)
    (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hf.1 S T ΛS' ΛT' hS' hT' _ e he f₀ hf.2.theta hf.2.lat).1
    (isSBHalf_of_lattices hS hT
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S ΛS' hS')
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T ΛT' hT')
      (GlobalTheory.PlaceDatum.infPart_idemSum he) hΦ)

end VecEx

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem DefNode.selfDual (G : ChiGrid.GridData L sc) {μ0 : T} (hL : L.Is μ0) {X : Node} (h : DefNode D.R.m X) :
    IsSelfDualC (G.V X) (G.Λ X) := by
  rcases X with ⟨_ | i, j⟩ | i | j
  · exact (colY_isV D T L μ0 hL j h.2.le).sd
  · exact (G.isV (X := .grid (i + 1) j) ⟨h.1, h.2.le⟩ (by simp)).sd
  · exact h.elim
  · exact (G.isV (X := .top j) h (by simp)).sd

theorem Std.selfDual {G : ChiGrid.GridData L sc} {U : Set T} (N : Std G U) {X : Node} (h : DefNode D.R.m X) :
    IsSelfDualC (G.V X) (colLat (N.fr X)) :=
  VecEx.isSelfDualC_colLat _ _ (N.fr_on X h)

theorem Normal.hasVec_of_defPair {G : ChiGrid.GridData L sc} {W : G.Weil} {μ0 : T} (hL : L.Is μ0) {U : Set T} {N : Std G U}
    (Z : Normal W N) {t : T} {p : Pair T} (hp : DefPair D.R.m p) (d : FinDatum G t p) : Z.HasVec d := by
  obtain ⟨h1, h2⟩ := hp.nodes
  have hv := Z.vac_is p hp
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ (h1.selfDual G hL)
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ (h2.selfDual G hL)
  rcases p with ⟨i, j⟩ | ⟨t', i, j⟩ | i | ⟨t', j⟩
  · exact VecEx.exists_isThetaAt_of_vac (S := G.pS (.chi i j)) (T := G.pT (.chi i j)) inferInstance inferInstance (isSelfDualC_neg (N.selfDual h2))
      (N.selfDual h1) d.e_is hv d.sb
  · exact hp.elim
  · exact hp.elim
  · exact VecEx.exists_isThetaAt_of_vac inferInstance inferInstance (N.selfDual h1)
      (N.selfDual h2) d.e_is hv d.sb

theorem hasVec {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : ChiGrid.GridData L sc) (W : G.Weil) :
    ∀ μ0, L.Is μ0 → ∀ (U : Set T) (N : Std G U) (Z : Normal W N) (t : T), t ∈ U → ∀ p : Pair T, DefPair D.R.m p →
      ∀ d : FinDatum G t p, Z.HasVec d :=
  fun _ hL _ _ Z _ _ _ hp d => Z.hasVec_of_defPair hL hp d

end GlobalTheory.FunObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalIdempotentDivisibleCongruent
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall.IdemChoice

open GlobalTheory.FunObj.StdDatum

theorem exists_idem_of_limit : (∀ (D : D7) (x : 𝓞 D.host.E), ∃ e ∈ OhE D, e * e = e ∧ ∀ N : ℕ, 0 < N → ∃ n : ℕ, 0 < n ∧ ∃ w ∈ OhE D, e = inc D (x : D.host.E) ^ n + (N : AE D) * w) → ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (δ u : 𝓞 D.host.E), inc D ((δ * u : 𝓞 D.host.E) : D.host.E) - 1 ∈ hatId D (D.host.conj • 𝔪) → ∃ f ∈ OhE D, ∃ w ∈ OhE D, f * f = f ∧ f * sgA D f = 0 ∧ f = inc D (δ : D.host.E) * w ∧ 1 - f ∈ hatId D (D.host.conj • 𝔪) := by
  intro hB1 D 𝔪 hsup δ u hδu
  set 𝔫 : Ideal (𝓞 D.host.E) := D.host.conj • 𝔪 with h𝔫
  have gen : ∀ {b : 𝓞 D.host.E}, b ∈ 𝔫 → ∀ {y : AE D}, y ∈ OhE D → inc D (b : D.host.E) * y ∈ hatId D 𝔫 :=
    fun {b} hb {y} hy => AddSubgroup.subset_closure ⟨b, hb, y, hy, rfl⟩
  have gen1 : ∀ {b : 𝓞 D.host.E}, b ∈ 𝔫 → inc D (b : D.host.E) ∈ hatId D 𝔫 := fun hb => by
    simpa using gen hb (one_mem (OhE D))
  by_cases hδ : δ = 0
  · subst hδ
    refine ⟨0, zero_mem _, 0, zero_mem _, by simp, by simp, by simp, ?_⟩
    have : inc D ((0 * u : 𝓞 D.host.E) : D.host.E) - 1 = -1 := by simp
    rw [this] at hδu
    simpa using neg_mem hδu
  have h1m : (1 : 𝓞 D.host.E) ∈ 𝔪 ⊔ 𝔫 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 h1m
  have h𝔫0 : 𝔫 ≠ ⊥ := by
    intro e
    have h𝔪 : 𝔪 = ⊥ := by
      by_contra h
      exact GlobalTheory.BotPairSmall.conj_smul_ne_bot D h e
    rw [e, h𝔪, sup_bot_eq] at hsup
    exact bot_ne_top hsup
  set x : 𝓞 D.host.E := s * δ * u with hx
  set X : AE D := inc D (x : D.host.E) with hX
  have hXO : X ∈ OhE D := GlobalTheory.CongIdx.inc_int_mem x

  have h1X : 1 - X ∈ hatId D 𝔫 := by
    have e : 1 - X = inc D (t : D.host.E) + inc D (s : D.host.E) * (-(inc D ((δ * u : 𝓞 D.host.E) : D.host.E) - 1)) := by
      have e1 : inc D (s : D.host.E) + inc D (t : D.host.E) = 1 := by
        rw [← map_add (f := _), show (s : D.host.E) + t = ((s + t : 𝓞 D.host.E) : D.host.E) from rfl, hst]; simp
      rw [hX, hx]
      push_cast
      simp only [map_mul]
      linear_combination -e1
    rw [e]
    exact add_mem (gen1 ht) (GlobalTheory.CongIdx.mul_mem_hatId (GlobalTheory.CongIdx.inc_int_mem s) (neg_mem hδu))

  have hxm : x ∈ 𝔪 := by rw [hx, mul_assoc]; exact Ideal.mul_mem_right _ _ hs
  have hsX : sgA D X ∈ hatId D 𝔫 := by
    rw [hX, GlobalTheory.NormSum.PtsMem.sgA_inc]
    exact gen1 (Ideal.smul_mem_pointwise_smul _ _ _ hxm)
  have hsXO : sgA D X ∈ OhE D := VacMove.sgA_mem D hXO

  have hN₁ : 0 < Ideal.absNorm (Ideal.span {δ}) := by
    rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hδ
  have hN₂ : 0 < Ideal.absNorm 𝔫 := by
    rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔫0
  set N := Ideal.absNorm (Ideal.span {δ}) * Ideal.absNorm 𝔫 with hN
  have hNδ : (N : 𝓞 D.host.E) ∈ Ideal.span {δ} := by
    rw [hN, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  have hN𝔫 : (N : 𝓞 D.host.E) ∈ 𝔫 := by
    rw [hN, Nat.cast_mul]; exact Ideal.mul_mem_left _ _ (Ideal.absNorm_mem _)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hNδ
  have hNinc : (N : AE D) = inc D ((N : 𝓞 D.host.E) : D.host.E) := by simp
  obtain ⟨e, heO, hee, hlim⟩ := hB1 D x
  obtain ⟨n, hn, w, hwO, hew⟩ := hlim N (Nat.mul_pos hN₁ hN₂)
  set ē := sgA D e with hē
  have hēO : ē ∈ OhE D := VacMove.sgA_mem D heO
  have hēē : ē * ē = ē := by rw [hē, ← map_mul, hee]
  refine ⟨e * (1 - ē), mul_mem heO (sub_mem (one_mem _) hēO), ?_⟩

  have hXd : X = inc D (δ : D.host.E) * inc D ((s * u : 𝓞 D.host.E) : D.host.E) := by
    rw [hX, hx, ← map_mul]; congr 1; push_cast; ring
  have hNd : (N : AE D) = inc D (δ : D.host.E) * inc D (c : D.host.E) := by
    rw [hNinc, ← hc, ← map_mul]; congr 1; push_cast; ring
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hed : e = inc D (δ : D.host.E) *
      (inc D ((s * u : 𝓞 D.host.E) : D.host.E) * X ^ m + inc D (c : D.host.E) * w) := by
    rw [hew, pow_succ, hNd, ← hX]
    linear_combination X ^ m * hXd
  refine ⟨(inc D ((s * u : 𝓞 D.host.E) : D.host.E) * X ^ m + inc D (c : D.host.E) * w) * (1 - ē),
    mul_mem (add_mem (mul_mem (GlobalTheory.CongIdx.inc_int_mem _) (pow_mem hXO m))
      (mul_mem (GlobalTheory.CongIdx.inc_int_mem _) hwO)) (sub_mem (one_mem _) hēO), ?_, ?_, ?_, ?_⟩
  · linear_combination (1 - ē) ^ 2 * hee + e * hēē
  · have hs2 : sgA D (e * (1 - ē)) = ē * (1 - e) := by
      rw [map_mul, map_sub, map_one, hē, GlobalTheory.NormSum.VacMove.sgA_sgA]
    rw [hs2]
    linear_combination (-(1 - ē) * ē) * hee
  · conv_lhs => rw [hed]
    ring
  ·
    have e1 : 1 - e * (1 - ē) = (1 - X ^ (m + 1)) - (N : AE D) * w + e * ē := by rw [hew, ← hX]; ring
    rw [e1]
    refine add_mem (sub_mem ?_ ?_) ?_
    · rw [← mul_neg_geom_sum]
      rw [mul_comm]
      exact GlobalTheory.CongIdx.mul_mem_hatId (sum_mem fun i _ => pow_mem hXO i) h1X
    · rw [hNinc]; exact gen hN𝔫 hwO
    · refine GlobalTheory.CongIdx.mul_mem_hatId heO ?_
      rw [hē, hew, ← hX, map_add (f := _), map_pow, map_mul, pow_succ, map_natCast]
      refine add_mem ?_ ?_
      · exact GlobalTheory.CongIdx.mul_mem_hatId (pow_mem hsXO m) hsX
      · rw [hNinc]; exact gen hN𝔫 (VacMove.sgA_mem D hwO)

end GlobalTheory.BotPairSmall.IdemChoice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzBruhatSchroedingerFixedLocalField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SchrTestVec

theorem exists_fixed_of_subgroup {K : Type} [CommRing K] [Invertible (2 : K)] [TopologicalSpace K] [IsTopologicalRing K]
    [T2Space K] {κ : Type} [Fintype κ] (ψ : AddChar K ℂ) (U₀ : Set K) (hU₀ : IsOpen U₀) (h0 : (0 : K) ∈ U₀)
    (hψ : ∀ t ∈ U₀, ψ t = 1) (B : AddSubgroup (κ → K)) (hBo : IsOpen (B : Set (κ → K)))
    (hBc : IsCompact (B : Set (κ → K))) :
    ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → K), φ₁ ≠ 0 ∧
      ∃ U ∈ nhds (0 : (κ → K) × (κ → K)), ∀ w ∈ U, GlobalTheory.WeilM.schr ψ w φ₁ = φ₁ := by
  refine ⟨(B : Set (κ → K)).indicator fun _ => (1 : ℂ), ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ (B : Set (κ → K))
    · filter_upwards [hBo.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    · filter_upwards [hBc.isClosed.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
  · exact HasCompactSupport.intro hBc fun x hx => Set.indicator_of_notMem hx _
  · intro h
    have := congrFun h 0
    rw [Set.indicator_of_mem (show (0 : κ → K) ∈ (B : Set (κ → K)) from B.zero_mem)] at this
    exact one_ne_zero this
  · have hc : Continuous fun z : ((κ → K) × (κ → K)) × (κ → K) =>
        z.2 ⬝ᵥ z.1.2 + ⅟(2 : K) * (z.1.1 ⬝ᵥ z.1.2) :=
      (continuous_snd.dotProduct continuous_fst.snd).add
        (continuous_const.mul (continuous_fst.fst.dotProduct continuous_fst.snd))
    have h1 : ∀ᶠ w : (κ → K) × (κ → K) in nhds 0, ∀ x ∈ (B : Set (κ → K)),
        x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2) ∈ U₀ := by
      refine hBc.eventually_forall_of_forall_eventually
        (P := fun (w : (κ → K) × (κ → K)) (x : κ → K) => x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2) ∈ U₀) fun x _ => ?_
      refine (hU₀.preimage hc).mem_nhds ?_
      simpa using h0
    have h2 : ∀ᶠ w : (κ → K) × (κ → K) in nhds 0, w.1 ∈ (B : Set (κ → K)) :=
      (hBo.preimage continuous_fst).mem_nhds B.zero_mem
    refine ⟨_, h1.and h2, fun w hw => ?_⟩
    obtain ⟨hw1, hw2⟩ := hw
    funext x
    show ψ (x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2)) * (B : Set (κ → K)).indicator (fun _ => (1 : ℂ)) (x + w.1) = _
    by_cases hx : x ∈ (B : Set (κ → K))
    · rw [hψ _ (hw1 x hx), one_mul, Set.indicator_of_mem hx,
        Set.indicator_of_mem (show x + w.1 ∈ (B : Set (κ → K)) from B.add_mem hx hw2)]
    · have hx' : x + w.1 ∉ (B : Set (κ → K)) := fun h => hx (by simpa using B.sub_mem h hw2)
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx', mul_zero]

theorem exists_fixed : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ∀ {κ : Type} [Fintype κ], ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), φ₁ ≠ 0 ∧
      ∃ U ∈ nhds (0 : (κ → Fv F v) × (κ → Fv F v)), ∀ w ∈ U, GlobalTheory.WeilM.schr ψ w φ₁ = φ₁ := by
  intro F _ _ v ψ hψ κ _
  obtain ⟨U₀, hU₀⟩ := GlobalTheory.HeisLatVac.lc_exists_open_ker ψ hψ
  refine exists_fixed_of_subgroup ψ U₀ U₀.isOpen U₀.zero_mem hU₀
    (AddSubgroup.pi Set.univ fun _ => (v.adicCompletionIntegers F).toSubring.toAddSubgroup) ?_ ?_
  · exact isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _
  · exact isCompact_univ_pi fun _ =>
      isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)

end GlobalTheory.SchrTestVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCompDet
section
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.FunObj.NormUniq.SplitDet

theorem exists_splitComp_det : ∀ {D : D7} {N : ℕ} {𝔪 : Ideal (𝓞 D.host.E)} {k : GA D N}, k ∈ intG D N → CongOne D 𝔪 k →
    SuppSplit D (k : GL (Fin N) (AE D)) → ∃ x : (AE D)ˣ, IntU D x ∧
      (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x : AE D) - 1)) ∧
      x = Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) * sgU D x ∧
      (x : AE D) - 1 ∈ hatId D 𝔪 ∧ (x : AE D) - 1 ∈ hatId D (D.host.conj • 𝔪) := by
  intro D N 𝔪 k hk hc hs
  have hint := (mem_intG k).1 hk
  have huO : ((Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) ∈ OhE D :=
    VacMove.det_int D _ hint
  have hn := VacMove.det_norm D k
  have hm1 : ((Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) - 1 ∈ hatId D 𝔪 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact GlobalTheory.FunObj.StdDatum.DetCong.det_sub_one_mem_hatId_of _ (fun i j => (hint i j).1) hc
  have hz : ∀ q : ℕ, q.Prime → InertQ D q →
      ZeroAt D q (((Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) - 1) :=
    fun q hq hi => GlobalTheory.VacuumScalar.zeroAt_det hq (hs q hq hi)
  set U := Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) with hU
  set u : AE D := (U : AE D) with hu
  have hm2 : u - 1 ∈ hatId D (D.host.conj • 𝔪) := by
    have e : u - 1 = -(u * sgA D (u - 1)) := by
      rw [map_sub, map_one, mul_sub, hn]; ring
    rw [e]
    exact neg_mem (GlobalTheory.FunObj.StdDatum.mul_mem_hatId huO (GlobalTheory.FunObj.StdDatum.DetCong.sgA_mem_hatId hm1))
  obtain ⟨ε, hε, h1, h2, h3⟩ := VacMove.exists_half_idem D
  have h1' : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, h1]
  have hεε : sgA D (sgA D ε) = ε := VacMove.sgA_sgA D ε
  set η := sgA D ε with hη
  set v := sgA D u with hv
  have hx : ((1 - η) + η * u) * ((1 - η) + η * v) = 1 := by
    linear_combination (1 - u - v + u * v) * h1' + η * hn
  let x : (AE D)ˣ := ⟨_, _, hx, by rw [mul_comm, hx]⟩
  have hxv : (x : AE D) = (1 - η) + η * u := rfl
  have hx1 : (x : AE D) - 1 = η * (u - 1) := by rw [hxv]; ring
  have hηO : η ∈ OhE D := VacMove.sgA_mem D hε
  have h0 : (1 - u) * (1 - (ε + η)) = 0 := by
    refine GlobalTheory.VacuumScalar.eq_zero_of_zeroAt _ fun q hq => ?_
    by_cases hi : InertQ D q
    · convert VacMove.zeroAt_mul D hq (hz q hq hi) (-(1 - (ε + η))) using 1
      ring
    · convert VacMove.zeroAt_mul D hq ((h3 q hq).2 hi) (1 - u) using 1
      ring
  refine ⟨x, ⟨?_, ?_⟩, fun q hq hi => ?_, ?_, ?_, ?_⟩
  · rw [hxv]; exact add_mem (sub_mem (one_mem _) hηO) (mul_mem hηO huO)
  · change (1 - η) + η * v ∈ OhE D
    exact add_mem (sub_mem (one_mem _) hηO) (mul_mem hηO (VacMove.sgA_mem D huO))
  · convert VacMove.zeroAt_mul D hq ((h3 q hq).1 hi) (η * (u - 1)) using 1
    rw [hx1]
    linear_combination (-(u - 1)) * h2 + (-(u - 1)) * h1'
  · ext
    change (1 - η) + η * u = u * sgA D ((1 - η) + η * u)
    rw [map_add (f := _), map_mul, map_sub, map_one, hεε]
    linear_combination h0 - ε * hn
  · rw [hx1]; exact GlobalTheory.FunObj.StdDatum.mul_mem_hatId hηO hm1
  · rw [hx1]; exact GlobalTheory.FunObj.StdDatum.mul_mem_hatId hηO hm2

end GlobalTheory.FunObj.NormUniq.SplitDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorLatticePointOfIntegralSplitPlaceCoorStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensorLattice_point_of_integral_splitPlace_coordinate : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v))
    (c : GL (Fin d) (Fv F v)), IsSplitBasis t X.L b → IsSplitBasis t W.L c →
    ∀ A : Matrix (Fin n) (Fin d) (Fv F v), (∀ i j, A i j ∈ v.adicCompletionIntegers F) →
      ∃ γ ∈ latAtV X W v, γ.map (piW (t.comp σ)) = 0 ∧ (b⁻¹).1 * γ.map (piW t) * (c⁻¹).1ᵀ = A := by
  first | exact @GlobalTheory.LatFill.exists_latAtV_coord | exact GlobalTheory.LatFill.exists_latAtV_coord | (intros; apply GlobalTheory.LatFill.exists_latAtV_coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceZeroAdeleUnitLatticeAtInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_traceZero_adele_unit_lattice_at_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d : ℕ) (W : Spc F E d) (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∃ β b up um : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) β ∧ cA σ β = -β ∧ ∀ z ∈ GlobalTheory.InertSph.latAt W v,
      β • z ∈ GlobalTheory.InertSph.latAt W v ∧ b • z ∈ GlobalTheory.InertSph.latAt W v ∧ up • z ∈ GlobalTheory.InertSph.latAt W v ∧
      um • z ∈ GlobalTheory.InertSph.latAt W v ∧ (β * b) • z = z ∧ ((1 + β) * up) • z = z ∧ ((1 - β) * um) • z = z := by
  first | exact @GlobalTheory.InertSph.exists_traceZero_unit | exact GlobalTheory.InertSph.exists_traceZero_unit | (intros; apply GlobalTheory.InertSph.exists_traceZero_unit <;> assumption)
end

