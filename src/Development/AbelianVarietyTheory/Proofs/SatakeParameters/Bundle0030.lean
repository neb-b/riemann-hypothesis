module

public import Mathlib
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalToGlobal.Divisibility.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.SatakeDualWeyl.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFieldAdicCompletionTensorOfInert
public import Formalism.SatakeDualWeyl.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmDataConjIsConjOf
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV

namespace GlobalTheory

theorem cmData_sig_isConjOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (hc : CMData F E), IsConjOf hc.sig := by
  intro F E _ _ _ _ _ _ hc
  refine ⟨fun h0 => ?_, fun e => star_star e, fun e he => (hc.fixed e).1 he⟩
  have hs : Function.Surjective (algebraMap F E) := fun e => (hc.fixed e).1 (AlgHom.congr_fun h0 e)
  have h1 : Module.finrank F E = 1 :=
    (LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Algebra.linearMap F E)
      ⟨(algebraMap F E).injective, hs⟩)).symm.trans (Module.finrank_self F)
  have := hc.deg2
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamFormTraceExistsUniqueStatement
section
open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamFormTrace_exists_unique : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L], IsTrDR k K L (trDR k K L) ∧ ∀ T, IsTrDR k K L T → T = trDR k K L := by
  first | (exact @GlobalTheory.W1.trDR_isTrDR_unique) | (exact GlobalTheory.W1.trDR_isTrDR_unique) | (intros; apply GlobalTheory.W1.trDR_isTrDR_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EsymmInvMulEsymmCard
section
noncomputable section

namespace GlobalTheory.SatakeInv

open Matrix

variable {K : Type} [Field K] {r : ℕ}

def tinv : GL (Fin r) K →* GL (Fin r) K where
  toFun g := ⟨((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ, (g : Matrix (Fin r) (Fin r) K)ᵀ,
    by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩
  map_one' := by ext i j; simp [Matrix.one_apply, eq_comm]
  map_mul' g h := by ext : 1; simp [_root_.mul_inv_rev, transpose_mul]

theorem tinv_val (g : GL (Fin r) K) :
    ((tinv g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ :=
  rfl

theorem tinv_inv_val (g : GL (Fin r) K) :
    (((tinv g)⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = (g : Matrix (Fin r) (Fin r) K)ᵀ :=
  rfl

theorem tinv_tinv (g : GL (Fin r) K) : tinv (tinv g) = g := by
  ext : 1
  rw [tinv_val, tinv_inv_val, transpose_transpose]

def scalGL (c : Kˣ) : GL (Fin r) K :=
  Units.map (Matrix.scalar (Fin r) : K →+* Matrix (Fin r) (Fin r) K).toMonoidHom c

theorem scalGL_val (c : Kˣ) :
    ((scalGL c : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = Matrix.scalar (Fin r) (c : K) := rfl

theorem scalGL_comm (c : Kˣ) (g : GL (Fin r) K) : scalGL c * g = g * scalGL c := by
  ext : 1
  simp only [Units.val_mul, scalGL_val]
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _)

theorem tinv_scalGL (c : Kˣ) : tinv (scalGL c : GL (Fin r) K) = scalGL c⁻¹ := by
  ext : 1
  have h : (scalGL c : GL (Fin r) K)⁻¹ = scalGL c⁻¹ := (map_inv (Units.map (Matrix.scalar (Fin r) : K →+* Matrix (Fin r) (Fin r) K).toMonoidHom) c).symm
  rw [tinv_val, h, scalGL_val, Matrix.scalar_apply, Matrix.diagonal_transpose]

theorem tinv_scalGL' (c : Kˣ) : tinv (scalGL c : GL (Fin r) K) = (scalGL c)⁻¹ := by
  rw [tinv_scalGL]
  exact map_inv (Units.map (Matrix.scalar (Fin r) : K →+* Matrix (Fin r) (Fin r) K).toMonoidHom) c

theorem tinv_injective : Function.Injective (tinv : GL (Fin r) K → GL (Fin r) K) := fun a b h => by
  rw [← tinv_tinv a, h, tinv_tinv]


omit [Field K] in
theorem glMap_eq_glMap_iff {O : Type} [CommRing O] [Field K] [Algebra O K] (a b : GL (Fin r) K)
    (L : Submodule O (Fin r → K)) :
    GlobalTheory.LatHecke.glMap a L = GlobalTheory.LatHecke.glMap b L ↔ GlobalTheory.LatHecke.glMap (a⁻¹ * b) L = L := by
  constructor
  · intro h
    rw [GlobalTheory.LatHecke.glMap_mul, ← h, ← GlobalTheory.LatHecke.glMap_mul, inv_mul_cancel, GlobalTheory.LatHecke.glMap_one]
  · intro h
    conv_lhs => rw [← h, ← GlobalTheory.LatHecke.glMap_mul, mul_inv_cancel_left]

theorem esymm_inv_mul_esymm_card (β : Multiset ℂ) (hβ : ∀ b ∈ β, b ≠ 0) {k : ℕ} (hk : k ≤ β.card) :
    (β.map (·⁻¹)).esymm k * β.esymm β.card = β.esymm (β.card - k) := by
  obtain ⟨n, α, rfl⟩ : ∃ (n : ℕ) (α : Fin n → ℂ), β = Finset.univ.val.map α := by
    induction β using Quotient.inductionOn with
    | h l => exact ⟨l.length, l.get, by simp⟩
  have hα : ∀ i, α i ≠ 0 := fun i => hβ _ (Multiset.mem_map_of_mem _ (Finset.mem_univ_val i))
  have hn : (Finset.univ.val.map α).card = n := by simp
  rw [hn] at hk ⊢
  simp only [Multiset.map_map, Finset.esymm_map_val, Function.comp_def]
  have h1 : Finset.powersetCard n (Finset.univ : Finset (Fin n)) = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  rw [h1, Finset.sum_singleton, Finset.sum_mul]
  refine Finset.sum_nbij' compl compl (fun t ht => ?_) (fun t ht => ?_) (by simp) (by simp) fun t _ => ?_
  · simp only [Finset.mem_powersetCard_univ] at ht ⊢
    simp [Finset.card_compl, ht]
  · simp only [Finset.mem_powersetCard_univ] at ht ⊢
    rw [Finset.card_compl, ht, Fintype.card_fin]; omega
  · rw [← Finset.prod_mul_prod_compl t, ← mul_assoc, ← Finset.prod_mul_distrib,
      Finset.prod_congr rfl (fun i _ => inv_mul_cancel₀ (hα i)), Finset.prod_const_one, one_mul]

end GlobalTheory.SatakeInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingEquivTensorInertAdicCompletion
section
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix

namespace GlobalTheory.InertCompletion


open scoped WithZeroTopology in
theorem exists_completion_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (h : IsInertAt F E v P) :
    ∃ φ : v.adicCompletion F →+* P.adicCompletion E, Continuous φ ∧
      (∀ x : F, φ (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) ∧
      ∀ x, Valued.v (φ x) = Valued.v x := by
  have h' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal := h
  have : P.asIdeal.LiesOver v.asIdeal := ⟨v.isMaximal.eq_of_le
    (Ideal.comap_ne_top _ P.isPrime.ne_top) (h' ▸ Ideal.le_comap_map)⟩
  have he : Ideal.ramificationIdx' v.asIdeal P.asIdeal = 1 := by
    by_contra hne
    have := (Ideal.ramificationIdx'_ne_one_iff h'.le).1 hne
    rw [h'] at this
    exact absurd this (not_le_of_gt (Ideal.pow_lt_self _ P.ne_bot P.isPrime.ne_top 2 le_rfl))
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver F E v P).continuous
  let φ : v.adicCompletion F →+* P.adicCompletion E :=
    ((HeightOneSpectrum.adicCompletion.equiv E P).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation F)) (WithVal (P.valuation E))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv F v).toRingHom
  have hφ : ∀ x : F, φ (algebraMap F _ x) = algebraMap E _ (algebraMap F E x) := fun x => by
    apply HeightOneSpectrum.adicCompletion.ext
    exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)
  have hcont : Continuous φ :=
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion E P).comp
      ((UniformSpace.Completion.continuous_map
        (f := algebraMap (WithVal (v.valuation F)) (WithVal (P.valuation E)))).comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion F v))
  refine ⟨φ, hcont, hφ, fun x => ?_⟩
  refine (HeightOneSpectrum.denseRange_algebraMap F v).induction_on
    (p := fun x => Valued.v (φ x) = Valued.v x) x
    (isClosed_eq
      ((Valued.continuous_valuation_of_surjective (P.valuedAdicCompletion_surjective E)).comp hcont)
      (Valued.continuous_valuation_of_surjective (v.valuedAdicCompletion_surjective F))) fun k => ?_
  rw [hφ, Idele.valued_algebraMap, Idele.valued_algebraMap,
    ← HeightOneSpectrum.valuation_liesOver E v P,
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal P.asIdeal v.ne_bot, he, pow_one]

theorem continuous_of_valued_eq {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (σ : P.adicCompletion E →+* P.adicCompletion E) (h : ∀ x, Valued.v (σ x) = Valued.v x) :
    Continuous σ := by
  refine (AddMonoidHomClass.isometry_of_norm σ fun x => ?_).continuous
  exact le_antisymm (Valued.toNormedField.norm_le_iff.2 (h x).le) (Valued.toNormedField.norm_le_iff.2 (h x).ge)

theorem surjective_of_continuous {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (φ : v.adicCompletion F →+* P.adicCompletion E) (hc : Continuous φ)
    (ψ : v.adicCompletion F ⊗[F] E →+* P.adicCompletion E)
    (hψ : ∀ a x, ψ (a ⊗ₜ x) = φ a * algebraMap E _ x) : Function.Surjective ψ := by
  letI : Algebra (v.adicCompletion F) (P.adicCompletion E) := φ.toAlgebra
  haveI : ContinuousSMul (v.adicCompletion F) (P.adicCompletion E) :=
    continuousSMul_of_algebraMap _ _ hc
  letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
  let f : v.adicCompletion F ⊗[F] E →ₐ[v.adicCompletion F] P.adicCompletion E :=
    ⟨ψ, fun a => (hψ a 1).trans (by rw [map_one, mul_one]; rfl)⟩
  have hcl : IsClosed (LinearMap.range f.toLinearMap : Set (P.adicCompletion E)) :=
    Submodule.closed_of_finiteDimensional _
  intro y
  refine (HeightOneSpectrum.denseRange_algebraMap E P).induction_on
    (p := fun y => y ∈ (LinearMap.range f.toLinearMap : Set (P.adicCompletion E))) y hcl fun x => ?_
  exact ⟨1 ⊗ₜ x, (hψ 1 x).trans (by rw [map_one, one_mul])⟩

theorem exists_ringEquiv_completion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E)), IsInertAt (maximalRealSubfield E) E v P → ∀ σ : P.adicCompletion E →+* P.adicCompletion E, (∀ x : E, σ (algebraMap E (P.adicCompletion E) x) = algebraMap E (P.adicCompletion E) (ReciprocityTheory.ChartRestriction.G.FD.cc x)) → (∀ x, Valued.v (σ x) = Valued.v x) → ∃ ψ : LocAlg v ≃+* P.adicCompletion E, (∀ x : E, ψ (locEmb v x) = algebraMap E (P.adicCompletion E) x) ∧ (∀ z, ψ (locConj v z) = σ (ψ z)) ∧ ∀ z, z ∈ locOrder v ↔ Valued.v (ψ z) ≤ 1 := by
  intro E _ _ _ _ v P h σ hσ hσv
  obtain ⟨φ, hc, hφ, hv⟩ := exists_completion_map v P h
  obtain ⟨ψ, hψ⟩ : ∃ ψ : LocAlg v →+* P.adicCompletion E,
      ∀ a x, ψ (a ⊗ₜ x) = φ a * algebraMap E _ x := by
    letI : Algebra (maximalRealSubfield E) (P.adicCompletion E) :=
      ((algebraMap E (P.adicCompletion E)).comp (algebraMap (maximalRealSubfield E) E)).toAlgebra
    let f : E →ₐ[maximalRealSubfield E] P.adicCompletion E := ⟨algebraMap E _, fun _ => rfl⟩
    let g : v.adicCompletion (maximalRealSubfield E) →ₐ[maximalRealSubfield E] P.adicCompletion E :=
      ⟨φ, hφ⟩
    exact ⟨(Algebra.TensorProduct.productMap g f).toRingHom, fun a x => rfl⟩
  have hF : IsField (LocAlg v) := InertField.isField_of_inert _ E
    (Algebra.IsQuadraticExtension.finrank_eq_two _ E) v (by
      rw [show Ideal.map _ v.asIdeal = P.asIdeal from h]; exact P.isPrime)
  have hinj : Function.Injective ψ := by
    letI := hF.toField
    exact ψ.injective
  have hE : ∀ x : E, ψ (locEmb v x) = algebraMap E _ x := fun x =>
    (hψ 1 x).trans (by rw [map_one, one_mul])
  have hA : ∀ a, ψ (algebraMap _ (LocAlg v) a) = φ a := fun a =>
    (hψ a 1).trans (by rw [map_one, mul_one])
  have hσφ : ∀ a, σ (φ a) = φ a := fun a =>
    congrFun ((HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) v).equalizer
      ((continuous_of_valued_eq P σ hσv).comp hc) hc (funext fun x => by
        simp only [Function.comp_apply, hφ, hσ]
        exact congrArg _ ((IsCMField.complexConj E).commutes x))) a
  have hconj : ∀ z, ψ (locConj v z) = σ (ψ z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rw [locConj_tmul, hψ, hψ, map_mul, hσφ, hσ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hint : ∀ s : 𝓞 E, Valued.v (algebraMap E (P.adicCompletion E) (s : E)) ≤ 1 := fun s =>
    (Idele.valued_algebraMap P (s : E)).trans_le (P.valuation_le_one s)
  refine ⟨RingEquiv.ofBijective ψ ⟨hinj, surjective_of_continuous v P φ hc ψ hψ⟩, hE, hconj,
    fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · change Valued.v (ψ z) ≤ 1
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact (congrArg Valued.v (hE a)).trans_le (hint a)
    | algebraMap a => exact ((congrArg Valued.v (hA a)).trans (hv a)).trans_le a.2
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Valuation.map_add_le _ hx hy
    | mul x y _ _ hx hy => rw [map_mul, map_mul]; exact mul_le_one' hx hy
  · replace hz : Valued.v (ψ z) ≤ 1 := hz
    have fix : ∀ w : LocAlg v, locConj v w = w → Valued.v (ψ w) ≤ 1 → w ∈ locOrder v := by
      intro w hw hw1
      obtain ⟨a, rfl⟩ := exists_of_locConj_eq v hw
      rw [hA, hv] at hw1
      exact (locOrder v).algebraMap_mem ⟨a, hw1⟩
    obtain ⟨θ, hθ⟩ := exists_sub_conj_notMem P.asIdeal P.isPrime.ne_top
    have hδ1 : P.valuation E ((θ : E) - ReciprocityTheory.ChartRestriction.G.FD.cc (θ : E)) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) P).2 hθ
    set δ : E := (θ : E) - ReciprocityTheory.ChartRestriction.G.FD.cc (θ : E) with hδ
    have hδ0 : δ ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hδ1
      exact zero_ne_one hδ1
    have hcδ : ReciprocityTheory.ChartRestriction.G.FD.cc δ⁻¹ = -δ⁻¹ := by
      have : ReciprocityTheory.ChartRestriction.G.FD.cc δ = -δ := by simp [hδ, ReciprocityTheory.ChartRestriction.G.FD.cc]
      rw [← inv_neg, ← this]
      exact map_inv₀ (IsCMField.complexConj E) δ
    have hone : locEmb v δ⁻¹ * (locEmb v θ - locEmb v (ReciprocityTheory.ChartRestriction.G.FD.cc (θ : E))) = 1 := by
      rw [← map_sub, ← map_mul, inv_mul_cancel₀ hδ0, map_one]
    set b : LocAlg v := (z - locConj v z) * locEmb v δ⁻¹ with hb
    have hb1 : locConj v b = b := by
      rw [hb, map_mul, map_sub, locConj_locConj, locConj_locEmb, hcδ, map_neg]; ring
    have hb2 : Valued.v (ψ b) ≤ 1 := by
      rw [hb, map_mul, map_mul, hE, Idele.valued_algebraMap, map_inv₀, hδ1, inv_one, mul_one,
        map_sub, hconj]
      exact Valuation.map_sub_le _ hz ((hσv _).trans_le hz)
    have ha1 : locConj v (z - b * locEmb v θ) = z - b * locEmb v θ := by
      rw [map_sub, map_mul, hb1, locConj_locEmb, hb]
      linear_combination (z - locConj v z) * hone
    have ha2 : Valued.v (ψ (z - b * locEmb v θ)) ≤ 1 := by
      rw [map_sub, map_mul, hE]
      refine Valuation.map_sub_le _ hz ?_
      rw [map_mul]
      exact mul_le_one' hb2 (hint θ)
    rw [← sub_add_cancel z (b * locEmb v θ)]
    exact add_mem (fix _ ha1 ha2) (mul_mem (fix _ hb1 hb2) (locEmb_mem_locOrder v θ))

end GlobalTheory.InertCompletion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsTail
section
namespace GlobalTheory.MatrixEntryBound

theorem entry_bound {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L}
    (hϖ : (Valued.v : L → WithZero (Multiplicative ℤ)) ϖ = WithZero.exp (-1 : ℤ)) (x : L) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → (Valued.v : L → WithZero (Multiplicative ℤ)) (ϖ ^ m * x) ≤ 1 := by
  by_cases hx : x = 0
  · exact ⟨0, fun m _ => by simp [hx]⟩
  · have hv : (Valued.v : L → WithZero (Multiplicative ℤ)) x ≠ 0 := by
      simpa using hx
    refine ⟨(WithZero.log (Valued.v x)).toNat, fun m hm => ?_⟩
    rw [map_mul, map_pow, hϖ, ← WithZero.exp_log hv, ← WithZero.exp_nsmul, ← WithZero.exp_add]
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    have : WithZero.log (Valued.v x) ≤ (m : ℤ) := by
      have := Int.self_le_toNat (WithZero.log (Valued.v x)); omega
    simp; omega

theorem main : ∀ {L : Type} [inst : Field L] [inst_1 : Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {ϖ : L}, (Valued.v : L → WithZero (Multiplicative ℤ)) ϖ = WithZero.exp (-1 : ℤ) → ∀ (M : Matrix (Fin n) (Fin n) L), ∃ (N : ℕ), ∀ (i j : Fin n), ϖ ^ N * M i j ∈ Formalism.UG.intL L := by
  intro L _ _ n ϖ hϖ M
  choose f hf using fun p : Fin n × Fin n => entry_bound hϖ (M p.1 p.2)
  refine ⟨Finset.univ.sup f, fun i j => ?_⟩
  unfold Formalism.UG.intL
  exact hf (i, j) _ (Finset.le_sup (f := f) (Finset.mem_univ (i, j)))

end GlobalTheory.MatrixEntryBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsInertAtOfUniqueUnramifiedPrime
section
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix

namespace GlobalTheory.SelfDualGenus


open IsDedekindDomain NumberField in
open scoped TensorProduct Matrix in
theorem _root_.GlobalTheory.SelfDualGenus.isInertAt_of_unique_unramified (E : Type) [Field E] [NumberField E] [IsCMField E]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E))
    (hP : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ (x : E)⁻¹ ∉ _root_.GlobalTheory.SelfDualGenus.semiLoc v))
    (hx : ∃ x : 𝓞 (maximalRealSubfield E), ∃ y : 𝓞 E,
      (y : E) = algebraMap (maximalRealSubfield E) E (x : maximalRealSubfield E) ∧
        y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2) :
    _root_.Formalism.UG.IsInertAt (maximalRealSubfield E) E v P := by
  unfold _root_.Formalism.UG.IsInertAt
  have key : ∀ P' : Ideal (𝓞 E), P'.IsMaximal →
      Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) P' = v.asIdeal → P' ≤ P.asIdeal := by
    intro P' hP' hcomap z hz
    by_cases hz0 : z = 0
    · rw [hz0]; exact P.asIdeal.zero_mem
    rw [hP z hz0]
    intro hmem
    rw [_root_.GlobalTheory.SelfDualGenus.mem_semiLoc_iff] at hmem
    obtain ⟨t, ht, hint⟩ := hmem
    have hzE : (z : E) ≠ 0 := by exact_mod_cast hz0
    let w : 𝓞 E := ⟨_, hint⟩
    have hzw : z * w = algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) t := by
      apply NumberField.RingOfIntegers.ext
      show (z : E) * (((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) t : 𝓞 E) : E) * (z : E)⁻¹) = _
      field_simp
    apply ht
    rw [← hcomap, Ideal.mem_comap, ← hzw]
    exact P'.mul_mem_right _ hz
  have hker : RingHom.ker (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ v.asIdeal := by
    intro a ha
    rw [RingHom.mem_ker] at ha
    have ha0 : a = 0 := FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield E)) (𝓞 E)
      (by rw [ha, map_zero])
    rw [ha0]; exact v.asIdeal.zero_mem
  obtain ⟨P0, hP0, hP0c⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal hker
  have hP0P : P0 = P.asIdeal := hP0.eq_of_le P.isPrime.ne_top (key P0 hP0 hP0c)
  have hcP : Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) P.asIdeal = v.asIdeal := by
    rw [← hP0P]
    exact hP0c
  have hQP : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal ≤ P.asIdeal := by
    rw [Ideal.map_le_iff_le_comap, hcP]
  obtain ⟨x, y, hyx, hyP, hyP2⟩ := hx
  have hyx' : y = algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) x := by
    apply NumberField.RingOfIntegers.ext
    rw [hyx]
    rfl
  have hxv : x ∈ v.asIdeal := by
    rw [← hcP, Ideal.mem_comap, ← hyx']; exact hyP
  have hyQ : y ∈ Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal := by
    rw [hyx']; exact Ideal.mem_map_of_mem _ hxv
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hQP
  by_cases hJtop : J = ⊤
  · rw [hJ, hJtop, Ideal.mul_top]
  exfalso
  obtain ⟨P'', hP'', hJP''⟩ := Ideal.exists_le_maximal J hJtop
  have hQP'' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal ≤ P'' := by
    rw [hJ]; exact Ideal.mul_le_right.trans hJP''
  have hcP'' : Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) P'' = v.asIdeal := by
    refine (v.isMaximal.eq_of_le (Ideal.comap_ne_top _ hP''.ne_top) ?_).symm
    rw [← Ideal.map_le_iff_le_comap]; exact hQP''
  have hJP : J ≤ P.asIdeal := hJP''.trans (key P'' hP'' hcP'')
  apply hyP2
  rw [pow_two]
  have := hJ ▸ hyQ
  exact Ideal.mul_mono_right hJP this

end GlobalTheory.SelfDualGenus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JInvNormLeOne
section
open GlobalTheory GlobalTheory.CMCurves

namespace GlobalTheory.ThLoc

theorem cm1 : Formalism.L2.Th1.CM.JInvariantIntegrality := by
  intro d L _ hd hL
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  rw [Formalism.L2.Th1.CM.jInv, g₂_cube_div_eq_modularJ ha h]
  refine isIntegral_modularJ_of_mul_mem (α := Formalism.L2.Th1.CM.omegaK d) (fun m hm => ?_) fun x hx ↦ ?_
  · have := congrArg Complex.im hm
    have h0 : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
    simp [Formalism.L2.Th1.CM.omegaK] at this
    omega
  · have key : ∀ y : ℂ, y ∈ Submodule.span ℤ {(τ : ℂ), 1} ↔ a * y ∈ L.lattice := fun y ↦ by
      rw [h, Submodule.mem_span_pair]
      simp [mul_right_inj' ha]
    rw [key] at hx ⊢
    simpa [mul_left_comm] using hL _ hx

end GlobalTheory.ThLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LaurentConstantTermEqEvalOriginChartStatement
section
open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentConstantTerm_eq_eval_origin_chart : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ ρ : F →ₗ[k] k, IsRes k x ρ → ∃ ev : rA k x {0} →ₐ[k] k, (∀ a : rA k x {0}, ρ a = ev a) ∧ RingHom.ker ev = Ideal.span (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) := by
  first | (exact @GlobalTheory.PD.ResEv.chart0) | (exact GlobalTheory.PD.ResEv.chart0) | (intros; apply GlobalTheory.PD.ResEv.chart0 <;> assumption)
end

