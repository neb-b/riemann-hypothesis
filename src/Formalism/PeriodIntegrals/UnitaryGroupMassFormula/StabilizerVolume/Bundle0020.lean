module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0018
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0015
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExistsUnifFv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0017
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0016

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVAll
section
namespace PI.VolStabS

theorem densV_holds : DensV :=
  densV_of_gram (gramFilt_of (dxOpen_of secGram_holds))

end PI.VolStabS
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExOmTOfSteps
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain

theorem latSB_holds : LatSB := by
  intro F E _ _ _ _ d M n b v
  have : Module.Finite F E := Module.Finite.of_basis b
  exact PositiveNearLattice.isSB_latV b v n M

theorem exOmT_of_steps' (hI : FibInfEx) (hV : FibVEx) (hU : SdUniq) (hDI : DensFibInf)
    (hDV : DensFibV) (hR : RestrProd) : ExOmT :=
  exOmT_of_steps hI hV latSB_holds hU hDI hDV hR

theorem exOmT_of_open (hI : FibInfEx) (hV : FibVEx) (hU : SdUniq) (hR : RestrProd) : ExOmT :=
  exOmT_of_steps' hI hV hU densFibInf_holds densFibV_holds hR

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHSt
section
noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def FibLat : Prop :=
  ∀ (V X Y : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X),
    μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
    ∀ (f : V → Y) (ι : X → Y), Function.Injective ι → ∀ (G : V → X), Continuous G →
    (∀ x, f x = ι (G x)) → ∀ (U : Set V) (B : Set X) (fib : X → Measure V),
    IsFibreFamily μ f ι U ν B fib → ∀ (T : X), B ∈ 𝓝 T → ∀ Nb ∈ 𝓝 T, (∀ x, G x ∈ Nb → x ∈ U) →
    ∀ (L : AddSubgroup V), IsOpen (L : Set V) → IsCompact (L : Set V) →
    ∀ (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X), Λ 0 ≤ L →
      (∀ n, IsOpen (Λ n : Set V)) → (∀ n, IsCompact (Λ n : Set V)) → Antitone Λ →
      (∀ n, IsOpen (H n : Set X)) → (∀ n, IsCompact (H n : Set X)) →
      (∀ N' ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N') →
      (∀ y ∈ L, G y - T ∈ H 0 → ∃ D : V →+ X, (∀ n, (Λ n).map D = H n) ∧
        ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1)) →
      ∫ x, (L : Set V).indicator (1 : V → ℂ) x ∂(fib T) =
        (((μ ((L : Set V) ∩ G ⁻¹' {z | z - T ∈ H 0})) / ν (H 0)).toReal : ℂ)

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensQ
section
noncomputable section

namespace PI.VolStabS

open NumberField IsDedekindDomain Filter Asymptotics
open scoped nonZeroDivisors

namespace LocalCountingSum

variable (K : Type) [Field K] [NumberField K]

def cnt (n : ℕ) : ℝ := (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ)

theorem sum_cnt (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, cnt K k =
    (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ) := by
  induction n with
  | zero =>
    have hE : IsEmpty {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ 0} := by
      constructor
      rintro ⟨I, hI⟩
      have h0 : Ideal.absNorm (I : Ideal (𝓞 K)) = 0 := Nat.le_zero.1 hI
      rw [Ideal.absNorm_eq_zero_iff] at h0
      exact (mem_nonZeroDivisors_iff_ne_zero.1 I.2) (by rw [h0]; rfl)
    rw [Nat.card_of_isEmpty]
    simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    haveI : Finite {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} := (Ideal.finite_setOf_absNorm_le₀ (S := 𝓞 K) n).to_subtype
    haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n + 1} :=
      (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) (n + 1)).to_subtype
    have hnz : ∀ I : Ideal (𝓞 K), Ideal.absNorm I = n + 1 → I ∈ (Ideal (𝓞 K))⁰ := by
      intro I hI
      refine mem_nonZeroDivisors_iff_ne_zero.2 (fun h => ?_)
      rw [h] at hI
      simp at hI
    let e : {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n + 1} ≃ {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} ⊕ {I : Ideal (𝓞 K) // Ideal.absNorm I = n + 1} :=
      { toFun := fun x => if h : Ideal.absNorm (x.1 : Ideal (𝓞 K)) ≤ n then Sum.inl ⟨x.1, h⟩
          else Sum.inr ⟨x.1.1, by have := x.2; omega⟩
        invFun := fun y => match y with
          | Sum.inl z => ⟨z.1, Nat.le_succ_of_le z.2⟩
          | Sum.inr z => ⟨⟨z.1, hnz z.1 z.2⟩, z.2.le⟩
        left_inv := by
          intro x
          by_cases h : Ideal.absNorm (x.1 : Ideal (𝓞 K)) ≤ n
          · simp only [dif_pos h]
          · simp only [dif_neg h]
        right_inv := by
          intro y
          rcases y with z | z
          · simp only [dif_pos z.2]
          · have hz : ¬ Ideal.absNorm z.1 ≤ n := by have := z.2; omega
            simp only [dif_neg hz] }
    rw [Nat.card_congr e, Nat.card_sum]
    unfold cnt
    push_cast
    ring

theorem sum_cnt_bigO :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, cnt K k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
  have h2 := (NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop
  have hc : ∀ n : ℕ, (Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ (n : ℝ)} : ℝ) =
      (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ) := by
    intro n
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun I => Nat.cast_le))
  simp only [Real.rpow_one]
  obtain ⟨L, hL⟩ : ∃ L, Tendsto ((fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, cnt K k) / fun n : ℕ => (n : ℝ))
      atTop (nhds L) :=
    ⟨_, h2.congr (fun n => by simp only [Function.comp_apply, Pi.div_apply, hc n, sum_cnt K n])⟩
  exact Asymptotics.isBigO_of_div_tendsto_nhds
    (Filter.eventually_atTop.2 ⟨1, fun n hn h0 => absurd h0 (by positivity)⟩) L hL

theorem cnt_summable : Summable fun n : ℕ ↦ cnt K n / (n : ℝ) ^ 2 := by
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := cnt K) (r := 1) (s := 2) (sum_cnt_bigO K)
    (fun n => by unfold cnt; positivity) zero_le_one (by norm_num)
  unfold LSeriesSummable at h
  have e : LSeries.term (fun n => ((cnt K n : ℝ) : ℂ)) 2 = fun n => ((cnt K n / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn.ne']
      push_cast
      congr 1
      exact_mod_cast Complex.cpow_natCast (n : ℂ) 2
  rw [e] at h
  exact Complex.summable_ofReal.1 h

end LocalCountingSum

theorem qV_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    qV v = (Ideal.absNorm v.asIdeal : ℝ) := by
  unfold qV
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem qvSum_holds : QvSum := by
  intro F _ _
  haveI hfin : ∀ n : ℕ, Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
    fun n => (Ideal.finite_setOf_absNorm_eq (S := 𝓞 F) n).to_subtype
  let f : Ideal (𝓞 F) → ℝ := fun I => ((Ideal.absNorm I : ℝ))⁻¹ ^ 2
  have hf0 : ∀ I, 0 ≤ f I := fun I => by positivity
  have hsig : Summable (fun x : Σ n : ℕ, {I : Ideal (𝓞 F) // Ideal.absNorm I = n} => f x.2.1) := by
    rw [summable_sigma_of_nonneg (fun x => hf0 _)]
    refine ⟨fun n => Summable.of_finite, ?_⟩
    have e2 : (fun n : ℕ => ∑' I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}, f I.1) =
        fun n => LocalCountingSum.cnt F n / (n : ℝ) ^ 2 := by
      funext n
      have hc : ∀ I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}, f I.1 = ((n : ℝ))⁻¹ ^ 2 := by
        intro I
        simp only [f, I.2]
      rw [tsum_congr hc, tsum_const, nsmul_eq_mul]
      unfold LocalCountingSum.cnt
      rw [inv_pow, div_eq_mul_inv]
    rw [e2]
    exact LocalCountingSum.cnt_summable F
  have hI : Summable f := (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)).summable_iff.1 hsig
  have hinj : Function.Injective (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) :=
    fun v w h => HeightOneSpectrum.ext h
  refine (hI.comp_injective hinj).congr (fun v => ?_)
  simp only [Function.comp_apply, f, qV_eq]

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensVolC
section
noncomputable section

namespace PI.VolStabS

namespace VolAAW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
  PositiveNearLattice SdDualW

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))

theorem crd_sigR (σ : E →ₐ[F] E) (z : Fv F v ⊗[F] E) (l : Fin d) :
    crd b (Fv F v) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ z) l =
      ∑ k, crd b (Fv F v) z k * algebraMap F (Fv F v) (b.repr (σ (b k)) l) := by
  set B := Algebra.TensorProduct.basis (Fv F v) b with hBdef
  have hB : ∀ k, B k = (1 : Fv F v) ⊗ₜ[F] b k := fun k => Algebra.TensorProduct.basis_apply _ _
  have hs : ∀ k, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ ((1 : Fv F v) ⊗ₜ[F] b k) = (1 : Fv F v) ⊗ₜ[F] σ (b k) := by
    intro k
    simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  conv_lhs => rw [← B.sum_repr z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [sigR_smul, hB, hs, crd, map_sum, map_smul, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, Algebra.TensorProduct.basis_repr_tmul,
    Finsupp.mapRange_apply, one_smul]
  simp [Finsupp.smul_apply, Finsupp.mapRange_apply, hBdef]

theorem ev_sig (σ : E →ₐ[F] E) :
    ∀ᶠ v in cofinite, ∀ z ∈ latA v b, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ z ∈ latA v b := by
  filter_upwards [ev_int_all (fun q : Fin d × Fin d => b.repr (σ (b q.1)) q.2)] with v h
  intro z hz l
  rw [crd_sigR]
  exact sum_mem fun k _ => mul_mem (hz k) (h (k, l))

theorem mem_hermO_iff (σ : E →ₐ[F] E) {a : ℕ} (T : HermR (Fv F v) σ a) :
    T ∈ hermO b v σ a ↔
      (fun p i => (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i p) ∈ latV (M := a) (n := a) b v := by
  constructor
  · intro h p i k
    exact h i p k
  · intro h i j k
    exact h j i k

theorem ev_dualH [Algebra.IsSeparable F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) :
    ∀ᶠ v in cofinite, {T : HermR (Fv F v) σ a | ∀ S ∈ hermO b v σ a,
      pairHerm (Fv F v) σ a S T ∈ v.adicCompletionIntegers F} = hermO b v σ a := by
  filter_upwards [ev_dual b σ hσ (1 : Matrix (Fin a) (Fin a) E) (by simp) (a := a), ev_sig b σ,
    ev_int (1 / 2 : F)] with v hD hS hh
  ext T
  constructor
  · intro hT
    rw [Set.mem_setOf_eq] at hT
    rw [SetLike.mem_coe, mem_hermO_iff, ← hD]
    intro X hX
    rw [← pairHerm_iota v σ hσ X T]
    apply hT
    intro i j k
    have h1 : X i j ∈ latA v b := fun k => hX i j k
    have h2 : X j i ∈ latA v b := fun k => hX j i k
    exact (add_mem (hS _ h1) h2) k
  · intro hT
    rw [SetLike.mem_coe, mem_hermO_iff, ← hD] at hT
    rw [Set.mem_setOf_eq]
    intro S hS
    set c : Fv F v := algebraMap F (Fv F v) (1 / 2) with hc
    let X : Fin a → Fin a → Fv F v ⊗[F] E := fun p q =>
      c • (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) q p
    have hX : X ∈ latV (M := a) (n := a) b v := by
      intro p q k
      have := crd_smul v b c ((S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) q p) k
      simp only [crd] at this
      show (Algebra.TensorProduct.basis (Fv F v) b).repr
        (c • (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) q p) k ∈ _
      rw [this]
      exact mul_mem hh (hS q p k)
    have hcc : c + c = 1 := by
      rw [hc, ← map_add (f := _)]
      norm_num
    have hSX : S = ⟨iota v σ X, iota_mem v σ hσ X⟩ := by
      apply Subtype.ext
      funext p q
      simp only [iota, X, sigR_smul]
      rw [S.2 p q, ← add_smul, hcc, one_smul]
    rw [hSX, pairHerm_iota v σ hσ X T]
    exact hT X hX

theorem isCompact_hermO (σ : E →ₐ[F] E) (a : ℕ) :
    IsCompact (hermO b v σ a : Set (HermR (Fv F v) σ a)) ∧
      IsOpen (hermO b v σ a : Set (HermR (Fv F v) σ a)) := by
  have := locallyCompact_Fv F v
  have hcl := (isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal
  have e : (hermO b v σ a : Set (HermR (Fv F v) σ a)) = Subtype.val ⁻¹'
      ((Set.univ.pi fun _ => Set.univ.pi fun _ => (latA v b : Set (Fv F v ⊗[F] E))) :
        Set (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))) := by
    ext S
    exact ⟨fun h p _ q _ k => h p q k, fun h p q k => h p (Set.mem_univ _) q (Set.mem_univ _) k⟩
  have hKc : IsCompact ((Set.univ.pi fun _ => Set.univ.pi fun _ =>
      (latA v b : Set (Fv F v ⊗[F] E))) : Set (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_latA v b
  have hKo : IsOpen ((Set.univ.pi fun _ => Set.univ.pi fun _ =>
      (latA v b : Set (Fv F v ⊗[F] E))) : Set (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))) :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_latA v b
  rw [e]
  exact ⟨hcl.isCompact_preimage hKc, hKo.preimage continuous_subtype_val⟩

theorem smul_hermO (σ : E →ₐ[F] E) (a : ℕ) :
    ∀ s ∈ v.adicCompletionIntegers F, ∀ S ∈ (hermO b v σ a : Set (HermR (Fv F v) σ a)),
      ∃ S' ∈ (hermO b v σ a : Set (HermR (Fv F v) σ a)),
        ∀ T, pairHerm (Fv F v) σ a S' T = s * pairHerm (Fv F v) σ a S T := by
  intro s hs S hS
  have hmem : s • (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ∈ HermR (Fv F v) σ a := by
    intro p q
    simp only [Matrix.smul_apply, sigR_smul, S.2 p q]
  refine ⟨⟨_, hmem⟩, ?_, fun T => ?_⟩
  · intro p q k
    have := crd_smul v b s ((S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) p q) k
    simp only [crd] at this
    show (Algebra.TensorProduct.basis (Fv F v) b).repr
      (s • (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) p q) k ∈ _
    rw [this]
    exact mul_mem hs (hS p q k)
  · simp only [pairHerm, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul,
      smul_eq_mul]
    ring

theorem smul_latV (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ latV (M := M) (n := a) b v,
      ∃ x' ∈ latV (M := M) (n := a) b v, ∀ y, BR (Fv F v) σ J x' y = s * BR (Fv F v) σ J x y := by
  intro s hs x hx
  refine ⟨s • x, ?_, fun y => BR_smul_left v σ J s x y⟩
  intro p i l
  have := crd_smul v b s (x p i) l
  simp only [crd] at this
  rw [Pi.smul_apply, Pi.smul_apply, this]
  exact mul_mem hs (hx p i l)

end VolAAW

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.NuInvLoc
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal

def GramPres : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ (g : HA (AF F) σ J) (X : Fin a → Fin M → AF F ⊗[F] E),
    gramR (AF F) σ J (g • X) = gramR (AF F) σ J X

def PullLoc : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ (g : HA (AF F) σ J) (d : ℕ) (b : Module.Basis (Fin d) F E)
    (Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
    Continuous Φinf → HasCompactSupport Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
    ∃ (Φinf' : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf' : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv' : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      Continuous Φinf' ∧ HasCompactSupport Φinf' ∧ IsPureFin b Φf' Φv' ∧
      IsProdInfFin (fun X => Φ (g • X)) Φinf' Φf' ∧
      (∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
        ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
        ∀ fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
        IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
          {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
        ∫ X, Φinf' X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT)) =
          ∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))) ∧
      (∀ v : HeightOneSpectrum (𝓞 F),
        ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
        ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
        ∀ fibV : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
        IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
          {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fibV →
        ∫ X, Φv' v X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT)) =
          ∫ X, Φv v X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT)))

theorem omInv_of (hG : GramPres) (hP : PullLoc) : OmInv := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν g
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hm : Measurable (fun y : Fin a → Fin M → AF F ⊗[F] E => g • y) :=
    (continuous_smul_tup σ J g).measurable
  have hG' := hG F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet g
  refine ⟨?_, ?_⟩
  · have hS : MeasurableSet {X : Fin a → Fin M → AF F ⊗[F] E |
        gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} :=
      (isClosed_eq (continuous_gramR (AF F) σ J) continuous_const).measurableSet.compl
    rw [Measure.map_apply hm hS]
    have e : (fun y : Fin a → Fin M → AF F ⊗[F] E => g • y) ⁻¹'
        {X | gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} =
        {X | gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} := by
      ext X
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, hG' X]
    rw [e]
    exact hν.1
  obtain ⟨⟨μinf, hμinf⟩, a1⟩ := hν.2
  refine ⟨⟨μinf, hμinf⟩, fun μinf hμinf => ?_⟩
  obtain ⟨⟨νinf, hνinf⟩, a2⟩ := a1 μinf hμinf
  refine ⟨⟨νinf, hνinf⟩, fun νinf hνinf => ?_⟩
  obtain ⟨⟨μv, hμv⟩, a3⟩ := a2 νinf hνinf
  refine ⟨⟨μv, hμv⟩, fun μv hμv => ?_⟩
  obtain ⟨⟨νv, hνv⟩, a4⟩ := a3 μv hμv
  refine ⟨⟨νv, hνv⟩, fun νv hνv => ?_⟩
  obtain ⟨⟨fibInf, hfi⟩, a5⟩ := a4 νv hνv
  refine ⟨⟨fibInf, hfi⟩, fun fibInf hfi => ?_⟩
  obtain ⟨⟨fibV, hfv⟩, a6⟩ := a5 fibInf hfi
  refine ⟨⟨fibV, hfv⟩, fun fibV hfv => ?_⟩
  intro d b Φ Φinf Φf Φv hcΦ hcs hpure hprod
  obtain ⟨Φinf', Φf', Φv', hc', hcs', hpure', hprod', hI, hV⟩ :=
    hP F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ g d b Φ Φinf Φf Φv hcΦ hcs hpure hprod
  obtain ⟨hint, hmult, heq⟩ := a6 fibV hfv d b (fun X => Φ (g • X)) Φinf' Φf' Φv' hc' hcs' hpure'
    hprod'
  have hΦm : Measurable Φ :=
    TopoMeas.measurable_adm Φ ⟨d, b, Φinf, Φf, Φv, hcΦ, hcs, hpure, hprod⟩
  have eI := hI μinf hμinf νinf hνinf fibInf hfi
  have eV : (fun v => ∫ X, Φv' v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))) =
      fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) :=
    funext fun v => hV v (μv v) (hμv v) (νv v) (hνv v) (fibV v) (hfv v)
  refine ⟨(integrable_map_measure hΦm.aestronglyMeasurable hm.aemeasurable).2 hint, ?_, ?_⟩
  · rw [← eV]; exact hmult
  · rw [integral_map hm.aemeasurable hΦm.aestronglyMeasurable, ← eI, ← eV]
    exact heq

theorem nuInv_of_loc (hG : GramPres) (hP : PullLoc) (hD : DetAdm) : NuInv :=
  nuInv_of (omUniq_of hD) (omInv_of hG hP)

end PI.VolStabS
end
end

