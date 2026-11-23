module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.SplitMatch

open Formalism.L2.NTheta

variable {D : D7}

theorem exists_isIdemAt {P : Pl D.host.E} (hP : conjPl P ≠ P) : ∃ e : AE D, IsIdemAt e P := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨e, f, h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P
  rcases h with ⟨h, -⟩ | ⟨-, ⟨v, ε, -, rfl⟩, ht⟩
  · exact ⟨e, h⟩
  · refine absurd (GlobalTheory.IdemSupport.eq_of_le (Ideal.map_le_iff_le_comap.2 fun x hx => ?_)) hP
    have h2 := GlobalTheory.IdemSupport.Comparison₂.conj (P := P) ht
    rw [GlobalTheory.IdemSupport.cA_algebraMap] at h2
    by_cases h0 : x = 0
    · rw [h0]; exact zero_mem _
    · exact (h2 x h0).2 ((ht x h0).1 hx)

theorem idem_unique {P : Pl D.host.E} {e e' f' : AE D} (he : IsIdemAt e P) (h : IsPrimeIdem P e' f') :
    e' = e ∧ f' = e + cA D e := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨hd, ε, hε, h1⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ (f := e + cA D e) (Or.inl ⟨he, rfl⟩)
  obtain ⟨hd', ε', hε', h1'⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ h
  exact ⟨GlobalTheory.IdemSupport.delta_unique hΦ hd' hd, by rw [h1, h1', GlobalTheory.IdemSupport.placeIdem_unique hε' hε]⟩

theorem mem_hyp {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) {V : HSp D} {k : GA D V} (hk : k ∈ hyp V P) :
    k ∈ locPart V (KsphC V ∅) e := by
  obtain ⟨h1, e', f', h2, h3⟩ := hk
  rw [(idem_unique he h2).2] at h3
  exact ⟨h1, h3⟩

theorem one_mem_hyp {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) (V : HSp D) : (1 : GA D V) ∈ hyp V P := by
  refine ⟨⟨one_mem _, fun y => ?_, fun v hv => absurd hv (Finset.notMem_empty v)⟩, e, e + cA D e,
    Or.inl ⟨he, rfl⟩, GlobalTheory.SplitHecke.suppAt_one V⟩
  rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one, Matrix.one_mulVec]

theorem unr {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) {χ : (AE D)ˣ →* Circle} (hχ : UnrPl P χ)
    (y : (AE D)ˣ) (h : (1 - e) * (y : AE D) = 1 - e) (h1 : finPart D (e * (y : AE D)) ∈ intAE D)
    (h2 : finPart D (e * ((y⁻¹ : (AE D)ˣ) : AE D)) ∈ intAE D) : χ y = 1 := by
  have h' : (1 - e) * ((y⁻¹ : (AE D)ˣ) : AE D) = 1 - e := by
    conv_lhs => rw [← h, mul_assoc, Units.mul_inv, mul_one]
  have e0 : finPart D e ∈ intAE D := by
    by_contra hc
    have := (he.2 1 one_ne_zero).2 (by
      rwa [show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, inv_one, RingHom.map_one, mul_one])
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have key : ∀ z : AE D, (1 - e) * z = 1 - e → finPart D (e * z) ∈ intAE D → finPart D z ∈ intAE D := fun z a b => by
    have : z = e * z + 1 - e := by linear_combination a
    rw [this, RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_one]
    exact sub_mem (add_mem b (GlobalTheory.SplitDivisors.one_mem_int D)) e0
  refine hχ e _ (Or.inl ⟨he, rfl⟩) y ?_ (key _ h h1) (key _ h' h2)
  linear_combination (cA D e - 1) * h + ((y : AE D) - 1) * he.1.2.1

theorem sphOp_of {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) {ϖ : 𝓞 D.host.E} (h1 : ϖ ∈ P.asIdeal)
    (h2 : ϖ ∉ P.asIdeal ^ 2) {V : HSp D} {d : List ℤ} (hd : d.Pairwise fun a b => b ≤ a) {α : GA D V}
    (hα : SuppAt e V α) (hD : DivAt V e (ϖ : D.host.E) d α) {R : Finset (GA D V)} (hR : ∀ γ ∈ R, SuppAt e V γ)
    (hc : IsCosetRep V (locPart V (KsphC V ∅) e) α R) : SphOp V P d R :=
  ⟨e, e + cA D e, ϖ, α, fun v hv => absurd hv (Finset.notMem_empty v), Or.inl ⟨he, rfl⟩, h1, h2, hd,
    fun _ _ => Iff.rfl, fun _ _ _ => rfl, hα, hD, hR, hc⟩

theorem splitLab_pairwise (n k : ℕ) : (splitLab n k).Pairwise fun a b => b ≤ a := by
  simp [splitLab, List.pairwise_append, List.pairwise_replicate]

theorem dual_splitLab_pairwise (n k : ℕ) : (dualLab (splitLab n k)).Pairwise fun a b => b ≤ a := by
  simp [dualLab, splitLab, List.pairwise_append, List.pairwise_replicate]

theorem exists_data {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) {ϖ : 𝓞 D.host.E} (h1 : ϖ ∈ P.asIdeal)
    (h2 : ϖ ∉ P.asIdeal ^ 2) (V : HSp D) : ∃ (α : ℕ → GA D V) (R R' : ℕ → Finset (GA D V)),
      (∀ j, j ≤ V.rank → IsHeckeElt V e (ϖ : D.host.E) j (α j) ∧ (∀ γ ∈ R j, SuppAt e V γ) ∧
        IsCosetRep V (locPart V (KsphC V ∅) e) (α j) (R j)) ∧
      (∀ j, j ≤ V.rank → IsHeckeElt V e (ϖ : D.host.E) j (α j) ∧ (∀ γ ∈ R' j, SuppAt e V γ) ∧
        IsCosetRep V (locPart V (KsphC V ∅) e) (α j)⁻¹ (R' j)) ∧
      (∀ j, j ≤ V.rank → SphOp V P (dualLab (splitLab V.rank j)) (R j)) ∧
      ∀ j, j ≤ V.rank → SphOp V P (splitLab V.rank j) (R' j) := by
  obtain ⟨-, hrep, hH⟩ := GlobalTheory.SplitPlace.split_local V P e he
  have h0 : (ϖ : D.host.E) ≠ 0 := fun h => h2 (by
    rw [show ϖ = 0 from Subtype.ext h]; exact zero_mem _)
  choose! α hα using (hH ϖ h1 h2).1
  choose! ρ hρ using hrep
  have hD := fun j hj => GlobalTheory.SplitDivisors.divAt_inv_of_isHeckeElt V P e ϖ j (α j) he h1 h2 hj (hα j hj)
  have s := fun j hj => (hα j hj).2.1
  have s' := fun j hj => GlobalTheory.SplitHecke.suppAt_inv (s j hj)
  refine ⟨α, fun j => ρ (α j), fun j => ρ (α j)⁻¹, fun j hj => ⟨hα j hj, hρ _ (s j hj)⟩,
    fun j hj => ⟨hα j hj, hρ _ (s' j hj)⟩, fun j hj => ?_, fun j hj => ?_⟩
  · refine sphOp_of he h1 h2 (dual_splitLab_pairwise _ _) (s j hj) ?_ (hρ _ (s j hj)).1 (hρ _ (s j hj)).2
    have := (_root_.GlobalTheory.DivDual.divAt_inv_and_mul V e _ _ _ he.1.1 h0 (hD j hj)).1
    rwa [inv_inv] at this
  · exact sphOp_of he h1 h2 (splitLab_pairwise _ _) (s' j hj) (hD j hj) (hρ _ (s' j hj)).1 (hρ _ (s' j hj)).2

section

variable {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)

theorem opOf_single (d : List ℤ) (z : ℂ) : opOf π P (Finsupp.single d z) = z • ∑ γ ∈ rep V P d, π γ := by
  unfold opOf
  exact Finsupp.sum_single_index (zero_smul _ _)

theorem opOf_sum (s : Finset ℕ) (d : ℕ → List ℤ) (z : ℕ → ℂ) :
    opOf π P (∑ j ∈ s, Finsupp.single (d j) (z j)) = ∑ j ∈ s, z j • opOf π P (Finsupp.single (d j) 1) := by
  simp only [opOf_single, one_smul]
  unfold opOf
  rw [← Finsupp.sum_finsetSum_index (by simp) (by simp [add_smul])]
  exact Finset.sum_congr rfl fun j _ => Finsupp.sum_single_index (zero_smul _ _)

theorem opOf_trunc (n k : ℕ) (d : ℕ → List ℤ) (z : ℕ → ℂ) (u : M) :
    opOf π P (∑ j ∈ Finset.range (n + 1), Finsupp.single (d j) (if j ≤ k then z j else 0)) u =
      ∑ j ∈ Finset.range (min k n + 1), z j • opOf π P (Finsupp.single (d j) 1) u := by
  rw [opOf_sum, LinearMap.sum_apply]
  symm
  refine (Finset.sum_congr rfl fun j hj => ?_).trans
    (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun j hj hj' => ?_)
  · rw [Finset.mem_range] at hj
    rw [if_pos (by omega), LinearMap.smul_apply]
  · rw [Finset.mem_range] at hj hj'
    rw [if_neg (by omega), zero_smul, LinearMap.zero_apply]

end

theorem dualC_splitC (n : ℕ) (z : ℕ → ℂ) :
    dualC (splitC n z) = ∑ j ∈ Finset.range (n + 1), Finsupp.single (dualLab (splitLab n j)) (z j) := by
  unfold dualC splitC
  rw [Finsupp.mapDomain_finsetSum]
  simp only [Finsupp.mapDomain_single]


set_option maxHeartbeats 1000000 in
theorem match_split : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → conjPl P ≠ P → UnrPl P χS → UnrPl P χT → VacFix ψ om P ∧ ∀ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ) (t : ℕ), Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) → (T.rank = S.rank + t → ∀ k, k ≤ T.rank → Match ψ om P (dualC (splitC S.rank fun j => if j ≤ k then (Ideal.absNorm P.asIdeal : ℂ) ^ ((S.rank - j) * (k - j)) * (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) t (k - j) : ℂ) * ((χS x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ S.rank)⁻¹ ^ k * ((χT x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ T.rank) ^ j else 0)) (Finsupp.single (splitLab T.rank k) 1)) ∧ (S.rank = T.rank + t → ∀ k, k ≤ S.rank → Match ψ om P (dualC (Finsupp.single (splitLab S.rank k) 1)) (splitC T.rank fun j => if j ≤ k then (Ideal.absNorm P.asIdeal : ℂ) ^ ((T.rank - j) * (k - j)) * (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) t (k - j) : ℂ) * ((χT x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ T.rank)⁻¹ ^ k * ((χS x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ S.rank) ^ j else 0)) := by
  intro D ψ S T χS χT om P hW hP hS hT
  have main : ∀ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ) (t : ℕ) (he : IsIdemAt e P) (h1 : ϖ ∈ P.asIdeal)
      (h2 : ϖ ∉ P.asIdeal ^ 2) (hx : (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e)) f (hf : IsVacAt ψ S T P f)
      αS αT RS RT a b, _ := fun e ϖ x t he h1 h2 hx f hf αS αT RS RT a b =>
    GlobalTheory.SplitHecke.hecke_identity_split ψ S T χS χT om P e ϖ x f αS αT RS RT t hW he h1 h2 hx
      (fun y a b c => ⟨unr he hS y a b c, unr he hT y a b c⟩) hf.1 (hf.2 e _ (Or.inl ⟨he, rfl⟩)) a b
  have fix : VacFix ψ om P := by
    intro f hf k hk k' hk'
    obtain ⟨e, he⟩ := exists_isIdemAt hP
    obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt
      (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
    have h0 : (ϖ : D.host.E) ≠ 0 := fun h => h2 (by
      rw [show ϖ = 0 from Subtype.ext h]; exact zero_mem _)
    have hi : incA D (ϖ : D.host.E) * incA D (ϖ : D.host.E)⁻¹ = 1 := by
      rw [← RingHom.map_mul, mul_inv_cancel₀ h0, RingHom.map_one]
    obtain ⟨αS, RS, -, a, -, -, -⟩ := exists_data he h1 h2 S
    obtain ⟨αT, -, RT, -, b, -, -⟩ := exists_data he h1 h2 T
    exact (main e ϖ (Units.mkOfMulEqOne _ _ (GlobalTheory.SplitHecke.idem_mul_inv he.1.1 hi)) 0 he h1 h2 rfl f hf
      αS αT RS RT a b).1 k (mem_hyp he hk) k' (mem_hyp he hk')
  refine ⟨fix, fun e ϖ x t he h1 h2 hx => ?_⟩
  obtain ⟨αS, RS, -, a, -, a', -⟩ := exists_data he h1 h2 S
  obtain ⟨αT, -, RT, -, b, -, b'⟩ := exists_data he h1 h2 T
  have eS : ∀ f, IsVacAt ψ S T P f → ∀ j, j ≤ S.rank → ∑ γ ∈ RS j, om (γ, 1) f =
      opOf (om.comp (MonoidHom.inl _ _)) P (Finsupp.single (dualLab (splitLab S.rank j)) 1) f := fun f hf j hj =>
    ((_root_.GlobalTheory.SphLabelOps.label_operators S P).1 _ _ (a' j hj)).2 _ (om.comp (MonoidHom.inl _ _)) f
      fun k hk => fix f hf k hk 1 (one_mem_hyp he T)
  have eT : ∀ f, IsVacAt ψ S T P f → ∀ j, j ≤ T.rank → ∑ γ ∈ RT j, om (1, γ) f =
      opOf (om.comp (MonoidHom.inr _ _)) P (Finsupp.single (splitLab T.rank j) 1) f := fun f hf j hj =>
    ((_root_.GlobalTheory.SphLabelOps.label_operators T P).1 _ _ (b' j hj)).2 _ (om.comp (MonoidHom.inr _ _)) f
      fun k hk => fix f hf 1 (one_mem_hyp he S) k hk
  refine ⟨fun hr k hk f hf => ?_, fun hr k hk f hf => ?_⟩
  · rw [dualC_splitC, opOf_trunc, ← eT f hf k hk, (main e ϖ x t he h1 h2 hx f hf αS αT RS RT a b).2.1 hr k hk]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [eS f hf j (by rw [Finset.mem_range] at hj; omega)]
  · rw [splitC, opOf_trunc, dualC, Finsupp.mapDomain_single, ← eS f hf k hk,
      (main e ϖ x t he h1 h2 hx f hf αS αT RS RT a b).2.2 hr k hk]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [eT f hf j (by rw [Finset.mem_range] at hj; omega)]

end GlobalTheory.Hk3.SplitMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

open MeasureTheory ComplexConjugate

namespace GlobalTheory.SqIntUnit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}


variable (k) in
theorem exists_ne_zero_ne_one : ∃ x : k, x ≠ 0 ∧ x ≠ 1 := by
  have h : absPow k ((1 : ℝ) : ℂ) ≠ 1 := fun e => one_ne_zero (absPow_ofReal_eq_one.1 e)
  obtain ⟨z, hz⟩ : ∃ z : kˣ, absPow k ((1 : ℝ) : ℂ) z ≠ 1 := by
    by_contra! h'
    exact h (MonoidHom.ext h')
  refine ⟨z, z.ne_zero, fun e => hz ?_⟩
  rw [show z = 1 from Units.ext e, map_one]


variable (k N) in
theorem modularCharacterFun_eq_one (g : AdGL k N) : Measure.modularCharacterFun g = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  let φ : GL (Fin N) k →* NNReal :=
    Measure.modularCharacter.comp (QuotientGroup.mk' (Subgroup.center (GL (Fin N) k)))
  refine _root_.GlobalTheory.gl_hom_nnreal_trivial_of_scalar k (exists_ne_zero_ne_one k) N φ (fun z => ?_) g
  have hz : Matrix.GeneralLinearGroup.scalar (Fin N) z ∈ Subgroup.center (GL (Fin N) k) :=
    Subgroup.mem_center_iff.2 fun h => (Matrix.GeneralLinearGroup.scalar_commute z h).symm
  show Measure.modularCharacter (QuotientGroup.mk' _ _) = 1
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 hz, map_one]

theorem isMulRightInvariant [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : Measure (AdGL k N))
    [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  rw [Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) μ) μ,
    ← Measure.modularCharacterFun_eq_haarScalarFactor μ g, modularCharacterFun_eq_one, one_smul]


variable (k) in
theorem compactOpen_basis (n : ℕ) : ∀ U ∈ nhds (1 : GL (Fin n) k), ∃ K : Subgroup (GL (Fin n) k),
    IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧ (K : Set (GL (Fin n) k)) ⊆ U := by
  intro U hU
  obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k (Fin n) U hU
  exact ⟨J, h1, GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsSmooth π → π.IsIrreducible → IsSqIntCoeff π → IsUnitarisable π := by
  intro k _ _ _ _ N V _ _ π hs hi hsq
  classical
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  obtain ⟨l, hl⟩ := GlobalTheory.ContraRefl.exists_smooth_form_ne hs (compactOpen_basis k N) hv₀
  set L : Module.Dual ℂ V := (l : Module.Dual ℂ V) with hLdef
  have hLo : IsOpen {g : GL (Fin N) k | L ∘ₗ π g = L} := by
    have h1 : IsOpen {g : GL (Fin N) k | π.dual g L = L} := l.2
    have : {g : GL (Fin N) k | L ∘ₗ π g = L} = (fun g => g⁻¹) ⁻¹' {g | π.dual g L = L} := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Representation.dual_apply, inv_inv]
      rfl
    rw [this]
    exact h1.preimage continuous_inv
  borelize (AdGL k N)
  let μ : Measure (AdGL k N) := Measure.haar
  have hF : ∀ v, ∃ F : AdGL k N → ℝ, (∀ g, F (QuotientGroup.mk g) = ‖L (π g v)‖) ∧ MemLp F 2 μ := fun v => by
    obtain ⟨F, h1, h2⟩ := hsq μ inferInstance v L hLo
    exact ⟨F, h1, by simpa using h2⟩
  choose F hF1 hF2 using hF
  have hc : ∀ z ∈ Subgroup.center (GL (Fin N) k), ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, π z v = c • v := by
    intro z hz
    obtain ⟨c, hc⟩ := schur_GL hs hi ⟨π z, fun g => by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul]
      exact congrArg π (Subgroup.mem_center_iff.1 hz g).symm⟩
    refine ⟨c, ?_, hc⟩
    have h1 := hF1 v₀ z
    have h2 := hF1 v₀ 1
    rw [(QuotientGroup.eq_one_iff z).2 hz] at h1
    rw [QuotientGroup.mk_one, h1, map_one, Module.End.one_apply] at h2
    have h3 : L v₀ ≠ 0 := hl
    have : ‖c‖ * ‖L v₀‖ = 1 * ‖L v₀‖ := by
      rw [one_mul, ← norm_mul, ← smul_eq_mul, ← map_smul, ← hc]
      exact h2
    exact mul_right_cancel₀ (norm_ne_zero_iff.2 h3) this
  let f : V → V → GL (Fin N) k → ℂ := fun v w g => L (π g v) * conj (L (π g w))
  have hfz : ∀ v w g, ∀ z ∈ Subgroup.center (GL (Fin N) k), f v w (g * z) = f v w g := by
    intro v w g z hz
    obtain ⟨c, hc1, hc⟩ := hc z hz
    have h1 : c * conj c = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc1]
      simp
    simp only [f, map_mul, Module.End.mul_apply, hc, map_smul, smul_eq_mul]
    linear_combination (L (π g v) * conj (L (π g w))) * h1
  let Φ : V → V → AdGL k N → ℂ := fun v w x => f v w (Quotient.out x)
  have hΦ : ∀ v w g, Φ v w (QuotientGroup.mk g) = f v w g := by
    intro v w g
    obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center (GL (Fin N) k)) g
    show f v w (Quotient.out (QuotientGroup.mk g : AdGL k N)) = f v w g
    rw [hz]
    exact hfz v w g z z.2
  have hfc : ∀ v w, Continuous (f v w) := by
    intro v w
    have h1 : ∀ u, Continuous fun g : GL (Fin N) k => L (π g u) := fun u =>
      ((GlobalTheory.ContraRefl.isLocallyConstant_orbit hs u).comp L).continuous
    exact (h1 v).mul (Complex.continuous_conj.comp (h1 w))
  have hΦc : ∀ v w, Continuous (Φ v w) := by
    intro v w
    refine (QuotientGroup.isQuotientMap_mk (Subgroup.center (GL (Fin N) k))).continuous_iff.2 ?_
    have : Φ v w ∘ QuotientGroup.mk = f v w := funext (hΦ v w)
    rw [this]
    exact hfc v w
  have hnorm : ∀ v w x, ‖Φ v w x‖ = F v x * F w x := by
    intro v w x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hΦ, hF1, hF1]
    simp [f, norm_mul]
  have hint : ∀ v w, Integrable (Φ v w) μ := by
    intro v w
    refine Integrable.mono' ((hF2 v).integrable_mul (hF2 w)) (hΦc v w).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [hnorm]
    rfl
  have hadd1 : ∀ v v' w, Φ (v + v') w = fun x => Φ v w x + Φ v' w x := fun v v' w => funext fun x => by
    simp only [Φ, f, map_add (f := _), add_mul]
  have hsmul1 : ∀ (a : ℂ) v w, Φ (a • v) w = fun x => a * Φ v w x := fun a v w => funext fun x => by
    simp only [Φ, f, map_smul, smul_eq_mul, mul_assoc]
  have hadd2 : ∀ v w w', Φ v (w + w') = fun x => Φ v w x + Φ v w' x := fun v w w' => funext fun x => by
    simp only [Φ, f, map_add (f := _), mul_add]
  have hsmul2 : ∀ (a : ℂ) v w, Φ v (a • w) = fun x => conj a * Φ v w x := fun a v w => funext fun x => by
    simp only [Φ, f, map_smul, smul_eq_mul, map_mul]
    ring
  let B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => ∫ x, Φ v w x ∂μ)
    (fun v v' w => by rw [hadd1, integral_add (hint _ _) (hint _ _)])
    (fun a v w => by rw [hsmul1, integral_const_mul, RingHom.id_apply, smul_eq_mul])
    (fun v w w' => by rw [hadd2, integral_add (hint _ _) (hint _ _)])
    (fun a v w => by rw [hsmul2, integral_const_mul, smul_eq_mul])
  have hB : ∀ v w, B v w = ∫ x, Φ v w x ∂μ := fun v w => rfl
  have hre : ∀ v x, (Φ v v x).re = F v x ^ 2 := by
    intro v x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hΦ, hF1]
    simp only [f, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  refine ⟨B, fun v w => ?_, fun v hv => ?_, fun h v w => ?_⟩
  · rw [hB, hB, ← integral_conj]
    congr 1
    funext x
    simp [Φ, f, map_mul, mul_comm]
  · have hcont : Continuous fun x => F v x ^ 2 := by
      have : (fun x => F v x ^ 2) = fun x => (Φ v v x).re := funext fun x => (hre v x).symm
      rw [this]
      exact Complex.continuous_re.comp (hΦc v v)
    have hi2 : Integrable (fun x => F v x ^ 2) μ := by
      have : (fun x => F v x ^ 2) = fun x => (Φ v v x).re := funext fun x => (hre v x).symm
      rw [this]
      exact (hint v v).re
    have hreB : (B v v).re = ∫ x, F v x ^ 2 ∂μ := by
      rw [hB]
      show RCLike.re (∫ x, Φ v v x ∂μ) = _
      rw [← integral_re (hint v v)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => hre v x)
    rw [hreB]
    refine lt_of_le_of_ne (integral_nonneg fun x => sq_nonneg _) (fun h0 => hv ?_)
    have h1 : (fun x => F v x ^ 2) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hi2).1 h0.symm
    have h2 : (fun x => F v x ^ 2) = 0 := (Continuous.ae_eq_iff_eq μ hcont continuous_const).1 h1
    have h3 : ∀ g, L (π g v) = 0 := fun g => by
      have := congrFun h2 (QuotientGroup.mk g)
      rw [Pi.zero_apply, hF1] at this
      simpa using this
    let W : Subrepresentation π :=
      ⟨{ carrier := {u | ∀ g, L (π g u) = 0}
         add_mem' := fun {a b} ha hb g => by simp [ha g, hb g]
         zero_mem' := fun g => by simp
         smul_mem' := fun c u hu g => by simp [hu g] },
        fun g u hu h => by
          show L (π h (π g u)) = 0
          rw [← Module.End.mul_apply, ← map_mul]
          exact hu (h * g)⟩
    haveI : IsSimpleOrder (Subrepresentation π) := hi
    rcases eq_bot_or_eq_top W with hW | hW
    · have hvW : v ∈ W.toSubmodule := h3
      rw [hW] at hvW
      exact (Submodule.mem_bot ℂ).1 hvW
    · exfalso
      have hvW : v₀ ∈ W.toSubmodule := by
        rw [hW]
        exact Submodule.mem_top
      have := hvW 1
      rw [map_one, Module.End.one_apply] at this
      exact hl this
  · haveI := isMulRightInvariant μ
    have hinv : ∀ x, Φ (π h v) (π h w) x = Φ v w (x * QuotientGroup.mk h) := by
      intro x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      rw [← QuotientGroup.mk_mul, hΦ, hΦ]
      simp only [f, map_mul, Module.End.mul_apply]
    rw [hB, hB, funext hinv]
    exact integral_mul_right_eq_self (Φ v w) _

end GlobalTheory.SqIntUnit
end

