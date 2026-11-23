module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MapCSmulMulVec
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0124
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectiveTorusClassesOfIdempotentDecomposi
section
noncomputable section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial

namespace GlobalTheory.UnitLemma.TorusPts

section Ring

variable {A : Type} [CommRing A] {I : Type} [Fintype I]

def tt (f h c d : I → A) : A := 1 + ∑ i, ((c i - 1) * f i + (d i - 1) * h i)

theorem f_mul_tt (f h c d : I → A) (hf : ∀ i, f i * f i = f i) (hff : ∀ i j, i ≠ j → f i * f j = 0)
    (hfh : ∀ i j, f i * h j = 0) (j : I) : f j * tt f h c d = c j * f j := by
  classical
  unfold tt
  rw [mul_add, Finset.mul_sum, Finset.sum_eq_single j]
  · linear_combination (c j - 1) * hf j + (d j - 1) * hfh j j
  · intro i _ hi
    linear_combination (c i - 1) * hff j i hi.symm + (d i - 1) * hfh j i
  · simp

theorem tt_swap (f h c d : I → A) : tt f h c d = tt h f d c := by
  unfold tt
  congr 1
  exact Finset.sum_congr rfl fun i _ => add_comm _ _

theorem tt_mul (f h c d c' d' : I → A) (hf : ∀ i, f i * f i = f i) (hff : ∀ i j, i ≠ j → f i * f j = 0)
    (hh : ∀ i, h i * h i = h i) (hhh : ∀ i j, i ≠ j → h i * h j = 0)
    (hfh : ∀ i j, f i * h j = 0) : tt f h c d * tt f h c' d' = tt f h (c * c') (d * d') := by
  have h1 := f_mul_tt f h c' d' hf hff hfh
  have h2 := f_mul_tt h f d' c' hh hhh (fun i j => by rw [mul_comm]; exact hfh j i)
  rw [← tt_swap] at h2
  have h3 : tt f h c d * tt f h c' d' =
      tt f h c' d' + ∑ i, ((c i - 1) * (f i * tt f h c' d') + (d i - 1) * (h i * tt f h c' d')) := by
    conv_lhs => arg 1; unfold tt
    rw [add_mul, one_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h3]
  simp only [h1, h2]
  unfold tt
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by simp only [Pi.mul_apply]; ring

theorem tt_one (f h : I → A) : tt f h 1 1 = 1 := by simp [tt]

end Ring

theorem isIntegral_idem {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {f : A} (hf : f * f = f) :
    IsIntegral O f := by
  nontriviality O
  refine ⟨X ^ 2 - X, ?_, ?_⟩
  · monicity!
  · simp [pow_two, hf]

theorem isIntegral_of_mul_idem {K : UQ} (B : InvAlg K) {f : B.A} (hf : f * f = f) (h0 : f ≠ 0) (x : K.E)
    (hx : IsIntegral K.O (algebraMap K.E B.A x * f)) : IsIntegral K.O x := by
  let J : Ideal B.A := Ideal.span {1 - f}
  have hJ : J ≠ ⊤ := by
    intro h
    have : (1 : B.A) ∈ J := h ▸ Submodule.mem_top
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 this
    apply h0
    linear_combination (-f) * hr - r * hf
  haveI : Nontrivial (B.A ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ
  let φ : K.E →ₐ[K.O] B.A ⧸ J := (Ideal.Quotient.mkₐ K.O J).comp (IsScalarTower.toAlgHom K.O K.E B.A)
  have hinj : Function.Injective φ := φ.toRingHom.injective
  rw [← isIntegral_algHom_iff φ hinj]
  have h1 := hx.map (Ideal.Quotient.mkₐ K.O J)
  have h2 : Ideal.Quotient.mkₐ K.O J (algebraMap K.E B.A x * f) = φ x := by
    show Ideal.Quotient.mk J _ = Ideal.Quotient.mk J (algebraMap K.E B.A x)
    rw [Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton'.2 ⟨-algebraMap K.E B.A x, by ring⟩
  rwa [h2] at h1

theorem le_of_isIntegral {K : UQ} {a : K.O} (ha : K.Small a) (n m : ℕ)
    (h : IsIntegral K.O (((algebraMap K.O K.E a) ^ n)⁻¹ * (algebraMap K.O K.E a) ^ m)) : n ≤ m := by
  by_contra hlt
  push Not at hlt
  obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff).1 h
  have ha0 : algebraMap K.O K.E a ≠ 0 := by
    simpa using ha.1
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
  have h1 : algebraMap K.O K.E (a * (a ^ d * r)) = algebraMap K.O K.E 1 := by
    simp only [map_mul, map_pow, map_one, hr]
    field_simp
    ring
  have h2 := IsFractionRing.injective K.O K.E h1
  exact ha.2.1 (IsUnit.of_mul_eq_one _ h2)

theorem torus_points : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e : ι → B.A) (S : Finset ι) (a : K.O), K.Small a → IsPre B e S → ∀ k : ℕ, ∃ f : ({i // i ∉ S} → Fin (k + 1)) → B.T ⧸ (intUnits K.O B.A).subgroupOf B.T, Function.Injective f ∧ ∀ n, IsIntegral K.O ((((Quotient.out (f n) : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A) := by
  intro K B ι _ e S a ha hP k
  classical
  obtain ⟨hC, hP⟩ := hP
  choose F hFi hF0 _ _ hFS using hP
  let f : {i // i ∉ S} → B.A := fun i => F i
  let h : {i // i ∉ S} → B.A := fun i => B.σ (F i)
  have hf : ∀ i, f i * f i = f i := fun i => hFi i
  have hh : ∀ i, h i * h i = h i := fun i => by
    show B.σ _ * B.σ _ = B.σ _
    rw [← map_mul, hFi i]
  have hfe : ∀ i, f i = f i * e i := fun i => by
    rw [(hFS i i.2).2]
    linear_combination -(hf i) - (hFS i i.2).1
  have hhe : ∀ i, h i = h i * e i := fun i => by
    rw [(hFS i i.2).2]
    linear_combination -(hh i) - (hFS i i.2).1
  have hee : ∀ i j : {i // i ∉ S}, i ≠ j → e i * e j = 0 := fun i j hij =>
    hC.ortho (fun h => hij (Subtype.ext h))
  have hff : ∀ i j, i ≠ j → f i * f j = 0 := fun i j hij => by
    rw [hfe i, hfe j]; linear_combination f i * f j * hee i j hij
  have hhh : ∀ i j, i ≠ j → h i * h j = 0 := fun i j hij => by
    rw [hhe i, hhe j]; linear_combination h i * h j * hee i j hij
  have hfh : ∀ i j, f i * h j = 0 := fun i j => by
    by_cases hij : i = j
    · subst hij; exact (hFS i i.2).1
    · rw [hfe i, hhe j]; linear_combination f i * h j * hee i j hij
  set α : K.E := algebraMap K.O K.E a with hα
  have hα0 : α ≠ 0 := by simpa [hα] using ha.1
  let c : ({i // i ∉ S} → Fin (k + 1)) → {i // i ∉ S} → B.A := fun n i => algebraMap K.E B.A (α ^ (n i : ℕ))
  let d : ({i // i ∉ S} → Fin (k + 1)) → {i // i ∉ S} → B.A := fun n i => algebraMap K.E B.A (α ^ (n i : ℕ))⁻¹
  have hcd : ∀ n, c n * d n = 1 := fun n => by
    funext i
    show algebraMap K.E B.A _ * algebraMap K.E B.A _ = 1
    rw [← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hα0), map_one]
  have hinv : ∀ n, tt f h (c n) (d n) * tt f h (d n) (c n) = 1 := fun n => by
    rw [tt_mul f h _ _ _ _ hf hff hh hhh hfh, hcd, mul_comm (d n), hcd, tt_one]
  have hσ : ∀ n, B.σ (tt f h (c n) (d n)) = tt f h (d n) (c n) := fun n => by
    rw [tt_swap f h (d n)]
    unfold tt
    have hcα : K.c α = α := ha.2.2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_one, map_sum, map_mul, map_sub, c, d, f, h, B.σ_σ, B.σ_alg, map_inv₀, map_pow, hcα]
  let u : ({i // i ∉ S} → Fin (k + 1)) → B.Aˣ := fun n =>
    ⟨tt f h (c n) (d n), tt f h (d n) (c n), hinv n, by rw [mul_comm]; exact hinv n⟩
  let t : ({i // i ∉ S} → Fin (k + 1)) → B.T := fun n => ⟨u n, by
    show tt f h (c n) (d n) * B.σ (tt f h (c n) (d n)) = 1
    rw [hσ, hinv]⟩
  have hαA : algebraMap K.O B.A a = algebraMap K.E B.A α := IsScalarTower.algebraMap_apply _ _ _ _
  have hia : IsIntegral K.O (algebraMap K.E B.A α) := hαA ▸ isIntegral_algebraMap
  have key : ∀ n m, ((t n)⁻¹ * t m) ∈ (intUnits K.O B.A).subgroupOf B.T → ∀ i, (n i : ℕ) ≤ m i := by
    intro n m hnm i
    have h1 : IsIntegral K.O (tt f h (d n) (c n) * tt f h (c m) (d m)) := hnm.1
    rw [tt_mul f h _ _ _ _ hf hff hh hhh hfh] at h1
    have h2 := (isIntegral_idem (O := K.O) (hf i)).mul h1
    rw [f_mul_tt f h _ _ hf hff hfh] at h2
    apply le_of_isIntegral ha
    apply isIntegral_of_mul_idem B (hf i) (hF0 i)
    rw [map_mul]
    exact h2
  refine ⟨fun n => QuotientGroup.mk (t n), ?_, ?_⟩
  · intro n m hnm
    funext i
    exact Fin.ext (le_antisymm (key n m (QuotientGroup.eq.1 hnm) i) (key m n (QuotientGroup.eq.1 hnm.symm) i))
  · intro n
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul ((intUnits K.O B.A).subgroupOf B.T) (t n)
    show IsIntegral K.O (((((QuotientGroup.mk (t n) : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T).out : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)
    rw [hw, Subgroup.coe_mul, mul_inv_rev, Units.val_mul, mul_assoc]
    refine IsIntegral.mul w.2.2 ?_
    show IsIntegral K.O (tt f h (d n) (c n) * _)
    rw [hαA]
    unfold tt
    rw [add_mul, Finset.sum_mul]
    refine IsIntegral.add (by rw [one_mul]; exact hia.pow k) (IsIntegral.sum _ fun i _ => ?_)
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (n i).2)
    have h1 : d n i * algebraMap K.E B.A α ^ k = algebraMap K.E B.A α ^ r := by
      have := congrFun (hcd n) i
      simp only [Pi.mul_apply, Pi.one_apply, c, map_pow] at this
      generalize (n i : ℕ) = j at hr this
      rw [hr, pow_add]
      linear_combination algebraMap K.E B.A α ^ r * this
    have h2 : ((d n i - 1) * f i + (c n i - 1) * h i) * algebraMap K.E B.A α ^ k =
        (algebraMap K.E B.A α ^ r - algebraMap K.E B.A α ^ k) * f i +
          (algebraMap K.E B.A α ^ (n i : ℕ) - 1) * h i * algebraMap K.E B.A α ^ k := by
      rw [← h1]; simp only [c, map_pow]; ring
    rw [h2]
    exact (((hia.pow r).sub (hia.pow k)).mul (isIntegral_idem (hf i))).add
      ((((hia.pow _).sub isIntegral_one).mul (isIntegral_idem (hh i))).mul (hia.pow k))

end GlobalTheory.UnitLemma.TorusPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMatrixFrobenius
section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

namespace GlobalTheory.WachTie.MatF

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ}

open PowerSeries in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) {l : ℕ} in
theorem _root_.GlobalTheory.WachTie.MatF.φD_smulA (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) (a : _root_.Formalism.BasicNotions.LetA O n)
    (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

open PowerSeries in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) {l : ℕ} in
theorem _root_.GlobalTheory.WachTie.MatF.γD_smulA (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) (g : W.Gam) (a : _root_.Formalism.BasicNotions.LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]
  rfl


open PowerSeries in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) {l : ℕ} in
theorem _root_.GlobalTheory.WachTie.MatF.coord_unique (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) {r : ℕ}
    (b : Module.Basis (Fin r) (_root_.Formalism.BasicNotions.LetA O n) ↥(W.N T)) (c d : Fin r → _root_.Formalism.BasicNotions.LetA O n)
    (h : ∑ m, c m • (b m : W.DD T) = ∑ m, d m • (b m : W.DD T)) : c = d := by
  have h' : ∑ m, c m • b m = ∑ m, d m • b m := Subtype.ext (by simpa [Submodule.coe_sum] using h)
  exact b.equivFun.symm.injective (by rw [b.equivFun_symm_apply, b.equivFun_symm_apply]; exact h')

open PowerSeries in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) {l : ℕ} in
theorem _root_.GlobalTheory.WachTie.MatF.exists_coord (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) {r : ℕ}
    (b : Module.Basis (Fin r) (_root_.Formalism.BasicNotions.LetA O n) ↥(W.N T)) (x : W.DD T) (hx : x ∈ W.N T) :
    ∃ c : Fin r → _root_.Formalism.BasicNotions.LetA O n, x = ∑ m, c m • (b m : W.DD T) := by
  refine ⟨b.equivFun ⟨x, hx⟩, ?_⟩
  have h := congrArg Subtype.val (b.sum_equivFun ⟨x, hx⟩)
  rw [Submodule.coe_sum] at h
  simpa only [Submodule.coe_smul] using h.symm

open PowerSeries in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) {l : ℕ} in
theorem _root_.GlobalTheory.WachTie.MatF.exists_matrix_frobenius (R : _root_.GlobalTheory.NB.Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) {r : ℕ}
    (b : Module.Basis (Fin r) (_root_.Formalism.BasicNotions.LetA O n) ↥(W.N T)) (hF : _root_.GlobalTheory.WachTie.FrTie W R j)
    (_hE : _root_.GlobalTheory.WachTie.EETie W R j jE)
    (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T) (hs : W.s = 1) (hu : IsUnit (W.DelF.card : O)) :
    ∃ (M : ℕ) (Φ : ZMod n → Matrix (Fin r) (Fin r) O⟦X⟧),
      (∀ i, ∃ (k : ℕ) (Ψ : Matrix (Fin r) (Fin r) O⟦X⟧),
        Φ i * Ψ = R.E ^ k • (1 : Matrix (Fin r) (Fin r) O⟦X⟧)) ∧
      (∀ k, (fun _ => j R.E : _root_.Formalism.BasicNotions.LetA O n) ^ M • W.φD T (b k : W.DD T) =
        ∑ m, (fun i => j (Φ i m k) : _root_.Formalism.BasicNotions.LetA O n) • (b m : W.DD T)) := by
  classical
  obtain ⟨hj, hrange, -, -, -, -, -, u, hu'⟩ := hF
  set q : _root_.Formalism.BasicNotions.LetA O n := fun _ => W.q₀ with hq
  set e : _root_.Formalism.BasicNotions.LetA O n := fun _ => j R.E with he
  set w : _root_.Formalism.BasicNotions.LetA O n := fun _ => ((u⁻¹ : O⟦X⟧ˣ) : O⟦X⟧) with hw
  have hqe : e = w * q := by
    funext i
    simp only [he, hw, hq, Pi.mul_apply]
    rw [← hu', mul_left_comm, Units.inv_mul, mul_one]
  have hpow : ∀ k (x : W.DD T), ((_root_.Formalism.BasicNotions.letφ (n := n) W.φ₀ ^ (W.s - 1)) fun _ => W.q₀) ^ k • x = q ^ k • x := by
    intro k x
    rw [hs, Nat.sub_self, pow_zero]
    rfl
  have hinv : ∀ y : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ y = y) → j (Function.invFun j y) = y :=
    fun y hy => Function.invFun_eq ((hrange y).2 hy)
  have hγe : ∀ δ ∈ W.DelF, W.γA δ e = e := by
    intro δ hδ
    funext i
    exact (hrange _).1 ⟨_, rfl⟩ δ hδ
  have hbN : ∀ k, (b k : W.DD T) ∈ W.N T := fun k => (b k).2
  have hbΔ : ∀ k, ∀ δ ∈ W.DelF, W.γD T δ (b k) = b k := fun k => (hb k).2
  have hlift : ∀ (f : Fin r → ℕ) (k : Fin r) (x : W.DD T), q ^ f k • x ∈ W.N T →
      e ^ (∑ m, f m) • x ∈ W.N T := by
    intro f k x hx
    have h1 := (W.N T).smul_mem (w ^ (∑ m, f m) * q ^ (∑ m, f m - f k)) hx
    rwa [smul_smul, mul_assoc, ← pow_add,
      Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)),
      ← mul_pow, ← hqe] at h1
  choose nφ hnφ using fun k => W.N_φ T _ (hbN k)
  have hyN : ∀ k, e ^ (∑ m, nφ m) • W.φD T (b k) ∈ W.N T := fun k =>
    hlift nφ k _ (by rw [← hpow]; exact hnφ k)
  set M := ∑ m, nφ m with hM
  choose C hC using fun k => _root_.GlobalTheory.WachTie.MatF.exists_coord W T b _ (hyN k)
  have hCinv : ∀ k m, ∀ δ ∈ W.DelF, W.γA δ (C k m) = C k m := by
    intro k m δ hδ
    have h := congrArg (W.γD T δ) (hC k)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [_root_.GlobalTheory.WachTie.MatF.γD_smulA, map_pow, hγe δ hδ, ← W.φγ_comm, hbΔ k δ hδ, hC k, map_sum] at h
    simp only [_root_.GlobalTheory.WachTie.MatF.γD_smulA, hbΔ _ δ hδ] at h
    exact congrFun (_root_.GlobalTheory.WachTie.MatF.coord_unique W T b _ _ h.symm) m

  choose kk hkk using fun m => W.N_φinv T _ (hbN m)
  have hspan : Submodule.span (_root_.Formalism.BasicNotions.LetA O n) (W.φD T '' W.N T) ≤
      Submodule.span (_root_.Formalism.BasicNotions.LetA O n) (Set.range fun t => W.φD T (b t)) := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := _root_.GlobalTheory.WachTie.MatF.exists_coord W T b y hy
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Submodule.sum_mem _ fun t _ => ?_
    rw [_root_.GlobalTheory.WachTie.MatF.φD_smulA]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  have hA : ∀ m, ∃ a : Fin r → _root_.Formalism.BasicNotions.LetA O n,
      ∑ t, a t • W.φD T (b t) = e ^ (∑ m', kk m') • (b m : W.DD T) := by
    intro m
    rw [← Submodule.mem_span_range_iff_exists_fun]
    apply hspan
    have h1 := (Submodule.span (_root_.Formalism.BasicNotions.LetA O n) (W.φD T '' W.N T)).smul_mem
      (w ^ (∑ m', kk m') * q ^ (∑ m', kk m' - kk m)) (hkk m)
    rw [hpow] at h1
    rwa [smul_smul, mul_assoc, ← pow_add,
      Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)),
      ← mul_pow, ← hqe] at h1
  choose a ha using hA
  set K := ∑ m', kk m' with hK
  set c := e ^ (M + K) with hc
  set P : Matrix (Fin r) (Fin r) (_root_.Formalism.BasicNotions.LetA O n) := Matrix.of fun m k => C k m with hP
  set A : Matrix (Fin r) (Fin r) (_root_.Formalism.BasicNotions.LetA O n) := Matrix.of fun t m => a m t with hAdef
  have hPA : P * A = c • 1 := by
    refine Matrix.ext fun m' m => ?_
    have h : ∑ m'', (∑ t, a m t * C t m'') • (b m'' : W.DD T) =
        ∑ m'', (Pi.single m c : Fin r → _root_.Formalism.BasicNotions.LetA O n) m'' • (b m'' : W.DD T) := by
      simp only [Pi.single_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hc, pow_add, mul_smul, ← ha m, Finset.smul_sum]
      simp_rw [smul_comm (e ^ M) (a m _), hC, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have h2 := congrFun (_root_.GlobalTheory.WachTie.MatF.coord_unique W T b _ _ h) m'
    simp only [Matrix.mul_apply, hP, hAdef, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    rw [Finset.sum_congr rfl fun t _ => mul_comm _ _, h2, Pi.single_apply]
    split_ifs <;> simp

  have hγP : ∀ δ ∈ W.DelF, P.map (W.γA δ) = P := by
    intro δ hδ
    refine Matrix.ext fun m k => ?_
    exact hCinv k m δ hδ
  have hγc : ∀ δ ∈ W.DelF, W.γA δ c = c := by
    intro δ hδ
    rw [hc, map_pow, hγe δ hδ]
  have hdet : P.det * A.det = c ^ r := by
    rw [← Matrix.det_mul, hPA, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hγdetP : ∀ δ ∈ W.DelF, W.γA δ P.det = P.det := by
    intro δ hδ
    have h := RingHom.map_det (W.γA δ : _root_.Formalism.BasicNotions.LetA O n →+* _root_.Formalism.BasicNotions.LetA O n) P
    rw [show (W.γA δ : _root_.Formalism.BasicNotions.LetA O n →+* _root_.Formalism.BasicNotions.LetA O n).mapMatrix P = P from hγP δ hδ] at h
    exact h
  have hγadj : ∀ δ ∈ W.DelF, ∀ x y, W.γA δ (P.adjugate x y) = P.adjugate x y := by
    intro δ hδ x y
    have h := RingHom.map_adjugate (W.γA δ : _root_.Formalism.BasicNotions.LetA O n →+* _root_.Formalism.BasicNotions.LetA O n) P
    rw [show (W.γA δ : _root_.Formalism.BasicNotions.LetA O n →+* _root_.Formalism.BasicNotions.LetA O n).mapMatrix P = P from hγP δ hδ] at h
    exact congrFun (congrFun h x) y
  set v := c ^ r * A.det with hv
  have hγv : ∀ δ ∈ W.DelF, W.γA δ v = v := by
    intro δ hδ
    have h1 : P.det * W.γA δ A.det = P.det * A.det := by
      rw [hdet, ← hγdetP δ hδ, ← map_mul, hdet, map_pow, hγc δ hδ]
    rw [hv, map_mul, map_pow, hγc δ hδ]
    calc c ^ r * W.γA δ A.det = A.det * (P.det * W.γA δ A.det) := by rw [← hdet]; ring
      _ = c ^ r * A.det := by rw [h1, ← hdet]; ring
  set Ψf := v • P.adjugate with hΨf
  have hPΨ : P * Ψf = c ^ (r + r) • 1 := by
    rw [hΨf, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, pow_add, hv, ← hdet]
    congr 1
    ring
  have hγΨ : ∀ δ ∈ W.DelF, ∀ x y, W.γA δ (Ψf x y) = Ψf x y := by
    intro δ hδ x y
    rw [hΨf, Matrix.smul_apply, smul_eq_mul, map_mul, hγv δ hδ, hγadj δ hδ]
  have hjP : ∀ i m k, j (Function.invFun j (P m k i)) = P m k i := fun i m k =>
    hinv _ fun δ hδ => congrFun (hCinv k m δ hδ) i
  have hjΨ : ∀ i x y, j (Function.invFun j (Ψf x y i)) = Ψf x y i := fun i x y =>
    hinv _ fun δ hδ => congrFun (hγΨ δ hδ x y) i
  refine ⟨M, fun i => Matrix.of fun m k => Function.invFun j (P m k i), fun i =>
    ⟨(M + K) * (r + r), Matrix.of fun x y => Function.invFun j (Ψf x y i), ?_⟩, fun k => ?_⟩
  · refine Matrix.ext fun x y => ?_
    apply hj
    have h := congrFun (congrFun (congrFun hPΨ x) y) i
    simp only [Matrix.mul_apply, Finset.sum_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, Pi.mul_apply] at h
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, hjP, hjΨ, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    rw [h]
    split_ifs <;> simp [hc, he, pow_mul]
  · rw [hC k]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    funext i
    exact (hjP i m k).symm

end GlobalTheory.WachTie.MatF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualHaarHyperbolicKernelPsiK
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp

noncomputable def trxForm {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E) (x : A.K) : LinearMap.BilinForm F A.K :=
  LinearMap.mk₂ F (fun u b => Algebra.trace F A.K (x * u * b))
    (fun m₁ m₂ n => by simp [mul_add, add_mul])
    (fun c m n => by simp [mul_smul_comm, smul_mul_assoc])
    (fun m n₁ n₂ => by simp [mul_add])
    (fun c m n => by simp [mul_smul_comm, smul_mul_assoc])

theorem selfDual_kx_exists : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ x : A.Kˣ, ∃ ν : Measure A.K, SelfDual ν (Hyp.kx A ψ x) := by
  intro F E _ _ _ _ _ A ψ hψ x
  have hT := (_root_.GlobalTheory.JR.EtFacts.main F E A).2.2.1
  obtain ⟨hL, -⟩ := hT
  have hsymm : (trxForm A (x : A.K)).IsSymm := by
    refine ⟨fun u b => ?_⟩
    simp only [trxForm, LinearMap.mk₂_apply, RingHom.id_apply]
    ring_nf
  have hleft : ∀ u : A.K, (∀ b, trxForm A (x : A.K) u b = 0) → u = 0 := by
    intro u hu
    have h0 : (x : A.K) * u = 0 := hL _ (fun b => by
      have := hu b
      simpa [trxForm, Algebra.traceForm_apply, mul_assoc] using this)
    have := congrArg (fun t => ((x⁻¹ : A.Kˣ) : A.K) * t) h0
    simpa [← mul_assoc] using this
  have hnd : (trxForm A (x : A.K)).Nondegenerate := by
    refine ⟨hleft, fun b hb => hleft b (fun u => ?_)⟩
    have := hb u
    simp only [trxForm, LinearMap.mk₂_apply] at this ⊢
    rw [show (x : A.K) * b * u = x * u * b by ring]
    exact this
  obtain ⟨⟨μ, hμ, -⟩, -⟩ := _root_.GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest F E ψ hψ A.K (trxForm A (x : A.K)) hsymm hnd
  refine ⟨μ, ?_⟩
  have hk : (fun u b => ψ (trxForm A (x : A.K) u b)) = Hyp.kx A ψ x := by
    funext u b
    simp [trxForm, Hyp.kx, Et.psiK]
  rw [← hk]
  exact hμ

end GlobalTheory.JR.Hyp
end

