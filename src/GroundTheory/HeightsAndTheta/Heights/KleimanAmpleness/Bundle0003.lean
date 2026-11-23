module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDefs
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CoordIdealIsMultiProjPrime
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Objects
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellMeets
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

variable (S : Type) [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
  [Field Ω] [Algebra S Ω]

def CellMeets (y : (Σ k, ι k) → Ω) (I : ∀ k, Finset (ι k)) : Prop :=
  ∀ k, ∀ i ∈ I k, y ⟨k, i⟩ ≠ 0

open scoped Classical

open Classical in
def cellSec (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (I : ∀ k, Finset (ι k)) : Submodule S Ω :=
  if CellMeets y I then
    Submodule.span S {z | ∃ (g t : MRingOver S ι) (a : K → ℕ),
      t ∈ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S I ∧ IsMultiHomog t a ∧ (∀ k, 0 ≤ γ k + a k) ∧
        IsMultiHomog g (fun k => (γ k + a k).toNat) ∧ z = aeval y g / aeval y t}
  else ⊥

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]


open Classical in
def cellD (y : (Σ k, ι k) → Ω) (n : ℕ) :
    (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) →ₗ[S] (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι (n + 1) → Ω) :=
  LinearMap.pi fun I => if CellMeets y I.1 then ∑ k, ∑ i ∈ I.1 k,
    if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.faceSign I.1 k i •
        LinearMap.proj (R := S) (φ := fun _ : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n => Ω)
          ⟨Function.update I.1 k ((I.1 k).erase i), h⟩
    else 0
  else 0

def cellC (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (n : ℕ) :
    Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) :=
  Submodule.pi Set.univ fun I => cellSec S y γ I.1

def cellZ (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (n : ℕ) :
    Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) :=
  cellC S y γ n ⊓ LinearMap.ker (cellD S y n)

def cellB (y : (Σ k, ι k) → Ω) (γ : K → ℤ) :
    (n : ℕ) → Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω)
  | 0 => ⊥
  | n + 1 => (cellC S y γ n).map (cellD S y n)

abbrev cellH (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (n : ℕ) : Type :=
  ↥(cellZ S y γ n) ⧸ (cellB S y γ n).comap (cellZ S y γ n).subtype

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CoordIdealXgen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def SerreVanish.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ)
    (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (G : GradedMod S N M), Module.Finite (Poly S N) M →
    ∃ c₀ : ℤ, ∀ (i : ℕ), 1 ≤ i → ∀ c : ℤ, c₀ ≤ c → Subsingleton (gradedH S N M G i c)

section Inhabitants

variable (k : Type) [Field k]

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.EqZeroOrIsHomogeneousOfMemPolyPiece
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

open MvPolynomial

noncomputable section

section Graded

variable (S : Type) [CommRing S] (N : ℕ)

theorem mem_polyPiece_of_isHomogeneous {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) :
    f ∈ IndefiniteRowSideFullHecke.Kleiman.polyPiece S N e := by
  rw [IndefiniteRowSideFullHecke.Kleiman.polyPiece, mem_weightedHomogeneousSubmodule]
  exact isWeightedHomogeneous_int_of_isHomogeneous hf

theorem eq_zero_or_isHomogeneous_of_mem_polyPiece {f : Poly S N} {d : ℤ}
    (hf : f ∈ IndefiniteRowSideFullHecke.Kleiman.polyPiece S N d) :
    f = 0 ∨ ∃ e : ℕ, (e : ℤ) = d ∧ f.IsHomogeneous e := by
  classical
  rw [IndefiniteRowSideFullHecke.Kleiman.polyPiece, mem_weightedHomogeneousSubmodule] at hf
  have hw : ∀ s : Fin (N + 1) →₀ ℕ,
      Finsupp.weight (fun _ : Fin (N + 1) => (1 : ℤ)) s = ((Finsupp.weight (1 : Fin (N + 1) → ℕ) s : ℕ) : ℤ) := by
    intro s
    simp [Finsupp.weight_apply, Finsupp.sum]
  by_cases h0 : f = 0
  · exact Or.inl h0
  · right
    obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.mp h0
    refine ⟨Finsupp.weight (1 : Fin (N + 1) → ℕ) s, ?_, ?_⟩
    · rw [← hw]; exact hf hs
    · intro t ht
      have h1 := hf ht
      have h2 := hf hs
      rw [hw] at h1 h2
      exact_mod_cast h1.trans h2.symm

variable (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]

def gradedEquiv : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M ≃ Kleiman.GradedPMod S N M where
  toFun G :=
    { piece := G.piece
      isInternal := G.internal
      smul_mem := fun d c p m hp hm => by
        rw [add_comm]
        exact G.smul_mem d c p (mem_polyPiece_of_isHomogeneous S N hp) m hm }
  invFun G :=
    { piece := G.piece
      internal := G.isInternal
      smul_mem := fun d c f hf m hm => by
        rcases eq_zero_or_isHomogeneous_of_mem_polyPiece S N hf with rfl | ⟨e, rfl, he⟩
        · rw [zero_smul]; exact zero_mem _
        · rw [add_comm]; exact G.smul_mem e c f m he hm }
  left_inv _ := rfl
  right_inv _ := rfl

end Graded

section Charts

variable (S : Type) [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω]

theorem pow_div_mem_chartRingI (x : Fin (N + 1) → Ω) (I : Kleiman.Chart x) (i₀ : Fin (N + 1))
    {s : Poly S N} (hs : s ∈ Kleiman.monos I.1) :
    ∃ e : ℕ, s.IsHomogeneous e ∧ x i₀ ^ e / aeval x s ∈ IndefiniteRowSideFullHecke.Kleiman.chartRingI S x I.1 := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨1, isHomogeneous_X S i, ?_⟩
    rw [pow_one, aeval_X]
    exact Algebra.subset_adjoin ⟨i, hi, i₀, rfl⟩
  | one => exact ⟨0, isHomogeneous_one _ _, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨e, hae, hea⟩ := ha
    obtain ⟨e', hbe, heb⟩ := hb
    refine ⟨e + e', hae.mul hbe, ?_⟩
    have : x i₀ ^ (e + e') / aeval x (a * b) = (x i₀ ^ e / aeval x a) * (x i₀ ^ e' / aeval x b) := by
      rw [map_mul, pow_add, mul_div_mul_comm]
    rw [this]
    exact mul_mem hea heb

theorem chartRingI.equiv (x : Fin (N + 1) → Ω) (I : Kleiman.Chart x) :
    IndefiniteRowSideFullHecke.Kleiman.chartRingI S x I.1 = Kleiman.chartRing S x I := by
  apply le_antisymm
  · rw [IndefiniteRowSideFullHecke.Kleiman.chartRingI, Algebra.adjoin_le_iff]
    rintro _ ⟨i, hi, j, rfl⟩
    exact ⟨X j, X i, 1, Kleiman.X_mem_monos hi, isHomogeneous_X S j, isHomogeneous_X S i, by simp⟩
  · rintro _ ⟨f, s, e, hs, hf, hse, rfl⟩
    obtain ⟨i₀, hi₀⟩ := I.2.1
    have hx₀ : x i₀ ≠ 0 := (Kleiman.mem_support x).mp (I.2.2 hi₀)
    have hs0 : aeval x s ≠ 0 := Kleiman.eval_ne_zero_of_mem_monos I hs
    have hsne : s ≠ 0 := fun h => hs0 (by rw [h, map_zero])
    obtain ⟨e', hse', hmem⟩ := pow_div_mem_chartRingI S x I i₀ hs
    have hee : e = e' := hse.inj_right hse' hsne
    subst hee
    have hall : ∀ g : Poly S N, aeval (fun l => x l / x i₀) g ∈ IndefiniteRowSideFullHecke.Kleiman.chartRingI S x I.1 := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C a => rw [aeval_C]; exact Subalgebra.algebraMap_mem _ a
      | add p q hp hq => rw [map_add]; exact add_mem hp hq
      | mul_X p i hp =>
        rw [map_mul, aeval_X]
        exact mul_mem hp (Algebra.subset_adjoin ⟨i₀, hi₀, i, rfl⟩)
    have hf' : aeval x f / x i₀ ^ e ∈ IndefiniteRowSideFullHecke.Kleiman.chartRingI S x I.1 := by
      rw [← Kleiman.aeval_div_of_isHomogeneous hf i₀]
      exact hall f
    have heq : aeval x f / aeval x s = (aeval x f / x i₀ ^ e) * (x i₀ ^ e / aeval x s) := by
      field_simp
    rw [heq]
    exact mul_mem hf' hmem

theorem chartRing.equiv (x : Fin (N + 1) → Ω) {i : Fin (N + 1)} (hi : x i ≠ 0) :
    ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i = Kleiman.chartRing S x (Kleiman.singleChart hi) := by
  rw [← IndefiniteRowSideFullHecke.Kleiman.chartRingI_singleton, ← chartRingI.equiv]
  rfl

end Charts

section Families

variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
variable {E : Type} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]



omit [Module S E] [IsScalarTower S Ω E] in
theorem mem_twist_twistSys_iff (F : Kleiman.SubSystem S x E) (c : ℤ) (I : Kleiman.Chart x)
    {i : Fin (N + 1)} (hi : i ∈ I.1) (z : E) :
    z ∈ (F.twist (Kleiman.twistSys S x c)).sub I ↔ ∃ y ∈ F.sub I, z = x i ^ c • y := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨q, hq, y, hy, rfl⟩ := hz
      change q ∈ Kleiman.twistMod S x c I at hq
      rw [Kleiman.twistMod_eq_span c I hi, Submodule.mem_span_singleton] at hq
      obtain ⟨a, rfl⟩ := hq
      refine ⟨a • y, Submodule.smul_mem _ a hy, ?_⟩
      rw [Kleiman.chartRing_smul_def, mul_smul]
      exact smul_comm _ _ _
    | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
    | add a b _ _ ha hb =>
      obtain ⟨y, hy, rfl⟩ := ha
      obtain ⟨y', hy', rfl⟩ := hb
      exact ⟨y + y', add_mem hy hy', (smul_add _ _ _).symm⟩
    | smul a w _ hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      refine ⟨a • y, Submodule.smul_mem _ a hy, ?_⟩
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_comm]
  · rintro ⟨y, hy, rfl⟩
    refine Submodule.subset_span ⟨x i ^ c, ?_, y, hy, rfl⟩
    change x i ^ c ∈ Kleiman.twistMod S x c I
    rw [Kleiman.twistMod_eq_span c I hi]
    exact Submodule.mem_span_singleton_self _

end Families

section Filtration

variable (S : Type) [CommRing S] (N : ℕ)
variable {M : Type} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]

end Filtration

end

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem AmpleCover.sub_twist (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = F.sub I * Q.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ _ = _
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_mul, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩; exact ⟨y, hy, q, hq, mul_comm _ _⟩
  · rintro ⟨y, hy, q, hq, rfl⟩; exact ⟨q, hq, y, hy, mul_comm _ _⟩

theorem AmpleCover.sub_pow (Q : SubSystem S x Ω) (n : ℕ) (I : Chart x) :
    (Q.pow n).sub I = Q.sub I ^ n := by
  induction n with
  | zero =>
    obtain ⟨i, hi⟩ := I.2.1
    rw [pow_zero]
    change twistMod S x 0 I = 1
    rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]
  | succ n ih =>
    change ((Q.pow n).twist Q).sub I = _
    rw [AmpleCover.sub_twist, ih, pow_succ]

theorem AmpleCover.proof : AmpleCover.Statement.{u, w} := by
  intro S _ Ω _ _ N x H A F hF I
  set R := chartRing S x I
  set G : Submodule R Ω := Submodule.span R (F.secs : Set Ω)
  set P : Submodule R Ω := H.sub I
  refine le_antisymm (Submodule.span_le.mpr fun z hz => ?_) fun y hy => ?_
  · exact (Submodule.mem_iInf _).mp hz I
  obtain ⟨Q', hQ'⟩ := H.invertible I
  have hpow : ∀ n, (H.pow n).sub I = P ^ n := fun n => AmpleCover.sub_pow H.toSubSystem n I
  have hone : ∀ n, P ^ n * Q' ^ n = 1 := fun n => by rw [← mul_pow, hQ', one_pow]

  set c : Ideal R := G.comap (LinearMap.toSpanSingleton R Ω y)
  set V : Submodule R Ω := Submodule.map (Algebra.linearMap R Ω) c.radical
  have hkey : P ^ A.m * Q' ^ A.m ≤ V := by
    rw [← hpow, ← A.generates I, Submodule.mul_le]
    intro u hu w hw
    have hmem : ∀ j, A.h j * w ∈ V := by
      intro j
      have h1 : A.h j * w ∈ (1 : Submodule R Ω) := by
        rw [← hone A.m, ← hpow]
        exact Submodule.mul_mem_mul (by rw [← A.generates I]; exact Submodule.subset_span ⟨j, rfl⟩) hw
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp h1
      obtain ⟨e, he⟩ := hF j I y hy
      refine ⟨a, ⟨e, ?_⟩, ha⟩
      change a ^ e • y ∈ G
      have hw' : w ^ e ∈ Q' ^ (A.m * e) := by
        rw [pow_mul]; exact Submodule.pow_mem_pow _ hw e
      have h2 : (y * A.h j ^ e) * w ^ e ∈ G * P ^ (A.m * e) * Q' ^ (A.m * e) :=
        Submodule.mul_mem_mul (by rw [← hpow]; exact he) hw'
      rw [mul_assoc, hone, mul_one] at h2
      rw [Algebra.smul_def, map_pow]
      change ((a : Ω)) ^ e * y ∈ G
      have : (a : Ω) = A.h j * w := ha
      rw [this]
      convert h2 using 1
      ring
    refine Submodule.span_induction (p := fun u _ => u * w ∈ V) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨j, rfl⟩; exact hmem j
    · rw [zero_mul]; exact V.zero_mem
    · intro a b _ _ ha hb; rw [add_mul]; exact V.add_mem ha hb
    · intro r a _ ha; rw [smul_mul_assoc]; exact V.smul_mem r ha
  obtain ⟨b, ⟨n, hn⟩, hb⟩ := hkey (by rw [hone]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩)
  have hb1 : (b : Ω) = 1 := hb
  have hbn : b ^ n • y ∈ G := hn
  rwa [Algebra.smul_def, map_pow, show algebraMap R Ω b = 1 from hb1, one_pow, one_mul] at hbn

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleTwistLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace AmpleTwistLocal

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem mem_chartRing_of_mem_zero {I : Chart x} {q : Ω} (hq : q ∈ twistMod S x 0 I) :
    q ∈ chartRing S x I := by
  refine Submodule.span_induction (p := fun q _ => q ∈ chartRing S x I) ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨f, s, e, e', hs, hf, hse, he, rfl⟩
    have hee : e' = e := by omega
    subst hee
    exact ⟨f, s, e', hs, hf, hse, rfl⟩
  · exact Subalgebra.zero_mem _
  · intro a b _ _ ha hb; exact Subalgebra.add_mem _ ha hb
  · intro a q _ hq
    rw [chartRing_smul_def]
    exact Subalgebra.mul_mem _ a.2 hq

theorem mul_mem_pow (H : SubSystem S x Ω) (I : Chart x) {c : ℕ} {z : Ω}
    (hz : z ∈ (H.pow c).sub I) (d : ℕ) {w : Ω} (hw : w ∈ (H.pow d).sub I) :
    z * w ∈ (H.pow (c + d)).sub I := by
  induction d generalizing w with
  | zero =>
    change w ∈ twistMod S x 0 I at hw
    have h := Submodule.smul_mem ((H.pow c).sub I)
      (⟨w, mem_chartRing_of_mem_zero hw⟩ : chartRing S x I) hz
    rw [chartRing_smul_def] at h
    rwa [Nat.add_zero, mul_comm]
  | succ d ih =>
    change w ∈ Submodule.span _ _ at hw
    refine Submodule.span_induction
      (p := fun w _ => z * w ∈ ((H.pow (c + d)).twist H).sub I) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨q, hq, y, hy, rfl⟩
      refine Submodule.subset_span ⟨q, hq, z * y, ih hy, ?_⟩
      simp only [smul_eq_mul]; ring
    · rw [mul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [mul_add]; exact Submodule.add_mem _ ha hb
    · intro a w _ hw
      rw [chartRing_smul_def, mul_left_comm, ← chartRing_smul_def]
      exact Submodule.smul_mem _ a hw

theorem pow_mem_pow (H : SubSystem S x Ω) (I : Chart x) {m : ℕ} {h : Ω}
    (hh : h ∈ (H.pow m).sub I) (n : ℕ) : h ^ n ∈ (H.pow (m * n)).sub I := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact one_mem_twistMod_zero I
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact mul_mem_pow H I ih m hh

theorem mul_mem_twist_pow (Q H : SubSystem S x Ω) (I : Chart x) {c d : ℕ} {z w : Ω}
    (hz : z ∈ (Q.twist (H.pow c)).sub I) (hw : w ∈ (H.pow d).sub I) :
    z * w ∈ (Q.twist (H.pow (c + d))).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction
    (p := fun z _ => z * w ∈ (Q.twist (H.pow (c + d))).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    refine Submodule.subset_span ⟨q * w, mul_mem_pow H I hq d hw, y, hy, ?_⟩
    simp only [smul_eq_mul]; ring
  · rw [zero_mul]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [add_mul]; exact Submodule.add_mem _ ha hb
  · intro a z _ hz
    rw [chartRing_smul_def, mul_assoc, ← chartRing_smul_def]
    exact Submodule.smul_mem _ a hz

theorem proof (hA : AmpleAffineGen.Statement.{u, w}) : AmpleTwistLocal.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x H A Q b j
  classical
  by_cases h0 : A.h j = 0
  · refine ⟨0, fun n _ I y _ => ⟨1, ?_⟩⟩
    rw [h0, pow_one, mul_zero]
    exact Submodule.zero_mem _
  obtain ⟨p, s, hs, hgen⟩ := hA S Ω N x H A Q b j h0
  have hhI : ∀ I : Chart x, A.h j ∈ (H.pow A.m).sub I := fun I =>
    (Submodule.mem_iInf _).mp (A.mem_secs j) I
  choose k hk using hs
  refine ⟨Finset.univ.sup fun q : Fin p × Chart x => k q.1 q.2, fun n hn I y hy => ?_⟩
  have hglob : ∀ t, s t * A.h j ^ n ∈ (Q.twist (H.pow (b + A.m * n))).secs := by
    intro t
    refine (Submodule.mem_iInf _).mpr fun I' => ?_
    have hle : k t I' ≤ n := le_trans
      (Finset.le_sup (f := fun q : Fin p × Chart x => k q.1 q.2) (Finset.mem_univ (t, I'))) hn
    have h1 := mul_mem_twist_pow Q.toSubSystem H.toSubSystem I' (hk t I')
      (pow_mem_pow H.toSubSystem I' (hhI I') (n - k t I'))
    have e1 : s t * A.h j ^ k t I' * A.h j ^ (n - k t I') = s t * A.h j ^ n := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]
    have e2 : b + A.m * k t I' + A.m * (n - k t I') = b + A.m * n := by
      rw [add_assoc, ← mul_add, Nat.add_sub_cancel' hle]
    rw [e1, e2] at h1
    exact h1
  have hpn : A.h j ^ n ≠ 0 := pow_ne_zero n h0
  obtain ⟨e, g, hg, hz⟩ := hgen I (y / A.h j ^ n) n (by rwa [div_mul_cancel₀ y hpn])
  refine ⟨e, ?_⟩
  have hy' : y = A.h j ^ n * ∑ t, g t * s t := by
    rw [← hz]; field_simp
  rw [hy', Finset.mul_sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun t _ => ?_
  have e3 : A.h j ^ n * (g t * s t) * A.h j ^ e = (s t * A.h j ^ n) * (g t * A.h j ^ e) := by ring
  rw [e3]
  exact Submodule.mul_mem_mul (Submodule.subset_span (hglob t)) (hg t)

end AmpleTwistLocal

end

end GroundTheory.Heights₂.Heights.Kleiman
end

