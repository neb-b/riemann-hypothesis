module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FamilyLeCoords
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.CupPair
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

section Abstract

variable {k : Type} [Field k] {M M' M₁ M₂ M₃ : Type} [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']
  [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂] [AddCommGroup M₃] [Module k M₃]

structure Cx (k M : Type) [Field k] [AddCommGroup M] [Module k M] where

  C : ℤ → Submodule k M

  D : M →ₗ[k] M

namespace Cx

def IsCx (K : Cx k M) : Prop := ∀ n, ∀ a ∈ K.C n, K.D a ∈ K.C (n + 1) ∧ K.D (K.D a) = 0

def Z (K : Cx k M) (n : ℤ) : Submodule k M := K.C n ⊓ LinearMap.ker K.D

def B (K : Cx k M) (n : ℤ) : Submodule k M := (K.C (n - 1)).map K.D

abbrev H (K : Cx k M) (n : ℤ) : Type := K.Z n ⧸ (K.B n).submoduleOf (K.Z n)

end Cx

def Adj (K : Cx k M) (L : Cx k M') (β : M →ₗ[k] M' →ₗ[k] k) (N : ℤ) : Prop :=
  ∀ n, ∃ ε : ℤˣ, ∀ a ∈ K.C n, ∀ b ∈ L.C (N - n - 1), β (K.D a) b = ε • β a (L.D b)

def IsMap (K : Cx k M) (L : Cx k M') (f : M →ₗ[k] M') : Prop := ∀ n, ∀ a ∈ K.C n, f a ∈ L.C n ∧ f (K.D a) = L.D (f a)

def pt (k : Type) [Field k] : Cx k k := ⟨fun n => if n = 0 then ⊤ else ⊥, 0⟩

end Abstract

section Cech

variable {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [Module k E]


variable (k ι E) in
def deltaL : (Finset ι → E) →ₗ[k] (Finset ι → E) where
  toFun := GlobalTheory.DI.delta
  map_add' a b := by
    funext t
    simp [GlobalTheory.DI.delta, Finset.sum_add_distrib]
  map_smul' r a := by
    funext t
    simp only [GlobalTheory.DI.delta, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

def cechC (F : Finset ι → Submodule k E) (n : ℤ) : Submodule k (Finset ι → E) :=
  Submodule.pi Set.univ fun s => if s.Nonempty ∧ (s.card : ℤ) = n + 1 then F s else ⊥

def cech (F : Finset ι → Submodule k E) : Cx k (Finset ι → E) := ⟨cechC F, deltaL k ι E⟩

def totD (d : E →ₗ[k] E) : (Finset ι → E) →ₗ[k] (Finset ι → E) :=
  deltaL k ι E + LinearMap.pi fun s => ((-1 : ℤ) ^ s.card) • (d ∘ₗ LinearMap.proj s)

def totC (T : ℕ → Finset ι → Submodule k E) (a b : ℕ) (n : ℤ) : Submodule k (Finset ι → E) :=
  Submodule.pi Set.univ fun s =>
    if s.Nonempty ∧ (a : ℤ) ≤ n + 1 - s.card ∧ n + 1 - s.card < b then T (n + 1 - s.card).toNat s else ⊥

def cupPair [Fintype ι] {E' : Type} [AddCommGroup E'] [Module k E'] (β : E →ₗ[k] E' →ₗ[k] k) :
    (Finset ι → E) →ₗ[k] (Finset ι → E') →ₗ[k] k :=
  ∑ j : ι, β.compl₁₂ (LinearMap.proj (Finset.univ.filter (· ≤ j))) (LinearMap.proj (Finset.univ.filter (j ≤ ·)))

end Cech

section Alg

variable {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [Ring E] [Algebra k E]

end Alg

end GlobalTheory.PD
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
section
namespace GlobalTheory.OTY

open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

def jz (A : WeightedAtlas n Y ι La) (z : Y → V n) (i : ι) (y : Y) : V n →L[ℂ] V n :=
  fderiv ℂ (z ∘ (A.chart i).symm) (A.chart i y)

def jdet (A : WeightedAtlas n Y ι La) (z : Y → V n) : ι → Y → ℂ :=
  fun i y => (jz A z i y).det

structure Etale (A : WeightedAtlas n Y ι La) (U : Set Y) (z : Y → V n) : Prop where
  isOpen : IsOpen U
  holo : ∀ i, DifferentiableOn ℂ (z ∘ (A.chart i).symm)
    ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)
  det_ne : ∀ i y, y ∈ U → y ∈ (A.chart i).source → jdet A z i y ≠ 0

def nz (A : WeightedAtlas n Y ι La) (τ : ι → Y → ℂ) : Set Y := {y | τ (A.pick y) y ≠ 0}

structure Cover (A : WeightedAtlas n Y ι La) where

  m : ℕ

  idx : Fin m → ι

  c : Fin m → V n

  r : Fin m → ℝ

  chi : Fin m → Y → ℝ
  r_pos : ∀ a, 0 < r a
  sub : ∀ a, Metric.closedBall (c a) (r a) ⊆ (A.chart (idx a)).target
  smooth : ∀ a, A.SmoothFn (chi a)
  supp : ∀ a, tsupport (chi a) ⊆
    (A.chart (idx a)).source ∩ A.chart (idx a) ⁻¹' Metric.ball (c a) (r a)
  nonneg : ∀ a y, 0 ≤ chi a y
  sum_one : ∀ y, ∑ a, chi a y = 1

def n0 (A : WeightedAtlas n Y ι La) (la : La) (F : ι → Y → ℂ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + la) F y) ∂A.mu

def n1 {A : WeightedAtlas n Y ι La} (C : Cover A) (la : La) (F : ι → Y → ℂ) : ℝ≥0∞ :=
  ∑ a, ∫⁻ v in Metric.ball (C.c a) (C.r a), ENNReal.ofReal
    ((∑ j, ‖wdb n j (F (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
      Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))

def CurvGe {A : WeightedAtlas n Y ι La} (C : Cover A) (la : La) (t : ℝ) : Prop :=
  ∀ a, ∀ v ∈ Metric.ball (C.c a) (C.r a), ∀ ξ : Fin n → ℂ,
    t * ∑ j, ‖ξ j‖ ^ 2 ≤ A.leviAt (C.idx a) (A.ph la (C.idx a)) ((A.chart (C.idx a)).symm v) ξ

def glue {A : WeightedAtlas n Y ι La} (C : Cover A) (la : La) (u : Fin C.m → V n → ℂ) :
    ι → Y → ℂ :=
  fun i y => ∑ a, (C.chi a y : ℂ) * A.g (A.kap + la) i (C.idx a) y * u a (A.chart (C.idx a) y)

def wT (T x : ℝ) : ℝ := 1 / (1 + min (x ^ 2) ((T + 1) ^ 2))

def IsCut (T : ℝ) (θ : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) θ ∧ (∀ x, x ≤ -T - 1 → θ x = 1) ∧ (∀ x, -T + 1 ≤ x → θ x = 0) ∧
    (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) ∧ ∀ x, |deriv θ x| ≤ 3 / 4

end

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
section
set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology

namespace GlobalTheory.AnPer.Charts

open CategoryTheory GlobalTheory.CatCoh

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}


set_option autoImplicit false in
open TopologicalSpace Filter Topology in
open CategoryTheory in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} {K : _root_.GlobalTheory.AnPer.Charts F} in
theorem _root_.GlobalTheory.AnPer.Charts.tsze_nil {O : Type} [CommRing O] [Algebra ℂ O] :
    IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom ℂ O (Fin g → O)).toRingHom) := by
  refine ⟨2, ?_⟩
  rw [pow_two, Submodule.zero_eq_bot, ← le_bot_iff, Ideal.mul_le]
  intro x hx y hy
  rw [RingHom.mem_ker] at hx hy
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, TrivSqZeroExt.fstHom_apply] at hx hy
  rw [Ideal.mem_bot]
  ext <;> simp [hx, hy]


variable (K) in
@[reducible] def jet (k : K.K) : K.Obj where
  k := k
  C := TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))
  alg := ((TrivSqZeroExt.inlHom _ _).comp (K.cst k)).toAlgebra
  J := RingHom.ker (TrivSqZeroExt.fstHom ℂ (Hol (K.W k)) (Fin g → Hol (K.W k))).toRingHom
  nil := tsze_nil
  ρ := TrivSqZeroExt.inlHom _ _
  ρ_cst _ := rfl

def tszeSec {O : Type} [CommRing O] [Algebra ℂ O] (D : Fin g → Derivation ℂ O O) : O →+* TrivSqZeroExt O (Fin g → O) where
  toFun h := TrivSqZeroExt.inl h + TrivSqZeroExt.inr fun a ↦ D a h
  map_one' := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp)
  map_zero' := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp)
  map_add' x y := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp)
  map_mul' x y := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp)


set_option autoImplicit false in
open TopologicalSpace Filter Topology in
open CategoryTheory in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} {K : _root_.GlobalTheory.AnPer.Charts F} in
theorem _root_.GlobalTheory.AnPer.Charts.fst_tszeSec {O : Type} [CommRing O] [Algebra ℂ O]
    (D : Fin g → Derivation ℂ O O) (h : O) :
    (_root_.GlobalTheory.AnPer.Charts.tszeSec D h).fst = h := by
  simp [_root_.GlobalTheory.AnPer.Charts.tszeSec]


set_option autoImplicit false in
open TopologicalSpace Filter Topology in
open CategoryTheory in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} {K : _root_.GlobalTheory.AnPer.Charts F} in
theorem _root_.GlobalTheory.AnPer.Charts.snd_tszeSec {O : Type} [CommRing O] [Algebra ℂ O]
    (D : Fin g → Derivation ℂ O O) (h : O) (a : Fin g) :
    (_root_.GlobalTheory.AnPer.Charts.tszeSec D h).snd a = D a h := by
  simp [_root_.GlobalTheory.AnPer.Charts.tszeSec]

def jetSec (k : K.K) : Hol (K.W k) →+* TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)) := tszeSec dw


set_option autoImplicit false in
open TopologicalSpace Filter Topology in
open CategoryTheory in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} {K : _root_.GlobalTheory.AnPer.Charts F} in
theorem _root_.GlobalTheory.AnPer.Charts.tsze_expand {O : Type} [CommRing O] (h : O) (v : Fin g → O) :
    (TrivSqZeroExt.inl h + TrivSqZeroExt.inr v : TrivSqZeroExt O (Fin g → O)) = TrivSqZeroExt.inl h +
      ∑ a, TrivSqZeroExt.inl (v a) * TrivSqZeroExt.inr (Pi.single a (1 : O)) := by
  congr 1
  simp only [TrivSqZeroExt.inl_mul_inr]
  ext b
  · simp [TrivSqZeroExt.fst_sum]
  · simp [TrivSqZeroExt.snd_sum, Finset.sum_apply, Pi.single_apply]

def jet0 (k : K.K) : K.Hom (K.triv k) (K.jet k) :=
  ptHom (K.jet k) (K.le_refl k)

def jet1 (k : K.K) : K.Hom (K.triv k) (K.jet k) :=
  fromTriv (K.jet k) (K.le_refl k) (jetSec k)
    (fun f ↦ TrivSqZeroExt.ext (fst_tszeSec _ _) (funext fun a ↦ (snd_tszeSec _ _ a).trans (dw_cst k a f)))
    (Relation.ReflTransGen.single ⟨fun a ↦ TrivSqZeroExt.inr (Pi.single a 1), fun _ ↦ rfl,
      fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _, fun h ↦ by
        simp only [RingHom.comp_apply, sh_refl]
        exact tsze_expand h fun a ↦ dw a h⟩)

end GlobalTheory.AnPer.Charts
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
section
noncomputable section

open WittVector Ideal Matrix GlobalTheory.Sandwich TensorProduct

namespace GlobalTheory.DetInv

variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

variable (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ]

variable {p O Λ}

abbrev rhoTA {ε : PreTilt O p} {h : ℕ} (D : Datum ε h Λ) (l : Λ) :
    Matrix (Fin h) (Fin h) (Ainf p O) := (D.ρT l).map (ofPadic p O)

end GlobalTheory.DetInv
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsStrictlySemistableIff
section
noncomputable section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.SSG

def ChartAt {O : Type} [CommRing O] (ϖ : O) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O)) (x : X) : Prop :=
  ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U) (m r : ℕ) (_ : 1 ≤ r) (_ : r ≤ m)
    (ψ : (MvPolynomial (Fin m) O ⧸ Ideal.span (Set.singleton
      ((∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) -
        MvPolynomial.C ϖ))) →+* Γ(X, U)),
    ψ.Etale ∧ ψ.comp (algebraMap O _) = ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ p.appLE ⊤ U le_top).hom

end GlobalTheory.SSG

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.TorusNoLeClassNoRankOne
section
noncomputable section

namespace GlobalTheory.UCls.Model

open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
variable (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)

theorem isUA_mul {g h : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUA c G g) (hh : IsUA c G h) :
    IsUA c G (g * h) :=
  ⟨by rw [det_mul]; exact hg.1.mul hh.1, fun x y => by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hg.2, hh.2]⟩

theorem isUA_inv {g : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUA c G g) : IsUA c G g⁻¹ :=
  ⟨isUnit_nonsing_inv_det g hg.1, fun x y => by
    rw [← hg.2, mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv g hg.1, one_mulVec, one_mulVec]⟩

theorem IsKM_maps {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) {x : Fin n → RA F E}
    (hx : x ∈ hat F L) : k *ᵥ x ∈ hat F L := by
  obtain ⟨y, hy, e⟩ := hk.2.1 x hx
  have : k *ᵥ x = M • y + x := by rw [← e]; abel
  rw [this]
  exact add_mem (nsmul_mem hy M) hx

theorem isKM_mul {k h : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) (hh : IsKM c G L M h) :
    IsKM c G L M (k * h) := by
  refine ⟨isUA_mul c G hk.1 hh.1, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, e⟩ := hk.2.1 _ (IsKM_maps c G L M hh hx)
    obtain ⟨z, hz, e'⟩ := hh.2.1 x hx
    refine ⟨y + z, add_mem hy hz, ?_⟩
    rw [← mulVec_mulVec, smul_add, ← e, ← e']; abel
  · obtain ⟨y, hy, e⟩ := hk.2.2 x hx
    obtain ⟨z, hz, e'⟩ := hh.2.2 y hy
    exact ⟨z, hz, by rw [← mulVec_mulVec, e', e]⟩

theorem isKM_inv {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) : IsKM c G L M k⁻¹ := by
  have hi : ∀ z, k⁻¹ *ᵥ (k *ᵥ z) = z := fun z => by
    rw [mulVec_mulVec, nonsing_inv_mul k hk.1.1, one_mulVec]
  refine ⟨isUA_inv c G hk.1, fun x hx => ?_, fun x hx => ⟨k *ᵥ x, IsKM_maps c G L M hk hx, hi x⟩⟩
  obtain ⟨z, hz, e⟩ := hk.2.2 x hx
  obtain ⟨y, hy, e'⟩ := hk.2.1 z hz
  refine ⟨-y, neg_mem hy, ?_⟩
  rw [← e, hi, smul_neg, ← e']; abel

theorem one_tmul_injective : Function.Injective fun x : E => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x := by
  have hA : Function.Injective (algebraMap F (FiniteAdeleRing (𝓞 F) F)) := by
    obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.1 (RingOfIntegers.not_isField F)
    let v : HeightOneSpectrum (𝓞 F) := ⟨p, hp, hp0⟩
    haveI : Nontrivial (FiniteAdeleRing (𝓞 F) F) := ⟨0, 1, fun h => by
      have := congrArg (fun a : FiniteAdeleRing (𝓞 F) F => a v) h
      exact zero_ne_one (α := v.adicCompletion F) this⟩
    exact (algebraMap F _).injective
  exact Algebra.TensorProduct.includeRight_injective hA

theorem ratM_det (γ : Matrix (Fin n) (Fin n) E) :
    (ratM F γ).det = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ γ.det :=
  (AlgHom.map_det (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) γ).symm

end GlobalTheory.UCls.Model
end
end

