module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0098
public import GroundTheory.Brauer.TensorSimple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0091

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechComplexDirectLimit
section
open CategoryTheory Limits Filter

namespace GlobalTheory

namespace CubeColim

variable {ι : Type} [LinearOrder ι] [Fintype ι]

theorem termMap_comp {X Y Z : Cube.{0} ι ℤ} (f : X ⟶ Y) (g : Y ⟶ Z) (p : ℕ)
    (x : Cube.Term X p) :
    Cube.termMap (f ≫ g) p x = Cube.termMap g p (Cube.termMap f p x) := rfl

theorem trans_congr {A : ℕ → Cube.{0} ι ℤ} (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d))
    {j j' c d : ℕ} (h : c + j = d) (h' : c + j' = d) (e : j = j') : μ j c d h = μ j' c d h' := by
  subst e; rfl

theorem nonempty_of_card {m : ℕ} (hm : 0 < m) (s : {s : Finset ι // s.card = m}) :
    s.1.Nonempty :=
  Finset.card_pos.1 (by rw [s.2]; exact hm)

theorem exists_lift {A : ℕ → Cube.{0} ι ℤ} {B : Cube.{0} ι ℤ}
    (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d)) (ρ : ∀ c, A c ⟶ B)
    (h1 : ∀ j c d h, μ j c d h ≫ ρ d = ρ c)
    (h3 : ∀ s : Finset ι, s.Nonempty → ∀ b : B.obj s, ∃ c, ∃ a : (A c).obj s, (ρ c).app s a = b)
    {m : ℕ} (hm : 0 < m) (z : Cube.Term B m) :
    ∃ C, ∃ a : Cube.Term (A C) m, Cube.termMap (ρ C) m a = z := by
  choose c a ha using fun s : {s : Finset ι // s.card = m} => h3 s.1 (nonempty_of_card hm s) (z s)
  have hc : ∀ s, c s + (Finset.univ.sup c - c s) = Finset.univ.sup c := fun s => by
    have := Finset.le_sup (f := c) (Finset.mem_univ s); omega
  refine ⟨Finset.univ.sup c,
    fun s => ((μ _ (c s) _ (hc s)).app s.1).hom (a s), funext fun s => ?_⟩
  have e := congrArg (fun f => (f.app s.1).hom (a s)) (h1 _ (c s) _ (hc s))
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at e
  rw [Cube.termMap_apply, e]
  exact ha s

theorem exists_kill {A : ℕ → Cube.{0} ι ℤ} {B : Cube.{0} ι ℤ}
    (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d)) (ρ : ∀ c, A c ⟶ B)
    (h2 : ∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e),
      μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'')
    (h4 : ∀ s : Finset ι, s.Nonempty → ∀ c (a : (A c).obj s), (ρ c).app s a = 0 →
      ∃ j, (μ j c (c + j) rfl).app s a = 0)
    {m : ℕ} (hm : 0 < m) (c : ℕ) (x : Cube.Term (A c) m) (hx : Cube.termMap (ρ c) m x = 0) :
    ∃ J, Cube.termMap (μ J c (c + J) rfl) m x = 0 := by
  choose j hj using fun s : {s : Finset ι // s.card = m} =>
    h4 s.1 (nonempty_of_card hm s) c (x s) (congrFun hx s)
  refine ⟨Finset.univ.sup j, funext fun s => ?_⟩
  have hle := Finset.le_sup (f := j) (Finset.mem_univ s)
  have hcomp := h2 (j s) (Finset.univ.sup j - j s) c (c + j s) (c + Finset.univ.sup j) rfl
    (by omega) (by omega)
  have e : μ (Finset.univ.sup j) c (c + Finset.univ.sup j) rfl =
      μ (j s + (Finset.univ.sup j - j s)) c (c + Finset.univ.sup j) (by omega) :=
    trans_congr μ _ _ (by omega)
  rw [Cube.termMap_apply, e, ← hcomp]
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  have e : ((μ (j s) c (c + j s) rfl).app s.1).hom (x s) = 0 := hj s
  rw [e, map_zero]
  rfl

theorem exists_cocycle_lift {A : ℕ → Cube.{0} ι ℤ} {B : Cube.{0} ι ℤ}
    (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d)) (ρ : ∀ c, A c ⟶ B)
    (h1 : ∀ j c d h, μ j c d h ≫ ρ d = ρ c)
    (h2 : ∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e),
      μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'')
    (h3 : ∀ s : Finset ι, s.Nonempty → ∀ b : B.obj s, ∃ c, ∃ a : (A c).obj s, (ρ c).app s a = b)
    (h4 : ∀ s : Finset ι, s.Nonempty → ∀ c (a : (A c).obj s), (ρ c).app s a = 0 →
      ∃ j, (μ j c (c + j) rfl).app s a = 0)
    {m : ℕ} (hm : 0 < m) (z : Cube.Term B m) (hz : Cube.d B m z = 0) :
    ∃ C, ∀ c, C ≤ c → ∃ a : Cube.Term (A c) m,
      Cube.termMap (ρ c) m a = z ∧ Cube.d (A c) m a = 0 := by
  obtain ⟨C₀, a, ha⟩ := exists_lift μ ρ h1 h3 hm z
  have hda : Cube.termMap (ρ C₀) (m + 1) (Cube.d (A C₀) m a) = 0 := by
    rw [Cube.termMap_d, ha, hz]
  obtain ⟨J, hJ⟩ := exists_kill μ ρ h2 h4 (Nat.succ_pos m) C₀ _ hda
  refine ⟨C₀ + J, fun c hc => ⟨Cube.termMap (μ (c - C₀) C₀ c (by omega)) m a, ?_, ?_⟩⟩
  · rw [← termMap_comp, h1, ha]
  · rw [← Cube.termMap_d]
    have e : μ (c - C₀) C₀ c (by omega) =
        μ J C₀ (C₀ + J) rfl ≫ μ (c - C₀ - J) (C₀ + J) c (by omega) := by
      rw [h2 J (c - C₀ - J) C₀ (C₀ + J) c rfl (by omega) (by omega)]
      exact trans_congr μ _ _ (by omega)
    rw [e, termMap_comp, hJ, map_zero]

end CubeColim

theorem cechComplex_homology_isZero_of_colimit :
    ∀ {ι : Type} [LinearOrder ι] [Fintype ι] (A : ℕ → Cube.{0} ι ℤ) (B : Cube.{0} ι ℤ) (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d)) (ρ : ∀ c, A c ⟶ B), (∀ j c d h, μ j c d h ≫ ρ d = ρ c) → (∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e), μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'') → (∀ s : Finset ι, s.Nonempty → ∀ b : B.obj s, ∃ c, ∃ a : (A c).obj s, (ρ c).app s a = b) → (∀ s : Finset ι, s.Nonempty → ∀ c (a : (A c).obj s), (ρ c).app s a = 0 → ∃ j, (μ j c (c + j) rfl).app s a = 0) → ∀ n : ℕ, (∀ᶠ c in atTop, IsZero ((cechComplex (A c)).homology n)) → IsZero ((cechComplex B).homology n) := by
  intro ι _ _ A B μ ρ h1 h2 h3 h4 n hn
  obtain ⟨N, hN⟩ := eventually_atTop.1 hn
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  cases n with
  | zero =>
    rw [cochainComplex_exactAt_zero_iff, cechComplex_d B 0]
    change Function.Injective (Cube.d B 1)
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨C, hC⟩ := CubeColim.exists_cocycle_lift μ ρ h1 h2 h3 h4 one_pos z hz
    obtain ⟨a, ha, hda⟩ := hC (max C N) (le_max_left _ _)
    have hex := (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (hN (max C N) (le_max_right _ _))
    rw [cochainComplex_exactAt_zero_iff, cechComplex_d _ 0] at hex
    change Function.Injective (Cube.d (A (max C N)) 1) at hex
    rw [injective_iff_map_eq_zero] at hex
    rw [← ha, hex a hda, map_zero]
  | succ p =>
    rw [cechComplex_exactAt_succ_iff]
    intro z
    refine ⟨fun hz => ?_, ?_⟩
    · obtain ⟨C, hC⟩ := CubeColim.exists_cocycle_lift μ ρ h1 h2 h3 h4 (m := p + 2) (by omega) z hz
      obtain ⟨a, ha, hda⟩ := hC (max C N) (le_max_left _ _)
      have hex := (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
        (hN (max C N) (le_max_right _ _))
      rw [cechComplex_exactAt_succ_iff] at hex
      obtain ⟨y, hy⟩ := (hex a).1 hda
      exact ⟨Cube.termMap (ρ _) (p + 1) y, by rw [← Cube.termMap_d, hy, ha]⟩
    · rintro ⟨y, rfl⟩
      exact Cube.d_d B (p + 1) y

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CenMapTmulEq
section
open scoped TensorProduct

namespace GlobalTheory.CentralizerMapTensor

theorem cenMap_tmul_eq (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (F B : Type) [Field F] [NumberField F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] (x : ℚ_[ℓ]) (f : F) :
    GlobalTheory.LKInvGood.cenMap ℓ F B (x ⊗ₜ[ℚ] f) = x ⊗ₜ[ℚ] algebraMap F B f := rfl

theorem commute_cenMap (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (F B : Type) [Field F] [NumberField F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] (a : ℚ_[ℓ] ⊗[ℚ] F) (y : ℚ_[ℓ] ⊗[ℚ] B) :
    Commute (GlobalTheory.LKInvGood.cenMap ℓ F B a) y := by
  induction a using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Commute.zero_left _
  | add a₁ a₂ h₁ h₂ => rw [map_add (f := _)]; exact h₁.add_left h₂
  | tmul x f =>
    rw [cenMap_tmul_eq]
    induction y using TensorProduct.induction_on with
    | zero => exact Commute.zero_right _
    | add y₁ y₂ h₁ h₂ => exact h₁.add_right h₂
    | tmul z b =>
      unfold Commute SemiconjBy
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        mul_comm x z, Algebra.commutes f b]

end GlobalTheory.CentralizerMapTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CenOrderFinite
section
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory

theorem cenOrder_finite : ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime],
    Module.Finite ℤ_[ℓ] (cenOrder ℓ F) := by
  intro F _ _ ℓ _
  classical
  let f : NumberField.RingOfIntegers F → ℚ_[ℓ] ⊗[ℚ] F := fun a => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (a : F)
  obtain ⟨s, hs⟩ := (inferInstance : Module.Finite ℤ (NumberField.RingOfIntegers F)).fg_top
  have hint : ∀ x ∈ (f '' (s : Set (NumberField.RingOfIntegers F))), IsIntegral ℤ_[ℓ] x := by
    rintro _ ⟨a, -, rfl⟩
    have h1 : IsIntegral ℤ ((a : F)) := NumberField.RingOfIntegers.isIntegral_coe a
    have h2 : IsIntegral ℤ (f a) := by
      have := h1.map ((Algebra.TensorProduct.includeRight : F →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] F).restrictScalars ℤ)
      simpa [f] using this
    exact h2.tower_top
  have hfin : Module.Finite ℤ_[ℓ] (Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F)))) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral ((s.finite_toSet).image f) hint
  have heq : cenOrder ℓ F = Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F))) := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro _ ⟨a, rfl⟩
      let A := Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F)))
      let N : Submodule ℤ (NumberField.RingOfIntegers F) :=
        { carrier := {x | f x ∈ A}
          add_mem' := by
            intro x y hx hy
            simp only [Set.mem_setOf_eq, f, map_add (f := _), TensorProduct.tmul_add] at hx hy ⊢
            exact A.add_mem hx hy
          zero_mem' := by
            simp only [Set.mem_setOf_eq, f, map_zero, TensorProduct.tmul_zero]
            exact A.zero_mem
          smul_mem' := by
            intro c x hx
            simp only [Set.mem_setOf_eq, f, zsmul_eq_mul, map_mul, map_intCast] at hx ⊢
            have : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((c : F) * (x : F)) = c • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (x : F)) := by
              rw [← zsmul_eq_mul, TensorProduct.tmul_smul]
            rw [this]
            exact A.toSubring.zsmul_mem hx c }
      have hsN : (s : Set _) ⊆ N := fun x hx => show f x ∈ A from Algebra.subset_adjoin ⟨x, hx, rfl⟩
      have : a ∈ N := by
        have := Submodule.span_le.mpr hsN
        rw [hs] at this
        exact this Submodule.mem_top
      exact this
    · apply Algebra.adjoin_mono
      rintro _ ⟨a, -, rfl⟩
      exact ⟨a, rfl⟩
  rw [heq]
  exact hfin

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAugmentationSubspaceTopEqKerSmul
section
open scoped TensorProduct
universe u

namespace GlobalTheory.HTRho

theorem mSub_top_eq_ker_smul :
    ∀ (k : Type) [Field k] (C : Type) [CommRing C] (H : Type u) [AddCommGroup H]
      [Module k H] (σ : C →+* Module.End k H) (χ : C →+* k),
      letI : Module (k ⊗[ℤ] C) H := Module.compHom H
        (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom
          (fun _ _ => Algebra.commutes _ _)).toRingHom
      ∀ x : H, x ∈ GlobalTheory.HTRho.mSub σ χ ⊤ ↔
        x ∈ (RingHom.ker (Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom
          (fun _ _ => Commute.all _ _) : k ⊗[ℤ] C →ₐ[k] k) • ⊤ : Submodule (k ⊗[ℤ] C) H) := by
  intro k _ C _ H _ _ σ χ x
  let : Module (k ⊗[ℤ] C) H := Module.compHom H (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H))
      σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)).toRingHom
  let L := Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom
    (fun _ _ => Algebra.commutes _ _)
  set φ : k ⊗[ℤ] C →ₐ[k] k := Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom
    (fun _ _ => Commute.all _ _) with hφdef
  have hsmul : ∀ (a : k ⊗[ℤ] C) (y : H), a • y = L a y := fun _ _ => rfl
  have hLt : ∀ (l : k) (c : C) (y : H), L (l ⊗ₜ c) y = l • σ c y := by
    intro l c y
    exact congrArg (fun f : Module.End k H => f y)
      (Algebra.TensorProduct.lift_tmul (Algebra.ofId k (Module.End k H))
        σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _) l c)
  have hφt : ∀ (l : k) (c : C), φ (l ⊗ₜ c) = l * χ c := by
    intro l c
    simp [hφdef, Algebra.TensorProduct.lift_tmul]
  have key : ∀ (a : k ⊗[ℤ] C) (y : H), L a y - φ a • y ∈ mSub σ χ ⊤ := by
    intro a y
    induction a using TensorProduct.inductionOn with
    | tmul l c =>
      rw [hLt, hφt, mul_smul, ← smul_sub]
      refine Submodule.smul_mem _ l (Submodule.subset_span ⟨c, y, trivial, ?_⟩)
      simp
    | add a b ha hb =>
      rw [map_add L, map_add φ, LinearMap.add_apply, add_smul, add_sub_add_comm]
      exact add_mem ha hb
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, y, -, rfl⟩ := hz
      have hmem : ((1 : k) ⊗ₜ c - (χ c) ⊗ₜ (1 : C)) ∈ RingHom.ker φ := by
        rw [RingHom.mem_ker]
        simp [hφt]
      have := Submodule.smul_mem_smul hmem (Submodule.mem_top (x := y))
      convert this using 1
      rw [hsmul, map_sub, LinearMap.sub_apply, hLt, hLt]
      simp
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul l z _ hz =>
      have : l • z = ((l ⊗ₜ (1 : C) : k ⊗[ℤ] C)) • z := by
        rw [hsmul, hLt]; simp
      rw [this]
      exact Submodule.smul_mem _ _ hz
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun a b ha hb => add_mem ha hb)
    rw [hsmul]
    have := key a y
    rwa [(RingHom.mem_ker).1 ha, zero_smul, sub_zero] at this

end GlobalTheory.HTRho
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyAlgHomEqMapMinpoly
section
open scoped TensorProduct

namespace GlobalTheory.CsaCharpoly
open Polynomial

theorem injective_of_isSimpleRing {R S : Type} [Ring R] [IsSimpleRing R] [Ring S] [Nontrivial S]
    (f : R →+* S) : Function.Injective f := by
  rcases eq_bot_or_eq_top (TwoSidedIdeal.ker f) with h | h
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ TwoSidedIdeal.ker f := (TwoSidedIdeal.mem_ker f).2 hx
    rw [h] at this
    simpa using this
  · exfalso
    have : (1 : R) ∈ TwoSidedIdeal.ker f := by rw [h]; trivial
    rw [TwoSidedIdeal.mem_ker, map_one] at this
    exact one_ne_zero this

theorem natDegree_minpoly_le_one_tmul {F A : Type} [Field F] [Ring A] [Algebra F A] (K : Type)
    [Field K] [Algebra F K] (g : A) (hK : IsIntegral K ((1 : K) ⊗ₜ[F] g)) :
    (minpoly F g).natDegree ≤ (minpoly K ((1 : K) ⊗ₜ[F] g)).natDegree := by
  set x : K ⊗[F] A := (1 : K) ⊗ₜ[F] g with hx
  have hli : LinearIndependent K (fun j : Fin (minpoly F g).natDegree => x ^ (j : ℕ)) := by
    have h := Module.Flat.linearIndependent_one_tmul (S := K) (linearIndependent_pow (K := F) g)
    convert h using 1
    funext j
    simp [hx, Algebra.TensorProduct.tmul_pow]
  by_contra hlt
  push_neg at hlt
  have hsum := aeval_eq_sum_range' hlt x
  rw [minpoly.aeval, ← Fin.sum_univ_eq_sum_range (fun i => (minpoly K x).coeff i • x ^ i)] at hsum
  have hc := Fintype.linearIndependent_iff.mp hli (fun i => (minpoly K x).coeff i) hsum.symm
  apply minpoly.ne_zero hK
  ext i
  rw [coeff_zero]
  by_cases hi : i < (minpoly F g).natDegree
  · exact hc ⟨i, hi⟩
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

end GlobalTheory.CsaCharpoly

namespace GlobalTheory
open Polynomial

theorem charpoly_algHom_eq_map_minpoly : ∀ (F L C : Type) [Field F] [Field L] [Algebra F L] [Ring C]
    [Algebra F C] [Algebra.IsCentral F C] [IsSimpleRing C] [FiniteDimensional F C] (n : ℕ),
    Module.finrank F C = n ^ 2 → ∀ (ι : C →ₐ[F] Matrix (Fin n) (Fin n) L) (y : C),
    (minpoly F y).natDegree = n → (ι y).charpoly = (minpoly F y).map (algebraMap F L) := by
  intro F L C _ _ _ _ _ _ _ _ n _ ι a hdeg
  have ha : IsIntegral F a := IsIntegral.of_finite F a
  have hn : 0 < n := hdeg ▸ minpoly.natDegree_pos ha
  haveI : NeZero n := ⟨hn.ne'⟩
  let g : L ⊗[F] C →ₐ[L] Matrix (Fin n) (Fin n) L :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) ι (fun l y ↦ Algebra.commute_algebraMap_left l _)
  haveI : IsSimpleRing (L ⊗[F] C) := GroundTheory.Brauer.isSimpleRing_tensorProduct_of_right
  have hg : Function.Injective g := GlobalTheory.CsaCharpoly.injective_of_isSimpleRing g.toRingHom
  have eg : g ((1 : L) ⊗ₜ a) = ι a := by
    simp only [g]; erw [Algebra.TensorProduct.lift_tmul]; simp
  have hyi : IsIntegral L ((1 : L) ⊗ₜ[F] a) := IsIntegral.of_finite L _
  have hxi : IsIntegral L (ι a) := IsIntegral.of_finite L _
  have hmin : minpoly L (ι a) = minpoly L ((1 : L) ⊗ₜ[F] a) := by
    rw [← eg]; exact minpoly.algHom_eq g hg _
  have hge : n ≤ (minpoly L (ι a)).natDegree := by
    rw [hmin, ← hdeg]; exact GlobalTheory.CsaCharpoly.natDegree_minpoly_le_one_tmul L a hyi
  have hdvd : minpoly L (ι a) ∣ (minpoly F a).map (algebraMap F L) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hmonic : ((minpoly F a).map (algebraMap F L)).Monic := (minpoly.monic ha).map _
  have hdm : ((minpoly F a).map (algebraMap F L)).natDegree = n := by rw [natDegree_map, hdeg]
  have e1 : (minpoly F a).map (algebraMap F L) = minpoly L (ι a) :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxi) hmonic hdvd (by rw [hdm]; exact hge)
  have e2 : (ι a).charpoly = minpoly L (ι a) :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxi) (Matrix.charpoly_monic _)
      (Matrix.minpoly_dvd_charpoly _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hge)
  rw [e2, e1]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassGroupNthPowerOfCodimOneMod
section
open Polynomial

namespace GlobalTheory.PicDiv

theorem classGroup_nthPower_of_codim_one_mod : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ), 1 ≤ N → (∀ P₀ : Ideal A, P₀.IsMaximal → ∀ h₀ : P₀ ∈ nonZeroDivisors (Ideal A), ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal → a ∉ P → ∀ h : P ∈ nonZeroDivisors (Ideal A), ∃ d : ClassGroup A, ClassGroup.mk0 ⟨P, h⟩ = ClassGroup.mk0 ⟨P₀, h₀⟩ * d ^ N) → (∃ f : A, f ≠ 0 ∧ Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N) → ∀ c : ClassGroup A, ∃ d, c = d ^ N := by
  intro k A _ _ _ _ _ _ N _hN hyp hf c
  obtain ⟨f, hf0, hfm⟩ := hf
  obtain ⟨_hfin, hmax, hadd, _hle⟩ := GlobalTheory.DedekindCodimG.dedekind_finiteType_codim k A
  have nz : ∀ I : Ideal A, I ≠ ⊥ → I ∈ nonZeroDivisors (Ideal A) := fun I hI =>
    mem_nonZeroDivisors_of_ne_zero hI
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  have hI0 : (I : Ideal A) ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
  by_cases hex : ∃ P₀ : Ideal A, P₀.IsMaximal ∧ P₀ ≠ ⊥
  swap
  · push_neg at hex
    have htop : (I : Ideal A) = ⊤ := by
      by_contra h
      obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ h
      exact hI0 (le_bot_iff.mp (hex M hM ▸ hIM))
    refine ⟨1, ?_⟩
    have : I = 1 := Subtype.ext (by rw [htop]; exact Ideal.one_eq_top.symm)
    rw [this, map_one, one_pow]
  obtain ⟨P₀, hP₀, hP₀ne⟩ := hex
  let H : Subgroup (ClassGroup A) := (powMonoidHom N : ClassGroup A →* ClassGroup A).range
  let π : ClassGroup A →* ClassGroup A ⧸ H := QuotientGroup.mk' H
  have hπ : ∀ d : ClassGroup A, π (d ^ N) = 1 := fun d =>
    (QuotientGroup.eq_one_iff _).mpr ⟨d, rfl⟩
  let γ : ClassGroup A := ClassGroup.mk0 ⟨P₀, nz P₀ hP₀ne⟩
  have hbot : ¬ (⊥ : Ideal A).IsMaximal := fun h =>
    hP₀ne (h.eq_of_le hP₀.ne_top bot_le).symm
  have hjac : ∀ x : A, x ≠ 0 → ∃ Q : Ideal A, Q.IsMaximal ∧ x ∉ Q := by
    intro x hx
    haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
    have hj : (⊥ : Ideal A).jacobson = ⊥ :=
      IsJacobsonRing.out' _ (Ideal.isPrime_bot).isRadical
    by_contra hne
    push_neg at hne
    apply hx
    have : x ∈ (⊥ : Ideal A).jacobson := by
      rw [Ideal.jacobson]
      exact Submodule.mem_sInf.mpr fun J hJ => hne J hJ.2
    rw [hj] at this
    exact (Submodule.mem_bot A).mp this
  have hmaxcls : ∀ (P : Ideal A) (hP : P.IsMaximal) (hPne : P ≠ ⊥),
      π (ClassGroup.mk0 ⟨P, nz P hPne⟩) = π γ := by
    intro P hP hPne
    obtain ⟨a₀, ha₀, H0⟩ := hyp P₀ hP₀ (nz P₀ hP₀ne)
    obtain ⟨a₁, ha₁, H1⟩ := hyp P hP (nz P hPne)
    obtain ⟨Q, hQ, hQa⟩ := hjac (a₀ * a₁) (mul_ne_zero ha₀ ha₁)
    have hQne : Q ≠ ⊥ := by rintro rfl; exact hbot hQ
    obtain ⟨d, hd⟩ := H0 Q hQ (fun h => hQa (Q.mul_mem_right _ h)) (nz Q hQne)
    obtain ⟨e, he⟩ := H1 Q hQ (fun h => hQa (Q.mul_mem_left _ h)) (nz Q hQne)
    have h1 := congrArg π hd
    have h2 := congrArg π he
    rw [map_mul, hπ, mul_one] at h1 h2
    rw [← h2, h1]
  have hall : ∀ J : Ideal A, ∀ hJ : J ∈ nonZeroDivisors (Ideal A),
      π (ClassGroup.mk0 ⟨J, hJ⟩) = π γ ^ Module.finrank k (A ⧸ J) := by
    intro J
    refine UniqueFactorizationMonoid.induction_on_prime (P := fun J : Ideal A => ∀ hJ : J ∈ nonZeroDivisors (Ideal A),
      π (ClassGroup.mk0 ⟨J, hJ⟩) = π γ ^ Module.finrank k (A ⧸ J)) J ?_ ?_ ?_
    · intro h; exact absurd rfl (nonZeroDivisors.ne_zero h)
    · intro x hx h
      have hx' : x = ⊤ := Ideal.isUnit_iff.mp hx
      subst hx'
      have e1 : (⟨⊤, h⟩ : nonZeroDivisors (Ideal A)) = 1 := Subtype.ext Ideal.one_eq_top.symm
      haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
      rw [e1, map_one, map_one, Module.finrank_zero_of_subsingleton, pow_zero]
    · intro a p ha hp ih h
      have hpne : p ≠ ⊥ := hp.ne_zero
      have hpmax : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hpne
      have e1 : (⟨p * a, h⟩ : nonZeroDivisors (Ideal A)) = ⟨p, nz p hpne⟩ * ⟨a, nz a ha⟩ := rfl
      rw [e1, map_mul, map_mul, hmaxcls p hpmax hpne, ih (nz a ha), hadd p a hpne ha,
        (hmax p hpmax).1, pow_add, pow_one]
  have hγN : π γ ^ N = 1 := by rw [← map_pow]; exact hπ γ
  have hspan : Ideal.span {f} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hf0
  have hγ1 : π γ = 1 := by
    have e := hall _ (nz _ hspan)
    have e0 : ClassGroup.mk0 (⟨Ideal.span {f}, nz _ hspan⟩ : nonZeroDivisors (Ideal A)) = 1 :=
      (ClassGroup.mk0_eq_one_iff _).mpr ⟨⟨f, rfl⟩⟩
    rw [e0, map_one] at e
    calc π γ = π γ ^ (1 % N) := by rw [← pow_eq_pow_mod 1 hγN, pow_one]
      _ = π γ ^ (Module.finrank k (A ⧸ Ideal.span {f}) % N) := by rw [hfm]
      _ = 1 := by rw [← pow_eq_pow_mod _ hγN, ← e]
  have hc := hall I.1 I.2
  rw [hγ1, one_pow] at hc
  have hmem : ClassGroup.mk0 I ∈ H := (QuotientGroup.eq_one_iff _).mp hc
  obtain ⟨d, hd⟩ := hmem
  exact ⟨d, hd.symm⟩

end GlobalTheory.PicDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMPencil
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory

theorem coefM_pencil : GlobalTheory.PsCo.Cw2a.T_coefM_pencil := by
  intro n L I _ _ A0 B0
  have h := pencil_det_adjugate_coeff (τ := Fin L ⊕ EntIdx n) A0 B0
  simpa only [coefM, muM, inM, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    Polynomial.lcoeff_apply, AlgEquiv.toLinearMap_apply, AlgHom.coe_coe] using h

end GlobalTheory
end

