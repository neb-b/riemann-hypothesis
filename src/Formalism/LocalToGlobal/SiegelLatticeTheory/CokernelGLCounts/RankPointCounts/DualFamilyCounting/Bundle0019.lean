module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0015
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXECPfC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSLocSB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSSplSPf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0008

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LeDualFOfGram
section
open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem isLattice_span {ι' : Type} [Finite ι'] (β : ι' → V)
    (hβ : Submodule.span K (Set.range β) = ⊤) :
    Submodule.IsFullLattice K (Submodule.span (𝓞 K) (Set.range β)) := by
  let : Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range β)) :=
    Submodule.IsLattice.of_fg K (Submodule.fg_span (Set.finite_range β))
  exact { span_eq_top := (Submodule.span_span_of_tower (𝓞 K) K (Set.range β)).trans hβ }

def rdualF (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔭 : Ideal (𝓞 F)) (y : V) : Submodule (𝓞 K) V :=
  (locF 𝔭 (1 : Submodule (𝓞 K) K)).comap ((h y).restrictScalars (𝓞 K))

def ldualF (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔭 : Ideal (𝓞 F)) (x : V) : Submodule (𝓞 K) V where
  carrier := {y | h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add (f := _), LinearMap.add_apply] at *
    exact Submodule.add_mem _ ha hb
  smul_mem' := by
    intro c z hz
    simp only [Set.mem_ofPred_eq] at *
    obtain ⟨r, hr⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range c
    rw [← algebraMap_smul K c z, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
      ← hr, ← smul_eq_mul, algebraMap_smul]
    exact Submodule.smul_mem _ r hz

theorem le_dualF_of_gram (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) {𝔭 : Ideal (𝓞 F)}
    (hp : 𝔭.IsPrime) {ι' : Type} (β : ι' → V)
    (hβ : ∀ i j, h (β i) (β j) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) :
    locF 𝔭 (Submodule.span (𝓞 K) (Set.range β)) ≤
      dualF h 𝔭 (locF 𝔭 (Submodule.span (𝓞 K) (Set.range β))) := by
  have key : ∀ y ∈ Submodule.span (𝓞 K) (Set.range β), ∀ x ∈ Submodule.span (𝓞 K) (Set.range β),
      h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    intro y hy x hx
    have hx' : Submodule.span (𝓞 K) (Set.range β) ≤ rdualF h 𝔭 y := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have hy' : Submodule.span (𝓞 K) (Set.range β) ≤ ldualF h 𝔭 (β j) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hβ i j
      exact hy' hy
    exact hx' hx
  intro x hx
  show ∀ y ∈ _, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
  intro y hy
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp _ x).1 hx
  obtain ⟨s, hs, hsy⟩ := (LocF.mem_locF_iff hp _ y).1 hy
  have := key _ hsy _ htx
  rw [localizedQuotients.form_smul hF] at this
  obtain ⟨u, hu, hux⟩ := (LocF.mem_locF_iff hp _ _).1 this
  refine (LocF.mem_locF_iff hp _ _).2 ⟨u * (s * t), fun hm => ?_, ?_⟩
  · rcases hp.mem_or_mem hm with h1 | h1
    · exact hu h1
    · exact (hp.mem_or_mem h1).elim hs ht
  · rw [Algebra.smul_def] at hux ⊢
    rw [map_mul, map_mul] at hux ⊢
    simpa [mul_assoc, mul_comm, mul_left_comm] using hux

end Formalism.L2.SG.Pf.GluingBases
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemSpanSSelf
section
open Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

section

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem unit_ne {a : K} {k : ℕ} (hu : IsUnitIn S (a * (π ^ k)⁻¹)) : a ≠ 0 := by
  intro ha
  apply hu.1
  rw [ha, zero_mul]

private theorem mem_iff_lemma {ι : Type} [Fintype ι] (b : ι → V) (v : V) :
    v ∈ spanS S b ↔ ∃ c : ι → K, (∀ i, c i ∈ S) ∧ v = ∑ i, c i • b i := Iff.rfl

theorem spanS_empty {ι : Type} [Fintype ι] [IsEmpty ι] (b : ι → V) (v : V) :
    v ∈ spanS S b ↔ v = 0 := by
  rw [mem_iff_lemma]
  constructor
  · rintro ⟨c, -, rfl⟩
    simp
  · rintro rfl
    exact ⟨0, fun _ => S.zero_mem, by simp⟩

theorem mem_spanS_self {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → V) (i : ι) :
    b i ∈ spanS S b := by
  refine (mem_iff_lemma b (b i)).2 ⟨fun j => if j = i then 1 else 0, fun j => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  · simp [ite_smul]

theorem core_empty {ι : Type} [Fintype ι] [IsEmpty ι] (b b' : ι → V) {φ : V ≃ₗ[K] V}
    (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom h) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ Submodule.span K (Set.range b), h w v = 0) → g v = φ v) ∧
      ∀ v, v ∈ spanS S b ↔ g v ∈ spanS S b' := by
  refine ⟨φ, hφ, fun v _ => rfl, fun v => ?_⟩
  rw [spanS_empty b v, spanS_empty b' (φ v)]
  constructor
  · intro h0
    rw [h0, map_zero]
  · intro h0
    apply φ.injective
    rw [h0, map_zero]

private theorem span_ne_eq_cutW_of_orthogonal {ι : Type} [Fintype ι] [DecidableEq ι] {f : ι → V}
    (ho : ∀ i j, i ≠ j → h (f i) (f j) = 0) {i₀ : ι} (hf0 : h (f i₀) (f i₀) ≠ 0) :
    Submodule.span K (Set.range (fun i : {i // i ≠ i₀} => f i)) =
      cutW h (Submodule.span K (Set.range f)) (f i₀) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show f i ∈ Submodule.span K (Set.range f) ⊓ LinearMap.ker (h (f i₀))
    exact Submodule.mem_inf.2 ⟨Submodule.subset_span ⟨i, rfl⟩,
      LinearMap.mem_ker.2 (ho i₀ i (Ne.symm i.2))⟩
  · intro v hv
    have hv' : v ∈ Submodule.span K (Set.range f) ⊓ LinearMap.ker (h (f i₀)) := hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv'
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hv1
    have ha0 : a i₀ = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [LinearMap.mem_ker, map_sum, Finset.sum_eq_single i₀] at hv2
      · rw [map_smul, smul_eq_mul] at hv2
        exact (mul_eq_zero.1 hv2).resolve_right hf0
      · intro i _ hi
        rw [map_smul, ho i₀ i (Ne.symm hi), smul_zero]
      · intro h'
        exact absurd (Finset.mem_univ i₀) h'
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀, ha0, zero_smul, zero_add]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem mem_spanS_iff_smul_add_mem_spanS_ne {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → V) (i₀ : ι)
    (v : V) : v ∈ spanS S f ↔
      ∃ a ∈ S, ∃ w ∈ spanS S (fun i : {i // i ≠ i₀} => f i), v = a • f i₀ + w := by
  rw [mem_iff_lemma]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c i₀, hc i₀, ∑ i : {i // i ≠ i₀}, c i • f i,
      (mem_iff_lemma _ _).2 ⟨fun i => c i, fun i => hc i, rfl⟩, ?_⟩
    exact Fintype.sum_eq_add_sum_subtype_ne _ i₀
  · rintro ⟨a, ha, w, hw, rfl⟩
    rw [mem_iff_lemma] at hw
    obtain ⟨d, hd, rfl⟩ := hw
    refine ⟨fun i => if hi : i = i₀ then a else d ⟨i, hi⟩, fun i => ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact ha
      · exact hd _
    · rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀]
      dsimp only
      rw [dite_eq_left rfl]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [dite_eq_right i.2]

theorem core_of_split (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (hsp : SplitAt S π h) :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ n →
    ∀ (b b' : ι → V) (e : ι → ℕ) (φ : V ≃ₗ[K] V),
    (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i j, i ≠ j → h (b' i) (b' j) = 0) →
    (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
    (∀ i, IsUnitIn S (h (b' i) (b' i) * (π ^ e i)⁻¹)) → φ ∈ Formalism.HermitianLatticesTheory.isom h →
    (∀ v, v ∈ Submodule.span K (Set.range b) ↔ φ v ∈ Submodule.span K (Set.range b')) →
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ Submodule.span K (Set.range b), h w v = 0) → g v = φ v) ∧
      ∀ v, v ∈ spanS S b ↔ g v ∈ spanS S b' := by
  intro n
  induction n with
  | zero =>
    intro ι _ _ hcard b b' e φ _ _ _ _ hφ _
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 (Nat.le_zero.1 hcard)
    exact core_empty b b' hφ
  | succ n ih =>
    intro ι _ _ hcard b b' e φ ho ho' hu hu' hφ hW
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact core_empty b b' hφ
    obtain ⟨i₀, -, hmin⟩ := Finset.exists_min_image Finset.univ e Finset.univ_nonempty
    have hb0 : b i₀ ∈ Submodule.span K (Set.range b) := Submodule.subset_span ⟨i₀, rfl⟩
    have hξ : φ (b i₀) ∈ Submodule.span K (Set.range b') := (hW _).1 hb0
    have hφn : h (φ (b i₀)) (φ (b i₀)) = h (b i₀) (b i₀) := hφ (b i₀) (b i₀)
    obtain ⟨c, hoc, huc, hcc, hspc, hiffc⟩ := hsp ι b' e i₀ ho' hu'
      (fun i => hmin i (Finset.mem_univ i)) (φ (b i₀)) hξ (by rw [hφn]; exact hu i₀)
    have hWc : ∀ v, v ∈ Submodule.span K (Set.range b) ↔
        φ v ∈ Submodule.span K (Set.range c) := by
      intro v
      rw [hspc]
      exact hW v
    obtain ⟨φ', hφ', hφ'0, hcut, hagree⟩ := exists_prep hs hd hφ hWc hb0
      (Submodule.subset_span ⟨i₀, rfl⟩) (by rw [hcc, hφn])
    have hA : h (b i₀) (b i₀) ≠ 0 := unit_ne (hu i₀)
    have hC : h (c i₀) (c i₀) ≠ 0 := unit_ne (huc i₀)
    have hcardS : Fintype.card {i // i ≠ i₀} ≤ n := by
      have := Fintype.card_subtype_lt (p := fun i => i ≠ i₀) (x := i₀) (by simp)
      omega
    have hWbb : ∀ v, v ∈ Submodule.span K (Set.range (fun i : {i // i ≠ i₀} => b i)) ↔
        φ' v ∈ Submodule.span K (Set.range (fun i : {i // i ≠ i₀} => c i)) := by
      intro v
      rw [span_ne_eq_cutW_of_orthogonal ho hA, span_ne_eq_cutW_of_orthogonal hoc hC]
      exact hcut v
    obtain ⟨g, hg, hgagree, hgiff⟩ := ih {i // i ≠ i₀} hcardS (fun i => b i) (fun i => c i)
      (fun i => e i) φ' (fun i j hij => ho i j (fun h' => hij (Subtype.ext h')))
      (fun i j hij => hoc i j (fun h' => hij (Subtype.ext h'))) (fun i => hu i) (fun i => huc i)
      hφ' hWbb
    have hperp : ∀ w ∈ Submodule.span K (Set.range (fun i : {i // i ≠ i₀} => b i)),
        h w (b i₀) = 0 := by
      intro w hw
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hw
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, LinearMap.sum_apply]
      exact Finset.sum_eq_zero fun i _ => by
        rw [map_smulₛₗ, LinearMap.smul_apply, ho i i₀ i.2, smul_zero]
    have hg0 : g (b i₀) = c i₀ := by rw [hgagree _ hperp, hφ'0]
    refine ⟨g, hg, fun v hv => ?_, fun v => ?_⟩
    · have hv' : ∀ w ∈ Submodule.span K (Set.range (fun i : {i // i ≠ i₀} => b i)), h w v = 0 :=
        fun w hw => hv w (Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩) hw)
      rw [hgagree v hv', hagree v hv]
    · rw [← hiffc, mem_spanS_iff_smul_add_mem_spanS_ne b i₀, mem_spanS_iff_smul_add_mem_spanS_ne c i₀]
      constructor
      · rintro ⟨a, ha, w, hw, rfl⟩
        refine ⟨a, ha, g w, (hgiff w).1 hw, ?_⟩
        rw [map_add (f := _), map_smul, hg0]
      · rintro ⟨a, ha, u, hu2, huv⟩
        refine ⟨a, ha, g.symm u, (hgiff _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hu2), ?_⟩
        apply g.injective
        rw [huv, map_add (f := _), map_smul, hg0, LinearEquiv.apply_symm_apply]

end

end Formalism.L2.SG.Pf.G3
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXECPf
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.EC

open Formalism.QuantumDeterminants WlocSk.NB

theorem expChart_of (hS : ShearStep) (hC : ConstStep) : ExpChart := by
  intro k r
  obtain ⟨σ, hσ, hσe⟩ := hS k r
  obtain ⟨Λ, hΛm, hΛ, hvol⟩ := hC k r
  have hE := Formalism.MainNotions.BridgeCSB.continuous_expLie (k := k) (r := r) (Nset k r)
  let Φ : (CI k r → ℂ) × (Fin r → ℝ) → Mt k r := fun t => phi0 t.1 t.2
  have hφ : Continuous Φ := continuous_nilpotent_chart
  unfold Formalism.MainNotions.S.haarLie
  rw [one_smul, hvol, Measure.map_smul, Measure.map_map hE.measurable hΛm, ← hσ.map_eq]
  congr 1
  have e : ((fun x : Formalism.MainNotions.S.lieE (Nset k r) => fun i j =>
      NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) i j) ∘ Λ : (J k r → ℝ) → Mt k r) = Φ ∘ σ := by
    funext y
    simp only [Function.comp, Φ]
    rw [hσe y, hΛ y, Formalism.MainNotions.BridgeCSB.unrealify_RL]
  rw [e]
  exact (Measure.map_map hφ.measurable hσ.measurable).symm
  exact hE.measurable.aemeasurable

end Formalism.L2.SG.Pf.NcReal.JX.EC

namespace Formalism.L2.SG.Pf.NcReal.JX

theorem exponential_chart_haar : ExpChart := EC.expChart_of EC.shear_change_holds EC.constant_change_holds

end Formalism.L2.SG.Pf.NcReal.JX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittSt
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter Matrix
open scoped TensorProduct

def AlgWitt : Prop :=
  ∀ (S : Type) [CommRing S] (s : S →+* S) (O : Subring S), (∀ z, s (s z) = z) → (∀ z ∈ O, s z ∈ O) →
    ∀ (n : ℕ) (J J' : Matrix (Fin n) (Fin n) S), Formalism.UG.IsHerm s J → J' * J = 1 →
    (∀ i j, J i j ∈ O) → (∀ i j, J' i j ∈ O) →
    ∀ (a : ℕ) (β β' : Fin a → S), (∀ i, β i ∈ O) → (∀ i, β' i ∈ O) → (∀ i, β i * β' i = 1) →
    (∀ i, ∀ t ∈ O, ∃ lam ∈ O, lam * s lam = 1 ∧ ∃ c' ∈ O, (β i - s lam * t) * c' = 1) →
    ∀ (x y : Fin a → Fin n → S), (∀ i k, x i k ∈ O) → (∀ i k, y i k ∈ O) →
    (∀ i j, Formalism.UG.hform s J (x i) (x j) = if i = j then β i else 0) →
    (∀ i j, Formalism.UG.hform s J (y i) (y j) = if i = j then β i else 0) →
    ∃ g : GL (Fin n) S, g ∈ Formalism.UG.UJ s J ∧ (∀ i j, (g : Matrix (Fin n) (Fin n) S) i j ∈ O) ∧
      (∀ i j, ((g⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) i j ∈ O) ∧
      ∀ i, (g : Matrix (Fin n) (Fin n) S) *ᵥ y i = x i

def HermDiag : Prop :=
  ∀ (K : Type) [Field K] (σ : K →+* K), (∀ z, σ (σ z) = z) → (2 : K) ≠ 0 →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) K), Formalism.UG.IsHerm σ J →
    ∀ (a : ℕ) (X0 : Fin a → Fin n → K),
    (Matrix.of fun i j => Formalism.UG.hform σ J (X0 i) (X0 j)).det ≠ 0 →
    ∃ P Q : Matrix (Fin a) (Fin a) K, Q * P = 1 ∧
      (∀ i j, i ≠ j → Formalism.UG.hform σ J (∑ l, P i l • X0 l) (∑ l, P j l • X0 l) = 0) ∧
      ∀ i, Formalism.UG.hform σ J (∑ l, P i l • X0 l) (∑ l, P i l • X0 l) ≠ 0

def LamAE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ δ : E, σ δ = δ → δ ≠ 0 →
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ t ∈ OEv (E := E) v,
      ∃ lam ∈ OEv (E := E) v, lam * sigR (Fv F v) σ lam = 1 ∧
        ∃ c' ∈ OEv (E := E) v, (inclR (Fv F v) δ - sigR (Fv F v) σ lam * t) * c' = 1

end Formalism.L2.SG.Pf.NcS.IntWittPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSWittLoc
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.WittLocPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

theorem local_witt_theorem : Formalism.L2.SG.Pf.NcS.LocSBPf.WittLocT := by
  intro F E _ _ _ _ _ σ n J a X0 hCM hJ hdet v X hX
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set Y := ratTup (F := F) (Fv F v) X0 with hYdef
  have hYG : gramR (Fv F v) σ J Y = (gramE σ J X0).map (inclR (F := F) (Fv F v)) :=
    PI.VolStabS.LocPosW.gramR_ratTup (Fv F v) σ J X0
  have hunit : IsUnit ((gramE σ J X0).map (inclR (F := F) (Fv F v))).det := by
    have e : ((gramE σ J X0).map (inclR (F := F) (Fv F v))).det = inclR (F := F) (Fv F v) (gramE σ J X0).det :=
      (RingHom.map_det (inclR (F := F) (Fv F v)) (gramE σ J X0)).symm
    rw [e]
    exact (Ne.isUnit hdet).map (inclR (F := F) (Fv F v))
  have hYind : LinearIndependent (Fv F v ⊗[F] E) Y :=
    PI.VolStabS.linIndep_of_isUnit_det (Fv F v) σ J Y (hYG ▸ hunit)
  have hXind : LinearIndependent (Fv F v ⊗[F] E) X :=
    PI.VolStabS.linIndep_of_isUnit_det (Fv F v) σ J X (hX ▸ hunit)
  by_cases hK : IsField (Fv F v ⊗[F] E)
  · letI : Field (Fv F v ⊗[F] E) := hK.toField
    have hσ : ∀ x, σ (σ x) = x := PI.VolStabS.sigma_invol_cm σ hCM
    have hinv : ∀ x, sigR (Fv F v) σ (sigR (Fv F v) σ x) = x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r t => simp [sigR, hσ]
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    letI : StarRing (Fv F v ⊗[F] E) := PI.VolStabS.starOfInv (sigR (Fv F v) σ) hinv
    haveI : CharZero (Fv F v ⊗[F] E) :=
      charZero_of_injective_algebraMap (algebraMap F (Fv F v ⊗[F] E)).injective
    have hs : starRingEnd (Fv F v ⊗[F] E) = sigR (Fv F v) σ := RingHom.ext fun _ => rfl
    have hJ' : ∀ i j, starRingEnd (Fv F v ⊗[F] E) (JR (F := F) (Fv F v) J j i) = JR (F := F) (Fv F v) J i j := by
      intro i j
      rw [hs]
      simp only [JR, Matrix.map_apply]
      rw [(fun x => by simp [sigR, inclR] : ∀ x : E, sigR (Fv F v) σ (inclR (F := F) (Fv F v) x) =
        inclR (F := F) (Fv F v) (σ x)), hJ.1 i j]
    have hdetJ : (JR (F := F) (Fv F v) J).det ≠ 0 := by
      have e : (JR (F := F) (Fv F v) J).det = inclR (F := F) (Fv F v) J.det := by
        rw [RingHom.map_det]
        rfl
      rw [e]
      intro h
      apply hJ.2
      exact (inclR (F := F) (Fv F v)).injective (h.trans (map_zero _).symm)
    have hGg : ∀ i j, Formalism.UG.hform (starRingEnd (Fv F v ⊗[F] E)) (JR (F := F) (Fv F v) J) (X i) (X j) =
        Formalism.UG.hform (starRingEnd (Fv F v ⊗[F] E)) (JR (F := F) (Fv F v) J) (Y i) (Y j) := by
      intro i j
      rw [hs]
      exact congrFun (congrFun (hX.trans hYG.symm) i) j
    obtain ⟨g, hg, hgX⟩ := PI.VolStabS.witt_tuple (JR (F := F) (Fv F v) J) hJ' hdetJ Y X hYind hXind hGg
    rw [hs] at hg
    exact ⟨⟨g, hg⟩, funext fun i => hgX i⟩
  · obtain ⟨π₁, π₂, h1, h2, -, h4, h5⟩ := Formalism.L2.SG.Pf.NcS.LT.splitStr σ v hCM hK
    exact Formalism.L2.SG.Pf.NcS.LT.WSp.witt_split σ J hJ v π₁ π₂ h1 h2 h4 h5 Y X hYind hXind (hYG.trans hX.symm)

end Formalism.L2.SG.Pf.NcS.WittLocPf
end
end

