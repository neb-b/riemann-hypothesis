module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfEqv
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0018
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.TmulMkLMemInvLOfValAtMemFilC
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0017

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfBA
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O}

theorem framepf_βα_core (Bs : FramepfBas W T) (π' Eπ : LetA O n) (h' M : ℕ)
    (c : ZMod n) (huE : IsUnit (algebraMap (LetA O n) W.EE Eπ))
    (eb : Module.Basis (Fin Bs.r) O (LcQ W T π' c)) (P R S : Fin Bs.r → Fin Bs.r → LetA O n)
    (hS : ∀ m k, S m k ∈ W.AΔ) (lam : O) (hPR : ∀ j k, ∑ m, P j m * R m k =
      (if j = k then algebraMap O (LetA O n) lam * letE c else 0) + π' ^ M * Eπ ^ (4 * h') * S j k)
    (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c)
    (hΨ : ∀ e j, Ψ (e ⊗ₜ eb j) = e • ∑ m, R m j • W.φD T (Bs.b m))
    (hΦ : ∀ a : Fin Bs.r → LetA O n, Φ (∑ k, a k • W.φD T (Bs.b k)) =
      ∑ j, algebraMap (LetA O n) W.EE (∑ k, a k * P j k) ⊗ₜ eb j)
    (x : LA W T π' c) (hx : x ∈ LamLA W T π' Eπ h' c ⊤) :
    Φ (Ψ x) - lam • x ∈ JLA W T π' Eπ h' M c := by
  choose a haΔ ha using (framepf_mem_toLA π' c eb _).1 hx
  have hee : (letE c : LetA O n) * letE c = letE c := Formalism.MainNotions.LiftingTheory.wmap_letE_idem c
  have hx' : algebraMap (LetA O n) W.EE (Eπ ^ h') • x =
      ∑ k, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a k) ⊗ₜ[O] eb k := by
    rw [← framepf_smulLA_alg, ← (Algebra.TensorProduct.basis W.EE eb).sum_repr (smulLA W T π' c _ x)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ha, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hm : ∀ j, ∑ k, a k * S j k ∈ W.AΔ := fun j =>
    Subalgebra.sum_mem _ fun k _ => W.AΔ.mul_mem (haΔ k) (hS j k)
  refine ⟨∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * ∑ k, a k * S j k) ⊗ₜ[O] eb j,
    ⟨∑ j, (⟨_, hm j⟩ : ↥W.AΔ) ⊗ₜ ⟨eb j, trivial⟩, by rw [map_sum]; rfl⟩, ?_⟩
  obtain ⟨Λ, hΛ⟩ : IsUnit (algebraMap (LetA O n) W.EE (Eπ ^ h')) := by rw [map_pow]; exact huE.pow _
  have hcan : ∀ z z' : LA W T π' c, algebraMap (LetA O n) W.EE (Eπ ^ h') • z =
      algebraMap (LetA O n) W.EE (Eπ ^ h') • z' → z = z' := by
    intro z z' h
    have := congrArg (fun w => ((Λ⁻¹ : W.EEˣ) : W.EE) • w) h
    simpa only [← hΛ, smul_smul, Units.inv_mul, one_smul] using this
  apply hcan
  have h1 : Ψ (algebraMap (LetA O n) W.EE (Eπ ^ h') • x) =
      ∑ m, (∑ k, (letE c : LetA O n) * a k * R m k) • W.φD T (Bs.b m) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx', map_sum]
    simp only [hΨ, algebraMap_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_smul.symm
  have h3 : ∀ j, ∑ m, (∑ k, (letE c : LetA O n) * a k * R m k) * P j m =
      algebraMap O (LetA O n) lam * ((letE c : LetA O n) * a j) +
        Eπ ^ h' * (π' ^ M * Eπ ^ (3 * h') * ((letE c : LetA O n) * ∑ k, a k * S j k)) := by
    intro j
    have : ∑ m, (∑ k, (letE c : LetA O n) * a k * R m k) * P j m =
        ∑ k, (letE c : LetA O n) * a k * ∑ m, P j m * R m k := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    simp only [hPR, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
    congr 1
    · linear_combination (algebraMap O (LetA O n) lam * a j) * hee
    · exact Finset.sum_congr rfl fun k _ => by ring
  rw [smul_sub, ← map_smul Φ, ← map_smul Ψ, h1, hΦ, smul_comm _ lam x, hx', framepf_smulLA_alg,
    Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h3, ← algebraMap_smul W.EE lam, IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
  simp only [TensorProduct.smul_tmul', smul_eq_mul]
  rw [← TensorProduct.sub_tmul, ← map_mul, ← map_mul, ← map_mul, ← map_sub, add_sub_cancel_left]

end Local

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfF
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

def WD : Prop :=
  ∀ τ ζ, Pt c ζ τ → ∀ {m m' : ℕ} (a : Fin m → LetA O n) (y : Fin m → W.DD T)
    (hy : ∀ j, y j ∈ NcS W T (c - 1)) (b : Fin m' → LetA O n) (z : Fin m' → W.DD T)
    (hz : ∀ k, z k ∈ NcS W T (c - 1)),
    ∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) ⊗ₜ[O] mkL W T π' c (y j) (hy j) =
      ∑ k, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * b k) ⊗ₜ[O] mkL W T π' c (z k) (hz k) →
    expS W T c ζ a y = expS W T c ζ b z

theorem expS_alg_mul (ζ : LL) (o : O) {m : ℕ} (a : Fin m → LetA O n) (y : Fin m → W.DD T) :
    expS W T c ζ (fun j => algebraMap O (LetA O n) o * a j) y = algebraMap O LL o • expS W T c ζ a y := by
  funext i
  simp only [expS, serC, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs
  · rw [map_mul, AlgHom.commutes, PowerSeries.algebraMap_apply, PowerSeries.coeff_C_mul, mul_smul]
  · rw [smul_zero]

theorem good_all (hwd : WD W T Pt π' c) {x : LA W T π' c} (hx : x ∈ NL W T Pt π' Eπ h' c)
    {m : ℕ} {a : Fin m → ↥W.AΔ} {y : Fin m → W.DD T} (hr : IsRepL W T π' Eπ h' c x a y) :
    ∀ τ ζ, Pt c ζ τ → ∀ i : ℤ, expS W T c ζ (fun j => (a j : LetA O n)) y i ∈
      Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (h' - i) := by
  have hrep : x ∈ NLset W T Pt π' Eπ h' c := by
    clear hr
    induction hx using Submodule.span_induction with
    | mem x hx => exact hx
    | zero =>
      refine ⟨0, Fin.elim0, Fin.elim0, ⟨fun j => j.elim0, by simp⟩, fun τ ζ _ i => ?_⟩
      simp [expS]
    | add x₁ x₂ _ _ h₁ h₂ =>
      obtain ⟨m₁, a₁, y₁, ⟨hy₁, he₁⟩, hg₁⟩ := h₁
      obtain ⟨m₂, a₂, y₂, ⟨hy₂, he₂⟩, hg₂⟩ := h₂
      let z : Fin (m₁ + m₂) → ↥(NcS W T (c - 1)) :=
        Fin.append (fun j => ⟨y₁ j, hy₁ j⟩) (fun j => ⟨y₂ j, hy₂ j⟩)
      refine ⟨m₁ + m₂, Fin.append a₁ a₂, fun j => z j, ⟨fun j => (z j).2, ?_⟩, fun τ ζ hpt i => ?_⟩
      · rw [map_add (f := _), he₁, he₂, Fin.sum_univ_add]
        simp only [z, Fin.append_left, Fin.append_right]
      · simpa only [expS, Fin.sum_univ_add, z, Fin.append_left, Fin.append_right] using
          Submodule.add_mem _ (hg₁ τ ζ hpt i) (hg₂ τ ζ hpt i)
    | smul o x _ hx =>
      obtain ⟨m, a, y, ⟨hy, he⟩, hg⟩ := hx
      refine ⟨m, fun j => o • a j, y, ⟨hy, ?_⟩, fun τ ζ hpt i => ?_⟩
      · rw [map_smul, he, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [TensorProduct.smul_tmul', Subalgebra.coe_smul, mul_smul_comm]
        simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
      · simp only [Subalgebra.coe_smul]
        simpa only [Algebra.smul_def, expS_alg_mul, Pi.smul_apply] using
          Submodule.smul_mem _ (algebraMap O LL o) (hg τ ζ hpt i)
  obtain ⟨m', a', y', ⟨hy', hx'⟩, hg⟩ := hrep
  obtain ⟨hy, hxr⟩ := hr
  intro τ ζ hpt i
  rw [hwd τ ζ hpt _ y hy _ y' hy' (hxr.symm.trans hx')]
  exact hg τ ζ hpt i

theorem nl_le : NL W T Pt π' Eπ h' c ≤ LamLA W T π' Eπ h' c ⊤ := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨m, a, y, ⟨hy, hx⟩, -⟩
  refine ⟨∑ j, a j ⊗ₜ ⟨mkL W T π' c (y j) (hy j), Submodule.mem_top⟩, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, hx]
  rfl

theorem nl_smulA {b : LetA O n} (hb : b ∈ W.AΔ) {x : LA W T π' c} (hx : x ∈ NL W T Pt π' Eπ h' c) :
    smulLA W T π' c b x ∈ NL W T Pt π' Eπ h' c := by
  have htmul (a : LetA O n) (e : W.EE) (z : LcQ W T π' c) :
      smulLA W T π' c a (e ⊗ₜ z) = (algebraMap (LetA O n) W.EE a * e) ⊗ₜ z := rfl
  have hcomm (x : LA W T π' c) :
      smulLA W T π' c (Eπ ^ h') (smulLA W T π' c b x) =
        smulLA W T π' c b (smulLA W T π' c (Eπ ^ h') x) := by
    induction x using TensorProduct.inductionOn with
    | tmul e z => simp only [htmul, mul_left_comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, a, y, ⟨hy, he⟩, hg⟩ := hx
    refine Submodule.subset_span
      ⟨m, fun j => ⟨b * a j, W.AΔ.mul_mem hb (a j).2⟩, y, ⟨hy, ?_⟩, fun τ ζ hpt => ?_⟩
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [hcomm, he, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [htmul, ← map_mul]
      congr 2
      ring
    · exact MLB.goodF_mul W T c ζ τ h' b _ y (hg τ ζ hpt)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx => rw [LinearMap.map_smul]; exact Submodule.smul_mem _ _ hx

theorem nl_sat (hwd : WD W T Pt π' c) (hp : algebraMap O LL ((PD.p : ℕ) : O) ≠ 0)
    {x : LA W T π' c} (hx : x ∈ LamLA W T π' Eπ h' c ⊤) (k : ℕ)
    (hk : ((PD.p : ℕ) : O) ^ k • x ∈ NL W T Pt π' Eπ h' c) : x ∈ NL W T Pt π' Eπ h' c := by
  have hrep : ∃ (m : ℕ) (a : Fin m → ↥W.AΔ) (y : Fin m → W.DD T), IsRepL W T π' Eπ h' c x a y := by
    obtain ⟨t, ht⟩ := hx
    obtain ⟨m, a, s, rfl⟩ := MLE.exists_fin_sum t
    have hs : ∀ j, ∃ z : ↥(NcS W T (c - 1)), Submodule.Quotient.mk z =
        ((s j : ↥(⊤ : Submodule O _)) : LcQ W T π' c) := fun j => Submodule.Quotient.mk_surjective _ _
    choose z hz using hs
    refine ⟨m, a, fun j => z j, ⟨fun j => (z j).2, ?_⟩⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← ht, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) ⊗ₜ
      ((s j : ↥(⊤ : Submodule O _)) : LcQ W T π' c) = _
    rw [← hz j]
    rfl
  obtain ⟨m, a, y, hy, he⟩ := hrep
  let o : O := ((PD.p : ℕ) : O) ^ k
  have hr' : IsRepL W T π' Eπ h' c (o • x) (fun j => o • a j) y := by
    refine ⟨hy, ?_⟩
    rw [map_smul, he, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.smul_tmul', Subalgebra.coe_smul, mul_smul_comm]
    simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
  have hg := good_all W T Pt π' Eπ h' c hwd hk hr'
  refine Submodule.subset_span ⟨m, a, y, ⟨hy, he⟩, fun τ ζ hpt i => ?_⟩
  have h1 := hg τ ζ hpt i
  simp only [Subalgebra.coe_smul] at h1
  simp only [Algebra.smul_def, expS_alg_mul, Pi.smul_apply] at h1
  have ho : algebraMap O LL o ≠ 0 := by simpa only [o, map_pow] using pow_ne_zero k hp
  exact (Submodule.smul_mem_iff _ ho).1 h1

end Generic

end Formalism.MainNotions.N.Ln34.MLF

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.SpanLeRange
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalFiltration

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.N.Ln34.ModelFPf
open scoped TensorProduct

section Span2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL)

theorem N_φ' (x : W.DD T) (hx : x ∈ W.N T) : ∃ k : ℕ, W.Q ^ k • W.φD T x ∈ W.N T :=
  W.N_φ T x hx

theorem Qpow_mono {x : W.DD T} {k K : ℕ} (hk : W.Q ^ k • W.φD T x ∈ W.N T) (hK : k ≤ K) :
    W.Q ^ K • W.φD T x ∈ W.N T := by
  rw [show K = (K - k) + k by omega, pow_add, mul_smul]
  exact Submodule.smul_mem _ _ hk

theorem LV_zero (K : ℕ) : LV W T c ζ K 0 = 0 := by
  have h0 : W.Q ^ K • W.φD T 0 ∈ W.N T := by rw [map_zero, smul_zero]; exact Submodule.zero_mem _
  rw [LV_eq W T c ζ K _ h0]
  rw [show (⟨_, h0⟩ : ↥(W.N T)) = 0 from Subtype.ext (by simp), map_zero]
  rfl

theorem LV_sum {ι : Type} (K : ℕ) (s : Finset ι) (f : ι → W.DD T)
    (hf : ∀ i, W.Q ^ K • W.φD T (f i) ∈ W.N T) :
    W.Q ^ K • W.φD T (∑ i ∈ s, f i) ∈ W.N T ∧
      LV W T c ζ K (∑ i ∈ s, f i) = ∑ i ∈ s, LV W T c ζ K (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by rw [Finset.sum_empty, map_zero, smul_zero]; exact Submodule.zero_mem _, ?_⟩
    rw [Finset.sum_empty, Finset.sum_empty, LV_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨by rw [map_add (f := _), smul_add]; exact Submodule.add_mem _ (hf a) ih.1, ?_⟩
    rw [LV_add W T c ζ K _ _ (hf a) ih.1, ih.2]

theorem letE_idem (d : ZMod n) : (letE d : LetA O n) * letE d = letE d := by
  funext i
  simp only [Pi.mul_apply, letE, Pi.single_apply]
  split_ifs <;> simp

variable {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop}

theorem span_le_range (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ)
    (hc0 : PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0) (hc1 : PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0)
    (π' : LetA O n) (hφπ : PowerSeries.constantCoeff (W.lev c ζ (W.φA π')) = 0)
    {r0 : ℕ} (b : Fin r0 → W.DD T) (hbΔ : ∀ j, b j ∈ W.NΔ T)
    (hbu : ∀ x ∈ W.N T, ∃! a : Fin r0 → LetA O n, x = ∑ j, a j • b j)
    {r : ℕ} (bL : Basis (Fin r) O (LcQ W T π' c)) (rep : Fin r → W.DD T)
    (hrep : ∀ k, rep k ∈ NcS W T (c - 1)) (hbrep : ∀ k, bL k = mkL W T π' c (rep k) (hrep k)) :
    Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ≤ LinearMap.range (UniversalLiftFrames.Phi W T c ζ rep) := by
  classical
  set R := LinearMap.range (UniversalLiftFrames.Phi W T c ζ rep)
  set c1 := PowerSeries.coeff 1 (W.lev c ζ W.Q)
  have hvan : ∀ (x : W.DD T) (hx : x ∈ W.N T) (K : ℕ) (hK : W.Q ^ K • W.φD T x ∈ W.N T) (j : ℤ),
      j < K → W.levN T c ζ ⟨_, hK⟩ j = 0 :=
    fun x hx K hK j hj => ((hp4.2 c ζ τ hPt).1.1 ⟨x, hx⟩ K hK j).2 hj
  have hLV : ∀ (x : W.DD T) (hx : x ∈ W.N T) (K : ℕ) (hK : W.Q ^ K • W.φD T x ∈ W.N T),
      LV W T c ζ K x = c1 ^ K • valAt W T c ζ x := by
    intro x hx K hK
    rw [LV_eq W T c ζ K _ hK, levN_val W T c ζ hp4 hPt hc0 hc1 x hx K hK]
  have hcancel : ∀ (K : ℕ) (u : T.V ⊗[Qp] BdR), c1 ^ K • u ∈ R → u ∈ R := by
    intro K u hu
    have := Submodule.smul_mem R ((c1 ^ K)⁻¹) hu
    rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hc1), one_smul] at this
  have hrepR : ∀ k, valAt W T c ζ (rep k) ∈ R := by
    intro k
    refine ⟨Pi.single k 1, ?_⟩
    rw [UniversalLiftFrames.Phi_apply]
    simp [Pi.single_apply]

  have hA : ∀ y (hy : y ∈ NcS W T (c - 1)), valAt W T c ζ y ∈ R := by
    intro y hy
    set p := (PiNS W T π' 1).comap (NcS W T (c - 1)).subtype
    set o := bL.repr (mkL W T π' c y hy)
    have h2 : (∑ k, o k • bL k) = p.mkQ (∑ k, o k • (⟨rep k, hrep k⟩ : ↥(NcS W T (c - 1)))) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, hbrep]
      rfl
    have h3 : (Submodule.Quotient.mk (⟨y, hy⟩ : ↥(NcS W T (c - 1))) : LcQ W T π' c) =
        Submodule.Quotient.mk (∑ k, o k • (⟨rep k, hrep k⟩ : ↥(NcS W T (c - 1)))) := by
      have := bL.sum_repr (mkL W T π' c y hy)
      rw [h2] at this
      exact this.symm
    have h4 := (Submodule.Quotient.eq p).1 h3
    rw [Submodule.mem_comap] at h4
    have hz : y - ∑ k, o k • rep k ∈ PiNS W T π' 1 := by simpa using h4
    obtain ⟨⟨y', hy'N, hy'⟩, -⟩ := (mem_PiNS W T π' 1 _).1 hz
    have hyeq : y = ∑ k, o k • rep k + π' • y' := by
      rw [pow_one] at hy'
      rw [hy']
      abel
    have hyN := ((mem_NcS W T _ y).1 hy).1
    have hrN : ∀ k, rep k ∈ W.N T := fun k => ((mem_NcS W T _ _).1 (hrep k)).1
    choose Kr hKr using fun k => N_φ' W T (rep k) (hrN k)
    obtain ⟨Ky, hKy⟩ := N_φ' W T y hyN
    obtain ⟨Kz, hKz⟩ := N_φ' W T y' hy'N
    set K := Ky + ∑ k, Kr k + Kz
    have hKk : ∀ k, W.Q ^ K • W.φD T (rep k) ∈ W.N T := fun k =>
      Qpow_mono W T (hKr k) (by
        have := Finset.single_le_sum (f := Kr) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        omega)
    have hKo : ∀ k, W.Q ^ K • W.φD T (o k • rep k) ∈ W.N T :=
      fun k => (LV_smulO W T c ζ K (o k) (rep k) (hKk k)).1
    have hKz' : W.Q ^ K • W.φD T y' ∈ W.N T := Qpow_mono W T hKz (by omega)
    have hKy' : W.Q ^ K • W.φD T y ∈ W.N T := Qpow_mono W T hKy (by omega)
    obtain ⟨hKπ, hLπ⟩ := LV_smulA W T c ζ K π' y' hKz' (hvan y' hy'N K hKz')
    obtain ⟨hKs, hLs⟩ := LV_sum W T c ζ K Finset.univ (fun k => o k • rep k) hKo
    apply hcancel K
    rw [← hLV y hyN K hKy']
    have e : LV W T c ζ K y = LV W T c ζ K (∑ k, o k • rep k + π' • y') := by rw [← hyeq]
    rw [e, LV_add W T c ζ K _ _ hKs hKπ, hLs, hLπ, hφπ, zero_smul, add_zero]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [(LV_smulO W T c ζ K (o k) (rep k) (hKk k)).2, hLV _ (hrN k) K (hKk k), smul_comm]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hrepR k))

  rw [← (hp4.2 c ζ τ hPt).1.2]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, k, hk, rfl⟩
  set d : ZMod n := c - 1
  have hx'N : (letE d : LetA O n) • (x : W.DD T) ∈ W.N T := Submodule.smul_mem _ _ x.2
  have ek : (letE c : LetA O n) • (W.Q ^ k • W.φD T x) = W.Q ^ k • W.φD T ((letE d : LetA O n) • (x : W.DD T)) := by
    rw [show d = c - 1 from rfl, φD_letE, smul_comm]
  have hk' : W.Q ^ k • W.φD T ((letE d : LetA O n) • (x : W.DD T)) ∈ W.N T := ek ▸ Submodule.smul_mem _ _ hk
  have hw : W.levN T c ζ ⟨_, hk⟩ k = W.levN T c ζ ⟨_, hk'⟩ k := by
    rw [← levN_letE W T c ζ ⟨_, hk⟩ k]
    rw [show (letE c : LetA O n) • (⟨_, hk⟩ : ↥(W.N T)) = ⟨_, hk'⟩ from
      Subtype.ext (by rw [Submodule.coe_smul]; exact ek)]
  rw [SetLike.mem_coe, hw, levN_val W T c ζ hp4 hPt hc0 hc1 _ hx'N k hk']
  refine Submodule.smul_mem _ _ ?_
  set x' := (letE d : LetA O n) • (x : W.DD T)
  obtain ⟨a, hax, -⟩ := hbu x' hx'N
  have hx'eq : x' = ∑ j, a j • ((letE d : LetA O n) • b j) := by
    have h1 : x' = (letE d : LetA O n) • x' := by
      show _ = (letE d : LetA O n) • ((letE d : LetA O n) • (x : W.DD T))
      rw [smul_smul, letE_idem]
    rw [h1, hax, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm]
  have hebN : ∀ j, (letE d : LetA O n) • b j ∈ NcS W T (c - 1) := by
    intro j
    refine (mem_NcS W T _ _).2 ⟨Submodule.smul_mem _ _ (hbΔ j).1, fun δ hδ => ?_, ?_⟩
    · rw [γD_letE, (hbΔ j).2 δ hδ]
    · rw [smul_smul, letE_idem]
  have hebN' : ∀ j, (letE d : LetA O n) • b j ∈ W.N T := fun j => ((mem_NcS W T _ _).1 (hebN j)).1
  choose Kb hKb using fun j => N_φ' W T _ (hebN' j)
  set K := k + ∑ j, Kb j
  have hKb' : ∀ j, W.Q ^ K • W.φD T ((letE d : LetA O n) • b j) ∈ W.N T := fun j =>
    Qpow_mono W T (hKb j) (by
      have := Finset.single_le_sum (f := Kb) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      omega)
  have hKa : ∀ j, W.Q ^ K • W.φD T (a j • ((letE d : LetA O n) • b j)) ∈ W.N T :=
    fun j => (LV_smulA W T c ζ K (a j) _ (hKb' j) (hvan _ (hebN' j) K (hKb' j))).1
  have hKx : W.Q ^ K • W.φD T x' ∈ W.N T := Qpow_mono W T hk' (by omega)
  apply hcancel K
  rw [← hLV x' hx'N K hKx]
  have e : LV W T c ζ K x' = LV W T c ζ K (∑ j, a j • ((letE d : LetA O n) • b j)) := by
    rw [← hx'eq]
  rw [e, (LV_sum W T c ζ K Finset.univ _ hKa).2]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [(LV_smulA W T c ζ K (a j) _ (hKb' j) (hvan _ (hebN' j) K (hKb' j))).2,
    hLV _ (hebN' j) K (hKb' j)]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hA _ (hebN j)))

end Span2

end Formalism.MainNotions.N.Ln34.UniversalFiltration

end
end

