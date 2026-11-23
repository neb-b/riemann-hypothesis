module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0352
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0369
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantTransitionMatrixCover
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.CovTrans

theorem zOm_smul_eq_q {l : ℕ} [Fact l.Prime] {X : Type} [AddCommGroup X] [Module (Om l) X] [Module ℚ_[l] X]
    [IsScalarTower ℚ_[l] (Om l) X] (c : ℤ_[l]) (x : X) : zOm l c • x = ((c : ℚ_[l])) • x := by
  show (algebraMap ℚ_[l] (Om l) (algebraMap ℤ_[l] ℚ_[l] c)) • x = _
  rw [algebraMap_smul]
  rfl

theorem coord_inj {l : ℕ} [Fact l.Prime] {X : Type} [AddCommGroup X] [Module (Om l) X] [Module ℚ_[l] X]
    [IsScalarTower ℚ_[l] (Om l) X] {n : ℕ} {v : Fin n → X} (hv : LinearIndependent ℚ_[l] v) {u u' : Fin n → ℤ_[l]}
    (h : ∑ i, zOm l (u i) • v i = ∑ i, zOm l (u' i) • v i) : u = u' := by
  simp only [zOm_smul_eq_q] at h
  have := Fintype.linearIndependent_iff.mp hv (fun i => (u i : ℚ_[l]) - u' i)
    (by simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self])
  funext i
  have h2 := this i
  rw [sub_eq_zero] at h2
  exact Subtype.ext h2

theorem dsum {l : ℕ} [Fact l.Prime] {X : Type} [AddCommGroup X] [Module (Om l) X] {p q : ℕ} (α : Fin p → ℤ_[l])
    (β : Fin p → Fin q → ℤ_[l]) (w : Fin q → X) :
    ∑ s, zOm l (α s) • ∑ i, zOm l (β s i) • w i = ∑ i, zOm l (∑ s, β s i * α s) • w i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.smul_sum, smul_smul, map_sum, map_mul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => ?_
  rw [mul_comm]

theorem transition : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (d : ℕ) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)), LinearIndependent ℚ_[l] b → ∀ (m m' : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (ρs' : Fin m' → (Γ →* GL (Fin a) (Om l))) (ι : Fin m → Fin m'), (∀ k, ρs' (ι k) = ρs k) → ∀ (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (t' : Fin m' → Finset (Matrix (Fin a) (Fin a) (Om l))), (∀ k, t' (ι k) = t k) → ∀ (M M' : ℕ), M ≤ M' → ∀ (d₁ d₂ : ℕ) (ρ₁ : Γ →* GL (Fin d₁) ℤ_[l]) (ρ₂ : Γ →* GL (Fin d₂) ℤ_[l]) (bb₁ : Fin d₁ → Fin m → Matrix (Fin a) (Fin a) (Om l)) (bb₂ : Fin d₂ → Fin m' → Matrix (Fin a) (Fin a) (Om l)) (e₁ : Fin d₁ → ℤ_[l]) (e₂ : Fin d₂ → ℤ_[l]), LinearIndependent ℚ_[l] bb₁ → (∀ k, Reads ρ₁ (ρs k) (fun s => bb₁ s k) e₁) → (∀ k, Reads ρ₂ (ρs' k) (fun s => bb₂ s k) e₂) → (∀ s, bb₂ s ∈ GlobalTheory.TraceConjugationCover.latT ρs' t' M') → (∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, ∃ z : Fin d₁ → ℤ_[l], x = ∑ s, zOm l (z s) • bb₁ s) → ∀ (P₁ : Matrix (Fin d) (Fin d₁) ℤ_[l]) (P₂ : Matrix (Fin d) (Fin d₂) ℤ_[l]) (n N₁ N₂ : ℕ), n ≤ N₁ → n ≤ N₂ → GlobalTheory.TraceConjugationCover.Carries r b ρs t M bb₁ P₁ N₁ → GlobalTheory.TraceConjugationCover.Carries r b ρs' t' M' bb₂ P₂ N₂ → ∃ f : Matrix (Fin d₁) (Fin d₂) ℤ_[l], (∀ g, f * ((ρ₂ g : GL (Fin d₂) ℤ_[l]) : Matrix (Fin d₂) (Fin d₂) ℤ_[l]) = ((ρ₁ g : GL (Fin d₁) ℤ_[l]) : Matrix (Fin d₁) (Fin d₁) ℤ_[l]) * f) ∧ ∀ i j, (l : ℤ_[l]) ^ n ∣ (P₁ * f - P₂) i j := by
  intro l _ Γ _ a r d b hb m m' ρs ρs' ι hι t t' ht M M' hM d₁ d₂ ρ₁ ρ₂ bb₁ bb₂ e₁ e₂ hbb₁ hR₁ hR₂ hmem₂ hcoord
    P₁ P₂ n N₁ N₂ hn₁ hn₂ hC₁ hC₂
  have hsm : ∀ {k : Fin m} (c : Om l) (w : Matrix (Fin a) (Fin a) (Om l)),
      (Pi.single k (c • w) : Fin m → Matrix (Fin a) (Fin a) (Om l)) = c • Pi.single k w := by
    intro k c w
    funext k₀
    by_cases h : k₀ = k
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hπL : ∀ y ∈ GlobalTheory.TraceConjugationCover.latL t' M', y ∘ ι ∈ GlobalTheory.TraceConjugationCover.latL t M := by
    intro y hy
    have hle : Submodule.map (LinearMap.funLeft ℤ_[l] (Matrix (Fin a) (Fin a) (Om l)) ι) (GlobalTheory.TraceConjugationCover.latL t' M') ≤
        GlobalTheory.TraceConjugationCover.latL t M := by
      rw [GlobalTheory.TraceConjugationCover.latL, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      simp only [Set.mem_iUnion, Set.mem_image] at hx
      obtain ⟨k', v, hv, rfl⟩ := hx
      change (Pi.single k' ((l : Om l) ^ M' • v)) ∘ ι ∈ _
      rw [← Finset.univ_sum_single (Pi.single k' ((l : Om l) ^ M' • v) ∘ ι)]
      refine Submodule.sum_mem _ fun k _ => ?_
      by_cases hk : ι k = k'
      · subst hk
        simp only [Function.comp_apply, Pi.single_eq_same]
        have hv' : v ∈ t k := by rw [← ht k]; exact hv
        have e1 : ((l : Om l) ^ M' • v) = zOm l ((l : ℤ_[l]) ^ (M' - M)) • ((l : Om l) ^ M • v) := by
          rw [map_pow, map_natCast, smul_smul, ← pow_add, Nat.sub_add_cancel hM]
        rw [e1, hsm, GlobalTheory.TraceConjugationCover.zOm_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_iUnion.mpr ⟨k, v, hv', rfl⟩))
      · simp [Pi.single_eq_of_ne hk]
    exact hle ⟨y, hy, rfl⟩
  have hdec : ∀ j, ∃ (F : Γ →₀ ℤ_[l]) (y : Fin m' → Matrix (Fin a) (Fin a) (Om l)), y ∈ GlobalTheory.TraceConjugationCover.latL t' M' ∧
      bb₂ j = (F.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs' g) + y := by
    intro j
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp (hmem₂ j)
    obtain ⟨F, hF⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hx
    refine ⟨F, y, hy, ?_⟩
    rw [← hxy, ← hF]
    simp only [GlobalTheory.TraceConjugationCover.zOm_smul]
  choose F y hy hbb using hdec
  have hπF : ∀ (G : Γ →₀ ℤ_[l]), (G.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs' g) ∘ ι =
      G.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g := by
    intro G
    funext k
    simp [Finsupp.sum, Finset.sum_apply, GlobalTheory.TraceConjugationCover.tup, hι]
  have hπbb : ∀ j, bb₂ j ∘ ι = ((F j).sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) + y j ∘ ι := by
    intro j
    rw [hbb j, ← hπF]
    rfl
  have hmemT : ∀ j, bb₂ j ∘ ι ∈ GlobalTheory.TraceConjugationCover.latT ρs t M := by
    intro j
    rw [hπbb j]
    refine Submodule.add_mem_sup ?_ (hπL _ (hy j))
    simp only [GlobalTheory.TraceConjugationCover.zOm_smul]
    exact Submodule.finsuppSum_mem _ _ _ _ (fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩))
  choose z hz using fun j => hcoord _ (hmemT j)
  have hcol : ∀ j k, bb₂ j (ι k) = ∑ s, zOm l (z j s) • bb₁ s k := by
    intro j k
    have := congrFun (hz j) k
    simpa [Finset.sum_apply] using this
  refine ⟨Matrix.of fun s j => z j s, ?_, ?_⟩
  · intro g
    ext i j
    have hA : ∀ k, (ρs k g).val * bb₂ j (ι k) =
        ∑ i, zOm l (((ρ₁ g).val * Matrix.of fun s j => z j s) i j) • bb₁ i k := by
      intro k
      have e := fun s => (hR₁ k).equi g s
      try simp only at e
      rw [hcol, Finset.mul_sum]
      simp_rw [Matrix.mul_smul, e]
      rw [dsum]
      simp [Matrix.mul_apply]
    have hB : ∀ k, (ρs k g).val * bb₂ j (ι k) =
        ∑ i, zOm l (((Matrix.of fun s j => z j s) * (ρ₂ g).val) i j) • bb₁ i k := by
      intro k
      rw [← hι k]
      have e := (hR₂ (ι k)).equi g j
      try simp only at e
      rw [e]
      simp_rw [hcol]
      rw [dsum]
      simp [Matrix.mul_apply]
    have key : (fun i => ((Matrix.of fun s j => z j s) * (ρ₂ g).val) i j) =
        fun i => ((ρ₁ g).val * Matrix.of fun s j => z j s) i j := by
      apply GlobalTheory.CovTrans.coord_inj hbb₁
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply]
      rw [← hB k, hA k]
    exact congrArg _ (congrFun key i)
  · intro i j
    have hsingle : ∑ s, zOm l ((Pi.single j 1 : Fin d₂ → ℤ_[l]) s) • bb₂ s = bb₂ j := by
      simp [Pi.single_apply]
    obtain ⟨w₂, hw₂⟩ := hC₂ (Pi.single j 1) (F j) (y j) (hy j) (by rw [hsingle]; exact hbb j)
    obtain ⟨w₁, hw₁⟩ := hC₁ (fun s => z j s) (F j) (y j ∘ ι) (hπL _ (hy j)) (by rw [← hz j, hπbb j])
    have hP₂ : P₂ *ᵥ Pi.single j 1 = fun i => P₂ i j := by
      funext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have hP₁ : P₁ *ᵥ (fun s => z j s) = fun i => (P₁ * Matrix.of fun s j => z j s) i j := by
      funext i; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [hP₂] at hw₂
    rw [hP₁] at hw₁
    have key : (fun i => (P₁ * Matrix.of fun s j => z j s) i j - P₂ i j) =
        fun i => (l : ℤ_[l]) ^ n * ((l : ℤ_[l]) ^ (N₁ - n) * w₁ i - (l : ℤ_[l]) ^ (N₂ - n) * w₂ i) := by
      apply GlobalTheory.CovTrans.coord_inj hb
      have hs : ∑ i, zOm l ((P₁ * Matrix.of fun s j => z j s) i j - P₂ i j) • b i =
          ∑ i, zOm l ((P₁ * Matrix.of fun s j => z j s) i j) • b i - ∑ i, zOm l (P₂ i j) • b i := by
        simp only [map_sub, sub_smul, Finset.sum_sub_distrib]
      rw [hs, hw₁, hw₂, add_sub_add_left_eq_sub]
      have e1 : (l : Om l) ^ N₁ = (l : Om l) ^ n * (l : Om l) ^ (N₁ - n) := by rw [← pow_add, Nat.add_sub_cancel' hn₁]
      have e2 : (l : Om l) ^ N₂ = (l : Om l) ^ n * (l : Om l) ^ (N₂ - n) := by rw [← pow_add, Nat.add_sub_cancel' hn₂]
      rw [e1, e2]
      simp only [Finset.smul_sum, smul_smul, map_mul, map_sub, map_pow, map_natCast, mul_sub, sub_smul,
        Finset.sum_sub_distrib, mul_assoc]
    have := congrFun key i
    rw [Matrix.sub_apply, this]
    exact Dvd.intro _ rfl

end GlobalTheory.CovTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteGroupDataSeriesIdempotentsLabelSums
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

noncomputable section

namespace GlobalTheory.LzExist

section Alg

variable {A : Type} [Ring A] [Algebra ℂ A]

def IsDecomp (S : Finset A) : Prop :=
  (∀ e ∈ S, e * e = e) ∧ (∀ e ∈ S, ∀ z : A, e * z = z * e) ∧ (∀ e ∈ S, e ≠ 0) ∧
    (∀ e ∈ S, ∀ f ∈ S, e ≠ f → e * f = 0) ∧ ∑ e ∈ S, e = 1

def IsPrim (S : Finset A) : Prop :=
  ∀ t ∈ S, ∀ x : A, x * x = x → (∀ z, x * z = z * x) → x * t = x → x = 0 ∨ x = t

theorem linInd {S : Finset A} (h : IsDecomp S) : LinearIndependent ℂ (fun x : S => (x : A)) := by
  rw [linearIndependent_iff']
  intro s c hs i hi
  have h1 : (∑ j ∈ s, c j • (j : A)) * (i : A) = c i • (i : A) := by
    rw [Finset.sum_mul, Finset.sum_eq_single i]
    · rw [smul_mul_assoc, h.1 _ i.2]
    · intro j _ hji
      rw [smul_mul_assoc, h.2.2.2.1 _ j.2 _ i.2 (fun e => hji (Subtype.ext e)), smul_zero]
    · intro h'; exact absurd hi h'
  rw [hs, zero_mul] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_right (h.2.2.1 _ i.2)

theorem card_le [Module.Finite ℂ A] {S : Finset A} (h : IsDecomp S) : S.card ≤ Module.finrank ℂ A := by
  have := (linInd h).fintype_card_le_finrank
  simpa using this

theorem refine_decomp [DecidableEq A] {S : Finset A} (h : IsDecomp S) {t : A} (ht : t ∈ S) {x : A}
    (hx : x * x = x) (hc : ∀ z, x * z = z * x) (hxt : x * t = x) (h0 : x ≠ 0) (ht' : x ≠ t) :
    IsDecomp (insert x (insert (t - x) (S.erase t))) ∧
      (insert x (insert (t - x) (S.erase t))).card = S.card + 1 := by
  obtain ⟨hI, hC, hN, hO, hS⟩ := h
  have htx : t * x = x := by rw [← hc t, hxt]
  have hxs : ∀ s ∈ S.erase t, x * s = 0 := by
    intro s hs
    obtain ⟨hst, hs⟩ := Finset.mem_erase.1 hs
    rw [← hxt, mul_assoc, hO t ht s hs (Ne.symm hst), mul_zero]
  have hsx : ∀ s ∈ S.erase t, s * x = 0 := fun s hs => by rw [← hc s]; exact hxs s hs
  have hts : ∀ s ∈ S.erase t, (t - x) * s = 0 := by
    intro s hs
    obtain ⟨hst, hs'⟩ := Finset.mem_erase.1 hs
    rw [sub_mul, hO t ht s hs' (Ne.symm hst), hxs s hs, sub_zero]
  have hst' : ∀ s ∈ S.erase t, s * (t - x) = 0 := by
    intro s hs
    obtain ⟨hst, hs'⟩ := Finset.mem_erase.1 hs
    rw [mul_sub, hO s hs' t ht hst, hsx s hs, sub_zero]
  have hxtx : x * (t - x) = 0 := by rw [mul_sub, hxt, hx, sub_self]
  have htxx : (t - x) * x = 0 := by rw [sub_mul, htx, hx, sub_self]
  have htt : (t - x) * (t - x) = t - x := by
    rw [mul_sub, htxx, sub_zero, sub_mul, hI t ht, hxt]
  have htx0 : t - x ≠ 0 := fun h => ht' (sub_eq_zero.1 h).symm
  have hnot : ∀ y, y * y = y → y ≠ 0 → (∀ s ∈ S.erase t, y * s = 0) → y ∉ S.erase t := by
    intro y hy hy0 hys hmem
    exact hy0 (by rw [← hy]; exact hys y hmem)
  have hm1 : t - x ∉ S.erase t := hnot _ htt htx0 hts
  have hm2 : x ∉ insert (t - x) (S.erase t) := by
    rw [Finset.mem_insert, not_or]
    refine ⟨fun e => h0 ?_, hnot _ hx h0 hxs⟩
    rw [← hx]; nth_rewrite 2 [e]; exact hxtx
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro e he
    rw [Finset.mem_insert, Finset.mem_insert] at he
    rcases he with rfl | rfl | he
    · exact hx
    · exact htt
    · exact hI e (Finset.mem_of_mem_erase he)
  · intro e he z
    rw [Finset.mem_insert, Finset.mem_insert] at he
    rcases he with rfl | rfl | he
    · exact hc z
    · rw [sub_mul, mul_sub, hC t ht z, hc z]
    · exact hC e (Finset.mem_of_mem_erase he) z
  · intro e he
    rw [Finset.mem_insert, Finset.mem_insert] at he
    rcases he with rfl | rfl | he
    · exact h0
    · exact htx0
    · exact hN e (Finset.mem_of_mem_erase he)
  · intro e he f hf hef
    rw [Finset.mem_insert, Finset.mem_insert] at he hf
    rcases he with rfl | rfl | he <;> rcases hf with rfl | rfl | hf
    · exact absurd rfl hef
    · exact hxtx
    · exact hxs f hf
    · exact htxx
    · exact absurd rfl hef
    · exact hts f hf
    · exact hsx e he
    · exact hst' e he
    · exact hO e (Finset.mem_of_mem_erase he) f (Finset.mem_of_mem_erase hf) hef
  · rw [Finset.sum_insert hm2, Finset.sum_insert hm1, ← add_assoc, add_sub_cancel,
      Finset.add_sum_erase S (fun e => e) ht, hS]
  · rw [Finset.card_insert_of_notMem hm2, Finset.card_insert_of_notMem hm1,
      Finset.card_erase_of_mem ht]
    have := Finset.card_pos.2 ⟨t, ht⟩
    omega

theorem exists_prim [Module.Finite ℂ A] [Nontrivial A] : ∃ S : Finset A, IsDecomp S ∧ IsPrim S := by
  classical
  let P : ℕ → Prop := fun n => ∃ S : Finset A, IsDecomp S ∧ S.card = n
  have h1 : P 1 := ⟨{1}, ⟨by simp, by simp, by simp, by simp, by simp⟩, by simp⟩
  have hb : ∀ n, P n → n ≤ Module.finrank ℂ A := by
    rintro n ⟨S, hS, rfl⟩; exact card_le hS
  obtain ⟨S, hS, hc⟩ := Nat.findGreatest_spec (P := P) (m := 1) (n := Module.finrank ℂ A) (hb 1 h1) h1
  refine ⟨S, hS, ?_⟩
  intro t ht x hx hc' hxt
  by_contra hne
  rw [not_or] at hne
  obtain ⟨h2, h3⟩ := refine_decomp hS ht hx hc' hxt hne.1 hne.2
  have := Nat.le_findGreatest (P := P) (hb _ ⟨_, h2, rfl⟩) ⟨_, h2, rfl⟩
  omega

theorem lab_unique {ι : Type} {S : Finset A} (hS : IsDecomp S) (hP : IsPrim S) (e : ι → A)
    (he_idem : ∀ i, e i * e i = e i) (he_c : ∀ i z, e i * z = z * e i)
    (he_o : ∀ i j, i ≠ j → e i * e j = 0) (T : Finset ι) (hT : ∑ i ∈ T, e i = 1) {t : A} (ht : t ∈ S) :
    ∃ i ∈ T, e i * t = t ∧ ∀ j, j ≠ i → e j * t = 0 := by
  have key : ∀ j, e j * t = 0 ∨ e j * t = t := by
    intro j
    refine hP t ht _ ?_ ?_ ?_
    · rw [mul_assoc, ← mul_assoc t, hS.2.1 t ht (e j), mul_assoc, hS.1 t ht, ← mul_assoc, he_idem]
    · intro z
      rw [mul_assoc, hS.2.1 t ht z, ← mul_assoc, he_c j z, mul_assoc]
    · rw [mul_assoc, hS.1 t ht]
  have hsum : ∑ j ∈ T, e j * t = t := by rw [← Finset.sum_mul, hT, one_mul]
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.symm ▸ hS.2.2.1 t ht)
  have hit : e i * t = t := (key i).resolve_left hne
  refine ⟨i, hi, hit, fun j hji => (key j).resolve_right fun hjt => hS.2.2.1 t ht ?_⟩
  have h0 : (e j * t) * (e i * t) = 0 := by
    rw [mul_assoc, ← mul_assoc t, hS.2.1 t ht (e i), mul_assoc, ← mul_assoc (e j), he_o j i hji,
      zero_mul]
  rw [hjt, hit, hS.1 t ht] at h0
  exact h0

end Alg

section Lz

variable (g r : ℕ) [Fact g.Prime] (e : (ZMod g)[X] → MonoidAlgebra ℂ (GL (Fin r) (ZMod g)))

abbrev GA (a : ℕ) : Type := MonoidAlgebra ℂ (GL (Fin a) (ZMod g))

def decS (a : ℕ) : Finset (GA g a) := (exists_prim (A := GA g a)).choose

theorem decS_spec (a : ℕ) : IsDecomp (decS g a) ∧ IsPrim (decS g a) :=
  (exists_prim (A := GA g a)).choose_spec

def LabQ (a : ℕ) (x : GA g a) (f : (ZMod g)[X]) : Prop :=
  (f.Monic ∧ f.natDegree = a ∧ f.coeff 0 ≠ 0) ∧
    ∀ h : a = r, e f * cast (congrArg (GA g) h) x = cast (congrArg (GA g) h) x


open Classical in
def labF (a : ℕ) (x : GA g a) : (ZMod g)[X] :=
  if h : ∃ f, LabQ g r e a x f then h.choose else (X - C 1) ^ a

theorem labF_spec (a : ℕ) (x : GA g a) :
    (labF g r e a x).Monic ∧ (labF g r e a x).natDegree = a ∧ (labF g r e a x).coeff 0 ≠ 0 := by
  unfold labF
  split_ifs with h
  · exact h.choose_spec.1
  · refine ⟨(monic_X_sub_C 1).pow a, ?_, ?_⟩
    · rw [natDegree_pow, natDegree_X_sub_C, mul_one]
    · rw [coeff_zero_eq_eval_zero]; simp

def lzE : PairedCharacterCondition.LzData g where
  Irr a := ↥(decS g a)
  finIrr a := inferInstance
  idem τ := τ.1
  idem_idem τ := (decS_spec g _).1.1 _ τ.2
  idem_central τ z := (decS_spec g _).1.2.1 _ τ.2 z
  idem_ne τ := (decS_spec g _).1.2.2.1 _ τ.2
  idem_orth τ σ h := (decS_spec g _).1.2.2.2.1 _ τ.2 _ σ.2 (fun e => h (Subtype.ext e))
  idem_sum a := by
    rw [Finset.sum_coe_sort (decS g a) (fun x => x)]; exact (decS_spec g a).1.2.2.2.2
  idem_prim τ x hx hc hxt := (decS_spec g _).2 _ τ.2 x hx hc hxt
  lab τ := labF g r e _ τ.1
  lab_spec τ := labF_spec g r e _ τ.1
  Rep a := Set ↥(decS g a)
  ofIrr τ := {τ}
  cons R τ := τ ∈ R
  cons_ofIrr _ _ := Set.mem_singleton_iff
  hc _ _ := ∅

open Classical in
theorem lzE_ser (hidem : ∀ f, e f * e f = e f) (hcen : ∀ f a, e f * a = a * e f)
    (horth : ∀ f f', f ≠ f' → e f * e f' = 0)
    (hsum : ∃ S : Finset (ZMod g)[X], (∀ f, f ∈ S ↔ f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0) ∧
      ∑ f ∈ S, e f = 1) (f : (ZMod g)[X]) :
    e f = ∑ τ : (lzE g r e).Irr r, if (lzE g r e).lab τ = f then (lzE g r e).idem τ else 0 := by
  obtain ⟨T, hTm, hT⟩ := hsum
  have hmain : ∀ t ∈ decS g r, ∀ f, e f * t = if labF g r e r t = f then t else 0 := by
    intro t ht f
    obtain ⟨i, hi, hit, hj⟩ :=
      lab_unique (decS_spec g r).1 (decS_spec g r).2 e hidem hcen horth T hT ht
    have hlab : labF g r e r t = i := by
      have hex : ∃ f, LabQ g r e r t f := ⟨i, (hTm i).1 hi, fun h => by simp only [cast_eq]; exact hit⟩
      have hs := hex.choose_spec.2 rfl
      simp only [cast_eq] at hs
      unfold labF
      rw [dite_eq_left hex]
      by_contra hne
      exact (decS_spec g r).1.2.2.1 t ht (hs.symm.trans (hj _ hne))
    rw [hlab]
    split_ifs with hif
    · subst hif; exact hit
    · exact hj f (Ne.symm hif)
  show e f = ∑ τ : ↥(decS g r), if labF g r e r τ.1 = f then τ.1 else 0
  calc e f = e f * ∑ τ : ↥(decS g r), τ.1 := by
        rw [Finset.sum_coe_sort (decS g r) (fun x => x), (decS_spec g r).1.2.2.2.2, mul_one]
    _ = ∑ τ : ↥(decS g r), e f * τ.1 := Finset.mul_sum _ _ _
    _ = _ := Finset.sum_congr rfl fun τ _ => hmain τ.1 τ.2 f

end Lz

theorem exists_lz_serEq : ∀ D : D7, ∃ lz : ∀ k : Fin 2, PairedCharacterCondition.LzData (D.host.g k), SerEq D lz := by
  intro D
  refine ⟨fun k => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩;
    lzE (D.host.g k) D.R.r (D.ntypes.eSer k), ?_⟩
  intro k f
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  exact lzE_ser _ _ _ (D.ntypes.eSer_idem k) (D.ntypes.eSer_central k) (D.ntypes.eSer_orth k)
    (D.ntypes.eSer_sum k) f

end GlobalTheory.LzExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixFlatOfTiltMapsAgree
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_galK_fixFlat_of_tilt_maps_agree : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type)
    [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O),
    ψ bk.flat ≠ 0 → ¬ IsUnit (ψ bk.flat) → IsAdicComplete (Ideal.span {ψ bk.flat}) O →
    ∀ ψ' : OCb l →+* O, (∀ s : bk.S, ψ ((bk.ev s).coeff 0) = ψ' ((bk.ev s).coeff 0)) →
    ∃ g : ↥(GK K), bk.FixFlat g ∧ ∀ y, ψ' y = ψ (Per.σF (g : GQ l) y) := by
  intro l _ K bk O _ _ _ _ _ ψ h0 hu hc ψ' hs
  have hflat : ψ' bk.flat = ψ bk.flat := by
    have h := hs X
    rw [bk.ev_X, WittVector.teichmuller_coeff_zero] at h
    exact h.symm
  have hW := _root_.GlobalTheory.BSP.wmap_ev_eq l K bk O ψ ψ' h0 hc hs
  obtain ⟨θ₁, hθ₁, hinj₁, hdom, hdiv⟩ := _root_.GlobalTheory.BSP.exists_untilt_map l K bk O ψ h0 hu hc
  obtain ⟨θ₂', hθ₂', hinj₂', -, -⟩ :=
    _root_.GlobalTheory.BSP.exists_untilt_map l K bk O ψ' (hflat ▸ h0) (hflat ▸ hu) (hflat ▸ hc)
  have hI : Ideal.span {WittVector.map ψ' (bk.ev bk.E)} = Ideal.span {WittVector.map ψ (bk.ev bk.E)} := by
    rw [hW bk.E]
  let θ₂ := (Ideal.quotEquivOfEq hI).toRingHom.comp θ₂'
  have hθ₂ : ∀ a : Ainf l, θ₂ (Per.θ l a) = Ideal.Quotient.mk _ (WittVector.map ψ' a) := by
    intro a
    simp only [θ₂, RingHom.comp_apply, hθ₂' a, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      Ideal.quotEquivOfEq_mk]
  have hinj₂ : Function.Injective θ₂ := (Ideal.quotEquivOfEq hI).injective.comp hinj₂'
  haveI := hdom
  have hK : ∀ r : ↥(OL K), θ₁ (intToOC K r) = θ₂ (intToOC K r) := by
    intro r
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (bk.str r)
    rw [← bk.θ_ev r x hx, hθ₁, hθ₂, hW x]
  obtain ⟨g, halg, hl⟩ := _root_.GlobalTheory.EmbTwo.exists_gal_eq l K _ θ₁ θ₂ hinj₁ hinj₂ hK
  obtain ⟨hroot, hfix⟩ := _root_.GlobalTheory.BSP.rootT_flat_alg_and_fix l K bk

  have key : ∀ z : OCb l, ψ z = ψ' z →
      ψ ((frobeniusEquiv (OCb l) l).symm z) = ψ' ((frobeniusEquiv (OCb l) l).symm z) := by
    intro z hz
    apply frobenius_inj O l
    rw [← RingHom.map_frobenius, ← RingHom.map_frobenius, frobenius_apply_frobeniusEquiv_symm, hz]
  have hiter : ∀ n : ℕ, ψ (((frobeniusEquiv (OCb l) l).symm)^[n] bk.flat) =
      ψ' (((frobeniusEquiv (OCb l) l).symm)^[n] bk.flat) := by
    intro n
    induction n with
    | zero => exact hflat.symm
    | succ n ih => rw [Function.iterate_succ_apply']; exact key _ ih
  have hθroot : ∀ n : ℕ, θ₁ (GlobalTheory.MemLoc.rootT bk.flat n) = θ₂ (GlobalTheory.MemLoc.rootT bk.flat n) := by
    intro n
    have e : GlobalTheory.MemLoc.rootT bk.flat n =
        Per.θ l (WittVector.teichmuller l (((frobeniusEquiv (OCb l) l).symm)^[n] bk.flat)) := by
      rw [GlobalTheory.MemLoc.rootT, WittVector.fontaineTheta_teichmuller]
    rw [e, hθ₁, hθ₂, WittVector.map_teichmuller, WittVector.map_teichmuller, hiter n]
  refine ⟨g, ?_, ?_⟩
  · refine hfix (g : GQ l) bk.flat fun n => ?_
    obtain ⟨z, hz⟩ := hroot n
    have h := halg _ ⟨z, hz⟩
    rw [← hθroot n] at h
    exact (hinj₁ h).symm
  · have hext := _root_.GlobalTheory.ringHom_eq_of_perfect_of_dvd_sub l (OCb l) O (ψ bk.flat) bk.Ep.natDegree bk.deg_pos hc.toIsHausdorff
      ψ' (ψ.comp (Per.σF (g : GQ l))) fun y => ?_
    · intro y
      exact RingHom.congr_fun hext y
    · have hmk := hl (Per.θ l (WittVector.teichmuller l y))
      rw [← GlobalTheory.RingBasics.θ_σA, hθ₁, hθ₂] at hmk
      have e2 : Per.σA (g : GQ l) (WittVector.teichmuller l y) =
          WittVector.teichmuller l (Per.σF (g : GQ l) y) := by
        exact GlobalTheory.RingIface.sigA_teich l (g : GQ l) y
      rw [e2, WittVector.map_teichmuller, WittVector.map_teichmuller, ← map_sub] at hmk
      have h := hdiv _ hmk
      rw [← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply,
        WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero,
        WittVector.teichmuller_coeff_zero] at h
      simpa [RingHom.comp_apply] using h

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltZerosUntiltFrobeniusDoubleSeriesStatement
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tilt_zeros_untiltFrobeniusDoubleSeries : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 2 ≤ h → μ ≠ 0 → ∃ y : Fin h → ℕ → Fl l, (∀ a k, ‖sh (y a k)‖ ≤ ‖(l : ℂ_[l])‖) ∧ (∀ a, ∑ i : Fin h, μ i * abelian₂ h i (y a) = 0) ∧ ∀ c : Fin h → ℚ_[l], (∀ j : ℕ, j < 2 → ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * abelian₂ h j (y a) = 0) → c = 0 := by
  first | exact @GlobalTheory.PSerExist.exists_zeros | exact GlobalTheory.PSerExist.exists_zeros | (intros; apply GlobalTheory.PSerExist.exists_zeros <;> assumption)
end

