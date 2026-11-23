module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ProdList
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.AltComb
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0347
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.AltSum
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Groth.AltS

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def tN (Δ : Segment k) (n : ℕ) : IrrGL (k := k) := Δ.first.nu (n : ℂ)

theorem tN_injective (Δ : Segment k) : Function.Injective (tN Δ) := fun a b h =>
  GlobalTheory.T.cuspidal_twist_injective PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top Δ.first Δ.isCusp_first a b h

theorem tN_zero (Δ : Segment k) : tN Δ 0 = Δ.first := by
  simp [tN]

theorem vWord_eq (Δ : Segment k) (S : Finset (Fin Δ.len)) :
    vWord Δ S = (AltC.wN Δ.len (S.map Fin.valEmbedding)).map (tN Δ) := by
  have key : ∀ (p : Fin Δ.len → Bool) (q : ℕ → Bool), (∀ a : Fin Δ.len, p a = q a) →
      ((List.finRange Δ.len).filter p).map Fin.val = (List.range Δ.len).filter q := by
    intro p q hpq
    rw [← List.map_coe_finRange_eq_range, List.filter_map]
    congr 1
    exact List.filter_congr fun a _ => hpq a
  have hmemS : ∀ a : Fin Δ.len, (a : ℕ) ∈ S.map Fin.valEmbedding ↔ a ∈ S := fun a => Finset.mem_map' Fin.valEmbedding
  unfold vWord AltC.wN
  rw [← key (fun a => decide (a ∈ S)) (fun n => decide (n ∈ S.map Fin.valEmbedding)) (by intro a; simp only [hmemS]),
    ← key (fun a => decide (a ∉ S)) (fun n => decide (n ∉ S.map Fin.valEmbedding)) (by intro a; simp only [hmemS]),
    ← List.map_reverse, ← List.map_append, List.map_map]
  rfl

theorem decWord_eq (Δ Γ : Segment k) (b : ℕ) (hb : Γ.first = tN Δ b) :
    decWord Γ = ((List.range' b Γ.len).reverse).map (tN Δ) := by
  unfold decWord
  rw [List.map_reverse]
  congr 1
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range']
  rw [Segment.term, hb, tN, tN]
  simp [Nat.cast_add]

theorem first_mem_decWord (Γ : Segment k) : Γ.first ∈ decWord Γ := by
  unfold decWord
  rw [List.mem_reverse, List.mem_ofFn]
  exact ⟨⟨0, Γ.len_pos⟩, by simp [Segment.term]⟩

end PositivityTheory.Groth.AltS

namespace PositivityTheory.Groth

open AltS

theorem altSum (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    AltSum k := by
  intro Δ h Γ
  have hW : ∀ S, (vWord Δ S).Nodup := fun S => by
    rw [vWord_eq]; exact (AltC.nodup_wN _ _).map (tN_injective Δ)
  have hmapiff : (Finset.univ.val.map Γ = {Δ}) ↔ h = 1 ∧ ∀ i, Γ i = Δ := by
    rw [← Multiset.replicate_one, Multiset.eq_replicate]
    simp
  by_cases hex : ∀ i, ∃ n, (Γ i).first = tN Δ n
  · choose b hb using hex
    have hd : ∀ i, decWord (Γ i) = ((List.range' (b i) (Γ i).len).reverse).map (tN Δ) :=
      fun i => decWord_eq Δ (Γ i) (b i) (hb i)
    have H := AltC.altSumN Δ.len Δ.len_pos (vSets Δ) (by intro S; simp [vSets]) b (fun i => (Γ i).len)
      (fun i => (Γ i).len_pos)
      (fun S => (-1 : ℤ) ^ S.card * (shuffleCount (vWord Δ S) (fun i => decWord (Γ i)) : ℤ)) (by
        intro S
        congr 1
        rw [AltC.shuffleCount_eq _ _ (hW S)]
        have e : ((∀ i, (decWord (Γ i)).Sublist (vWord Δ S)) ∧ ∀ x ∈ vWord Δ S, ∃! i, x ∈ decWord (Γ i)) ↔
            AltC.Cond Δ.len (S.map Fin.valEmbedding) b (fun i => (Γ i).len) := by
          simp only [hd, vWord_eq]
          rw [AltC.cond_map (tN Δ) (tN_injective Δ)]
          rfl
        by_cases hC : AltC.Cond Δ.len (S.map Fin.valEmbedding) b (fun i => (Γ i).len)
        · rw [if_pos (e.2 hC), if_pos hC]; simp
        · rw [if_neg (mt e.1 hC), if_neg hC]; simp)
    rw [H]
    have hiff : (h = 1 ∧ ∀ i, b i = 0 ∧ (Γ i).len = Δ.len) ↔ Finset.univ.val.map Γ = {Δ} := by
      rw [hmapiff]
      refine and_congr_right fun _ => forall_congr' fun i => ⟨fun ⟨h0, hl⟩ => ?_, fun he => ⟨?_, by rw [he]⟩⟩
      · exact Segment.ext_first (by rw [hb i, h0, tN_zero]) hl
      · exact tN_injective Δ (by rw [← hb i, he, tN_zero])
    by_cases hc : Finset.univ.val.map Γ = {Δ}
    · rw [if_pos (hiff.2 hc), if_pos hc]
    · rw [if_neg (mt hiff.1 hc), if_neg hc]
  · push Not at hex
    obtain ⟨i, hi⟩ := hex
    rw [if_neg]
    · apply Finset.sum_eq_zero
      intro S _
      rw [AltC.shuffleCount_eq _ _ (hW S), if_neg]
      · simp
      rintro ⟨hs, _⟩
      have := (hs i).subset (first_mem_decWord (Γ i))
      rw [vWord_eq, List.mem_map] at this
      obtain ⟨n, _, hn⟩ := this
      exact hi n hn.symm
    · rw [hmapiff]
      rintro ⟨_, hall⟩
      exact hi 0 (by rw [hall i, tN_zero])

end PositivityTheory.Groth

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.TriSupportedLe
section
open MvPolynomial

namespace PositivityTheory.Groth.ChartWirtingerDerivatives

def toZAlg {σ : Type*} (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ) :
    MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial σ ℤ :=
  AlgHom.mk ψ (by
    intro r
    show ψ (algebraMap ℤ (MvPolynomial σ ℤ) r) = algebraMap ℤ (MvPolynomial σ ℤ) r
    rw [algebraMap_eq, eq_intCast C r]
    exact map_intCast ψ r)

theorem tri_supported_le {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) (N : ℕ) :
    supported ℤ {t | w t < N} ≤ (supported ℤ {t | w t < N}).map (toZAlg ψ) := by
  induction N with
  | zero =>
    intro x hx
    have he : {t | w t < 0} = (∅ : Set σ) := by
      ext t
      simp
    rw [he, supported_empty] at hx
    obtain ⟨r, rfl⟩ := Algebra.mem_bot.1 hx
    exact Subalgebra.algebraMap_mem _ r
  | succ N ih =>
    intro x hx
    rw [supported_eq_adjoin_X] at hx
    refine Algebra.adjoin_le ?_ hx
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨ε, p, hp, hψ⟩ := h s
    have hs' : w s < N + 1 := hs
    have hXs : X s ∈ supported ℤ {t | w t < N + 1} := X_mem_supported.2 hs
    have h1 : ψ (X s) ∈ (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) :=
      Subalgebra.mem_map.2 ⟨X s, hXs, rfl⟩
    have h2 : p ∈ (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) := by
      have hp' : p ∈ supported ℤ {t | w t < N} := by
        rw [mem_supported]
        intro t ht
        have := hp t ht
        show w t < N
        omega
      refine Subalgebra.map_mono (supported_mono ?_) (ih hp')
      intro t ht
      have ht' : w t < N := ht
      show w t < N + 1
      omega
    have key : X s = ((ε⁻¹ : ℤˣ) : ℤ) • (ψ (X s) - p) := by
      rw [hψ, add_sub_cancel_right, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    rw [key]
    exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ h1 h2) _

theorem tri_surj {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) : Function.Surjective ψ := by
  have hrange : ∀ s, X s ∈ (toZAlg ψ).range := by
    intro s
    have hmem := tri_supported_le w ψ h (w s + 1)
      (X_mem_supported.2 (show w s < w s + 1 by omega))
    obtain ⟨y, -, hy⟩ := Subalgebra.mem_map.1 hmem
    exact (AlgHom.mem_range _).2 ⟨y, hy⟩
  have htop : (toZAlg ψ).range = ⊤ := by
    rw [eq_top_iff, ← adjoin_range_X, Algebra.adjoin_le_iff]
    rintro _ ⟨s, rfl⟩
    exact hrange s
  intro y
  have hy : y ∈ (toZAlg ψ).range := by
    rw [htop]
    exact Algebra.mem_top
  obtain ⟨x, hx⟩ := (AlgHom.mem_range _).1 hy
  exact ⟨x, hx⟩

theorem tri_bij {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) : Function.Bijective ψ := by
  refine ⟨?_, tri_surj w ψ h⟩
  have hpre : ∀ s, ∃ (ε : ℤˣ) (q : MvPolynomial σ ℤ), (∀ t ∈ q.vars, w t < w s) ∧
      ψ ((ε : ℤ) • X s + q) = X s := by
    intro s
    obtain ⟨ε, p, hp, hψ⟩ := h s
    have hp' : ((ε⁻¹ : ℤˣ) : ℤ) • p ∈ supported ℤ {t | w t < w s} := by
      apply Subalgebra.smul_mem
      rw [mem_supported]
      intro t ht
      exact hp t ht
    obtain ⟨q, hq, hqe⟩ := Subalgebra.mem_map.1 (tri_supported_le w ψ h (w s) hp')
    refine ⟨ε⁻¹, -q, ?_, ?_⟩
    · intro t ht
      rw [vars_neg] at ht
      exact (mem_supported.1 hq) (Finset.mem_coe.2 ht)
    · have hqe' : ψ q = ((ε⁻¹ : ℤˣ) : ℤ) • p := hqe
      rw [map_add (f := _), map_neg, map_zsmul, hψ, hqe', smul_add, smul_smul, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, one_smul, add_neg_cancel_right]
  choose ε' q hq hψq using hpre
  let φ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ :=
    (aeval fun s => ((ε' s : ℤˣ) : ℤ) • X s + q s).toRingHom
  have hφX : ∀ s, φ (X s) = ((ε' s : ℤˣ) : ℤ) • X s + q s := fun s => aeval_X _ _
  have hφs : Function.Surjective φ := tri_surj w φ (fun s => ⟨ε' s, q s, hq s, hφX s⟩)
  have hcomp : ∀ a, ψ (φ a) = a := by
    have hc : ψ.comp φ = RingHom.id _ := by
      apply MvPolynomial.ringHom_ext
      · intro r
        show ψ (φ (C r)) = C r
        simp only [eq_intCast C r, map_intCast]
      · intro s
        show ψ (φ (X s)) = X s
        rw [hφX]
        exact hψq s
    intro a
    rw [← RingHom.comp_apply, hc, RingHom.id_apply]
  intro a b hab
  obtain ⟨a', rfl⟩ := hφs a
  obtain ⟨b', rfl⟩ := hφs b
  rw [hcomp, hcomp] at hab
  rw [hab]

theorem uni_inj {M I : Type*} (L : M ≃ I) (w : M → ℕ) (f : M → I →₀ ℤ)
    (h1 : ∀ m, f m (L m) = 1) (hlt : ∀ m n, f m (L n) ≠ 0 → m = n ∨ w m < w n) :
    Function.Injective (Finsupp.linearCombination ℤ f) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hne
  have hsupp : a.support.Nonempty := Finsupp.support_nonempty_iff.2 hne
  obtain ⟨n, hn, hmin⟩ := a.support.exists_min_image w hsupp
  have hcoef := congrArg (fun g => g (L n)) ha
  simp only [Finsupp.linearCombination_apply, Finsupp.coe_zero, Pi.zero_apply] at hcoef
  rw [Finsupp.sum_apply, Finsupp.sum, Finset.sum_eq_single n] at hcoef
  · simp only [Finsupp.smul_apply, h1, smul_eq_mul, mul_one] at hcoef
    exact (Finsupp.mem_support_iff.1 hn) hcoef
  · intro m hm hmn
    simp only [Finsupp.smul_apply, smul_eq_mul]
    by_cases hf : f m (L n) = 0
    · simp [hf]
    · rcases hlt m n hf with h | h
      · exact absurd h hmn
      · exact absurd (hmin m hm) (not_le.2 h)
  · intro hn'
    exact absurd hn hn'

theorem uni_exists {M I C : Type*} (L : M ≃ I) (c : M → C) (w : M → ℕ) (b : C → ℕ) (f : M → I →₀ ℤ)
    (hb : ∀ m, w m ≤ b (c m)) (h1 : ∀ m, f m (L m) = 1)
    (hlt : ∀ m n, f m (L n) ≠ 0 → c m = c n ∧ (m = n ∨ w m < w n)) :
    ∀ n, ∃ a : M →₀ ℤ, (∀ m ∈ a.support, c m = c n) ∧
      Finsupp.linearCombination ℤ f a = Finsupp.single (L n) 1 := by
  classical
  intro n
  suffices key : ∀ d n, b (c n) - w n = d → ∃ a : M →₀ ℤ, (∀ m ∈ a.support, c m = c n) ∧
      Finsupp.linearCombination ℤ f a = Finsupp.single (L n) 1 from key _ n rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro n hd
    set v : I →₀ ℤ := Finsupp.single (L n) 1 - f n with hv
    have hvsupp : ∀ i ∈ v.support, c (L.symm i) = c n ∧
        b (c (L.symm i)) - w (L.symm i) < d := by
      intro i hi
      have hvi : v i ≠ 0 := Finsupp.mem_support_iff.1 hi
      set m := L.symm i with hm
      have hi' : i = L m := by rw [hm, Equiv.apply_symm_apply]
      have hne : m ≠ n := by
        intro hmn
        apply hvi
        rw [hi', hmn, hv, Finsupp.sub_apply, Finsupp.single_eq_same, h1, sub_self]
      have hf : f n (L m) ≠ 0 := by
        intro hf0
        apply hvi
        rw [hi', hv, Finsupp.sub_apply, hf0, sub_zero, Finsupp.single_apply, if_neg]
        intro heq
        exact hne (L.injective heq).symm
      obtain ⟨hc, hw⟩ := hlt n m hf
      rcases hw with hw | hw
      · exact absurd hw.symm hne
      · refine ⟨hc.symm, ?_⟩
        have hbm := hb m
        rw [← hc] at hbm ⊢
        omega
    have hex : ∀ i ∈ v.support, ∃ a : M →₀ ℤ, (∀ m ∈ a.support, c m = c n) ∧
        Finsupp.linearCombination ℤ f a = Finsupp.single i 1 := by
      intro i hi
      obtain ⟨hc, hlt'⟩ := hvsupp i hi
      obtain ⟨a, ha1, ha2⟩ := ih _ hlt' (L.symm i) rfl
      refine ⟨a, fun m hm => (ha1 m hm).trans hc, ?_⟩
      rw [ha2, Equiv.apply_symm_apply]
    choose! g hg1 hg2 using hex
    refine ⟨Finsupp.single n 1 + ∑ i ∈ v.support, v i • g i, ?_, ?_⟩
    · intro m hm
      rcases Finset.mem_union.1 (Finsupp.support_add hm) with hm1 | hm1
      · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hm1
        rw [hm1]
      · have hex' : ∃ i ∈ v.support, m ∈ (v i • g i).support := by
          by_contra h
          have hz : (∑ i ∈ v.support, v i • g i) m = 0 := by
            rw [Finset.sum_apply']
            apply Finset.sum_eq_zero
            intro i hi
            apply Finsupp.notMem_support_iff.mp
            exact fun hmi => h ⟨i, hi, hmi⟩
          exact Finsupp.mem_support_iff.mp hm1 hz
        obtain ⟨i, hi, hmi⟩ := hex'
        exact hg1 i hi m (Finsupp.support_smul hmi)
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [map_add (f := _), map_sum, Finsupp.linearCombination_single, one_smul]
        rw [Finset.sum_congr rfl (fun i hi => by rw [map_smul, hg2 i hi])]
        have hsum : ∑ i ∈ v.support, v i • Finsupp.single i (1 : ℤ) = v := by
          conv_rhs => rw [← Finsupp.sum_single v]
          rw [Finsupp.sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finsupp.smul_single, smul_eq_mul, mul_one]
        rw [hsum, hv]
        abel

theorem uni_bij {M I C : Type*} (L : M ≃ I) (c : M → C) (w : M → ℕ) (b : C → ℕ) (f : M → I →₀ ℤ)
    (hb : ∀ m, w m ≤ b (c m)) (h1 : ∀ m, f m (L m) = 1)
    (hlt : ∀ m n, f m (L n) ≠ 0 → c m = c n ∧ (m = n ∨ w m < w n)) :
    Function.Bijective (Finsupp.linearCombination ℤ f) := by
  refine ⟨uni_inj L w f h1 (fun m n hf => (hlt m n hf).2), ?_⟩
  have hrange : ∀ i, Finsupp.single i (1 : ℤ) ∈ LinearMap.range (Finsupp.linearCombination ℤ f) := by
    intro i
    obtain ⟨a, -, ha⟩ := uni_exists L c w b f hb h1 hlt (L.symm i)
    rw [Equiv.apply_symm_apply] at ha
    exact LinearMap.mem_range.2 ⟨a, ha⟩
  intro g
  have hg : g ∈ LinearMap.range (Finsupp.linearCombination ℤ f) := by
    refine Finsupp.induction_linear g ?_ ?_ ?_
    · exact Submodule.zero_mem _
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy
    · intro i r
      have hmem := Submodule.smul_mem _ r (hrange i)
      rwa [Finsupp.smul_single, smul_eq_mul, mul_one] at hmem
  exact LinearMap.mem_range.1 hg

end PositivityTheory.Groth.ChartWirtingerDerivatives

namespace PositivityTheory.Groth

theorem triAut : TriAut := fun _ w ψ h => ChartWirtingerDerivatives.tri_bij w ψ h

theorem uniTri : UniTri := fun _ _ _ L c w b f hb h1 hlt =>
  ⟨ChartWirtingerDerivatives.uni_bij L c w b f hb h1 hlt, ChartWirtingerDerivatives.uni_exists L c w b f hb h1 hlt⟩

end PositivityTheory.Groth
end

