module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemInvCoeIdeal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0014
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0026
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0019

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SemidefG
section
noncomputable section

open NumberField Module Formalism.MainNotions.S
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) {r : ℕ}

theorem hsw (x y : S.V) : S.hT y x = star (S.hT x y) := (S.herm.eq x y).symm

theorem hsw0 {x y : S.V} (h : S.hT x y = 0) : S.hT y x = 0 := by rw [hsw, h, star_zero]

variable {S}
variable (e y : Fin r → S.V) (z : S.V) (N : ℕ)

structure Dual : Prop where
  ee : ∀ a b, S.hT (e a) (e b) = 0
  yy : ∀ a b, S.hT (y a) (y b) = 0
  ey : ∀ a b, S.hT (e a) (y b) = if a = b then 1 else 0
  ez : ∀ a, S.hT (e a) z = 0
  yz : ∀ a, S.hT (y a) z = 0
  zz : S.hT z z = -(N : E)

def IsW (w : S.V) : Prop := (∀ a, S.hT (e a) w = 0) ∧ (∀ a, S.hT (y a) w = 0) ∧ S.hT z w = 0

variable {e y z N}

theorem Dual.ye (h : Dual e y z N) (a b) : S.hT (y a) (e b) = if b = a then 1 else 0 := by
  rw [hsw, h.ey]; split_ifs <;> simp

theorem real_of (τ : E →+* ℂ) (hτc : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) (w : S.V) :
    τ (S.hT w w) = ((τ (S.hT w w)).re : ℂ) := by
  have h1 : starRingEnd ℂ (τ (S.hT w w)) = τ (S.hT w w) := by
    rw [← hτc, ← hsw]
  have him : (τ (S.hT w w)).im = 0 := Complex.conj_eq_iff_im.1 h1
  exact Complex.ext (by simp) (by simp [him])

theorem semidefG (h : Dual e y z N) (hN : 0 < N) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    {p' : ℕ} (hsig : Formalism.UG.HasSignature (S.gram.map τ) p' (r + 1)) (w : S.V) (hw : IsW e y z w) :
    0 ≤ (τ (S.hT w w)).re := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨hE, hF, hz⟩ := hw
  have hT0 : (0 : ℝ) < N := by exact_mod_cast hN
  let wv : Fin r ⊕ Bool → S.V := Sum.elim (fun a => e a - y a) (fun b => if b then w else z)
  let d : Fin r ⊕ Bool → ℝ := Sum.elim (fun _ => -2) (fun b => if b then (τ (S.hT w w)).re else -(N : ℝ))
  have hoff : ∀ i j, i ≠ j → S.hT (wv i) (wv j) = 0 := by
    intro i j hij
    rcases i with a | b <;> rcases j with a' | b'
    · have ha : a ≠ a' := fun h => hij (by rw [h])
      have ha' : a' ≠ a := fun h => ha h.symm
      simp only [wv, Sum.elim_inl, map_sub, LinearMap.sub_apply, h.ee, h.yy, h.ey, h.ye, if_neg ha, if_neg ha']
      simp
    · cases b'
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, if_false, map_sub,
          LinearMap.sub_apply, h.ez, h.yz, sub_zero]
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, if_true, map_sub, LinearMap.sub_apply, hE, hF, sub_zero]
    · cases b
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, if_false, map_sub,
          hsw0 S (h.ez a'), hsw0 S (h.yz a'), sub_zero]
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, if_true, map_sub, hsw0 S (hE a'), hsw0 S (hF a'), sub_zero]
    · cases b <;> cases b'
      · exact absurd rfl hij
      · simpa [wv] using hz
      · simpa [wv] using hsw0 S hz
      · exact absurd rfl hij
  have hdiag : ∀ i, τ (S.hT (wv i) (wv i)) = (d i : ℂ) := by
    intro i
    rcases i with a | b
    · simp only [wv, d, Sum.elim_inl, map_sub, LinearMap.sub_apply, h.ee, h.yy, h.ey, h.ye, if_true]
      simp only [map_zero, map_one]
      push_cast; ring
    · cases b
      · simp only [wv, d, Sum.elim_inr, Bool.false_eq_true, if_false, h.zz, map_neg, map_natCast]
        push_cast; ring
      · simp only [wv, d, Sum.elim_inr, if_true]
        exact real_of τ hτ w
  have hneg : ∀ i, d i < 0 := by
    intro i
    rcases i with a | b
    · simp [d]
    · cases b
      · simp only [d, Sum.elim_inr, Bool.false_eq_true, if_false]; linarith
      · simpa [d] using hlt
  have hc := PI.CntNotPosW.card_le_of_negFamily S τ hτ hsig wv d hoff hdiag hneg
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool] at hc
  omega

theorem isoZeroG (h : Dual e y z N) (hN : 0 < N) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    (hsemi : ∀ w, IsW e y z w → 0 ≤ (τ (S.hT w w)).re) (w : S.V) (hw : IsW e y z w) (h0 : S.hT w w = 0) :
    w = 0 := by
  obtain ⟨hE, hF, hz⟩ := hw
  have orthW : ∀ v : S.V, IsW e y z v → S.hT w v = 0 := by
    rintro v ⟨hvE, hvF, hvz⟩
    by_contra hx
    set x := S.hT w v with hxdef
    have hτx : τ x ≠ 0 := (map_ne_zero τ).2 hx
    have hNq : 0 < Complex.normSq (τ x) := Complex.normSq_pos.2 hτx
    set v' : S.V := star x • v with hv'
    have hxx : τ (x * star x) = ((Complex.normSq (τ x) : ℝ) : ℂ) := by
      rw [map_mul, hτ, Complex.mul_conj]
    have key : ∀ n : ℕ, 2 * n * Complex.normSq (τ x) ≤ (τ (S.hT v' v')).re := by
      intro n
      set u : S.V := (n : E) • w - v' with hu
      have huW : IsW e y z u := by
        refine ⟨fun a => ?_, fun a => ?_, ?_⟩
        · simp [hu, hv', map_sub, map_smul, hE a, hvE a]
        · simp [hu, hv', map_sub, map_smul, hF a, hvF a]
        · simp [hu, hv', map_sub, map_smul, hz, hvz]
      have hs := hsemi u huW
      have hyw : S.hT v w = star x := by rw [hsw]
      have e1 : S.hT u u = -(2 * (n : E)) * (x * star x) + S.hT v' v' := by
        simp only [hu, map_sub, LinearMap.sub_apply, map_smulₛₗ, LinearMap.smul_apply,
          smul_eq_mul, starRingEnd_apply, star_natCast, h0, hv', star_star, hyw, ← hxdef, RingHom.id_apply]
        ring
      have e2 : (τ (S.hT u u)).re = -(2 * n * Complex.normSq (τ x)) + (τ (S.hT v' v')).re := by
        rw [e1, map_add (f := _), map_mul, hxx, map_neg, map_mul, map_ofNat, map_natCast, Complex.add_re]
        congr 1
        have : -(2 * (n : ℂ)) * ((Complex.normSq (τ x) : ℝ) : ℂ) =
            ((-(2 * n * Complex.normSq (τ x)) : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.ofReal_re]
      linarith
    obtain ⟨n, hn⟩ := exists_nat_gt ((τ (S.hT v' v')).re / (2 * Complex.normSq (τ x)))
    have h2 := key n
    rw [div_lt_iff₀ (by positivity)] at hn
    nlinarith
  have hzz : S.hT z z ≠ 0 := by
    rw [h.zz, neg_ne_zero]; exact_mod_cast hN.ne'
  apply S.nondeg.1 w
  intro x
  set xW : S.V := x - ∑ a, (S.hT (y a) x • e a + S.hT (e a) x • y a) - (S.hT z x / S.hT z z) • z with hxW
  have hzE : ∀ a, S.hT z (e a) = 0 := fun a => hsw0 S (h.ez a)
  have hzF : ∀ a, S.hT z (y a) = 0 := fun a => hsw0 S (h.yz a)
  have hWE : ∀ b, S.hT (e b) xW = 0 := by
    intro b
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hxW, map_sub, map_sum, map_add (f := _), map_smul, h.ee, h.ey, h.ez]
  have hWF : ∀ b, S.hT (y b) xW = 0 := by
    intro b
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hxW, map_sub, map_sum, map_add (f := _), map_smul, h.yy, h.ye, h.yz]
  have hWz : S.hT z xW = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hxW, map_sub, map_sum, map_add (f := _), map_smul, hzE, hzF, hzz]
  have h1 := orthW xW ⟨hWE, hWF, hWz⟩
  have hwE : ∀ a, S.hT w (e a) = 0 := fun a => hsw0 S (hE a)
  have hwF : ∀ a, S.hT w (y a) = 0 := fun a => hsw0 S (hF a)
  have hwz : S.hT w z = 0 := hsw0 S hz
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [hxW, map_sub, map_sum, map_add (f := _), map_smul, hwE, hwF, hwz] using h1

end Gen

end Formalism.L2.SG.Pf.Cnt.R1
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.VdEqVJof
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G1

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem vd_eq_vJof (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭.IsMaximal)
    (b : Fin (finrank K (⊤ : Submodule K V)) → V) (a : Fin (finrank K (⊤ : Submodule K V)) → 𝓞 F)
    (hJ : Cnt.IsJordanIn h ⊤ L 𝔭 b a) : vd h L 𝔭 = Cnt.vJof 𝔭 a := by
  classical
  obtain ⟨P, hP, hPc⟩ := exists_over (K := K) 𝔭 h𝔭
  haveI := h𝔭.isPrime
  have e : Fin (finrank K (⊤ : Submodule K V)) ≃ Fin (finrank K V) := finCongr (finrank_top K V)
  have hmap : ∀ x : 𝓞 F, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap F K (x : F) := fun x => by
    rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]
  have hA0 : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hJ.2.2.2.2 i
  have horth : ∀ i j, i ≠ j → h (b (e.symm i)) (b (e.symm j)) = 0 :=
    fun i j hij => hJ.2.2.1 _ _ fun h' => hij (e.symm.injective h')
  have hrange : Set.range (fun j => b (e.symm j)) = Set.range b := e.symm.surjective.range_comp b

  have hgb : (U0.gram h fun j => b (e.symm j)).det =
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (∏ i, a i)) := by
    rw [gram_det_orth horth]
    have hp : ∏ j, h (b (e.symm j)) (b (e.symm j)) = ∏ i, h (b i) (b i) :=
      Fintype.prod_equiv e.symm _ _ fun _ => rfl
    rw [hp, map_prod, map_prod]
    exact Finset.prod_congr rfl fun i _ => by rw [hJ.2.2.2.1 i, hmap]
  have key : ∀ m : ℕ, discrIdeal h L ≤ extP K 𝔭 ^ m ↔ m ≤ vF 𝔭 (∏ i, a i) := by
    intro m
    constructor
    · intro hle
      have ht : ∀ i, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t • b i ∈ L := fun i => by
        have hb : b i ∈ locF 𝔭 L := by
          rw [← hJ.2.1]
          exact LocF.le_locF 𝔭 _ (Submodule.subset_span ⟨i, rfl⟩)
        exact (LocalSpans.mem_locF 𝔭 L (b i)).1 hb
      choose t ht1 ht2 using ht
      have ht0 : ∀ i, t i ≠ 0 := fun i h0 => ht1 i (h0 ▸ 𝔭.zero_mem)
      have hT0 : (∏ i, t i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ht0 i
      have hvT : vF 𝔭 (∏ i, t i) = 0 := by
        rw [vF_prod h𝔭 Finset.univ t ht0]
        exact Finset.sum_eq_zero fun i _ => vF_of_notMem h𝔭 (ht1 i)
      have hst : ∀ u : F, star (algebraMap F K u) = algebraMap F K u := fun u => (hF _).2 ⟨u, rfl⟩
      have hx : (U0.gram h fun j => algebraMap F K (t (e.symm j) : F) • b (e.symm j)).det =
          algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) ((∏ i, t i) * (∏ i, t i) * ∏ i, a i)) := by
        rw [gram_det_smul_orth horth]
        have hp1 : ∏ j, star (algebraMap F K (t (e.symm j) : F)) * algebraMap F K (t (e.symm j) : F) =
            ∏ i, algebraMap F K (t i : F) * algebraMap F K (t i : F) :=
          Fintype.prod_equiv e.symm _ _ fun j => by rw [hst]
        have hp2 : ∏ j, h (b (e.symm j)) (b (e.symm j)) = ∏ i, h (b i) (b i) :=
          Fintype.prod_equiv e.symm _ _ fun _ => rfl
        rw [hp1, hp2, map_mul, map_mul, map_mul, map_mul, map_prod, map_prod, map_prod, map_prod,
          Finset.prod_mul_distrib]
        simp only [hmap, hJ.2.2.2.1]
      have hxL : ∀ j, algebraMap F K (t (e.symm j) : F) • b (e.symm j) ∈ L := fun j => by
        rw [← hmap, algebraMap_smul]
        exact ht2 _
      have hmem : algebraMap (𝓞 F) (𝓞 K) ((∏ i, t i) * (∏ i, t i) * ∏ i, a i) ∈ discrIdeal h L :=
        Ideal.subset_span ⟨_, hxL, hx.symm⟩
      have h2 := hle hmem
      have h3 : (∏ i, t i) * (∏ i, t i) * ∏ i, a i ∈ 𝔭 ^ m := by
        rw [← MeanB.comap_extP_pow (K := K) 𝔭 m]
        exact h2
      rw [mem_pow_iff h𝔭 (mul_ne_zero (mul_ne_zero hT0 hT0) hA0), vF_mul h𝔭 (mul_ne_zero hT0 hT0) hA0,
        vF_mul h𝔭 hT0 hT0, hvT] at h3
      simpa using h3
    · intro hv
      unfold discrIdeal
      rw [Ideal.span_le]
      rintro z ⟨x, hxL, hz⟩
      have hx' : ∀ i, x i ∈ spanS (locRing P) fun j => b (e.symm j) := fun i => by
        have hxi : x i ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range fun j => b (e.symm j))) := by
          rw [hrange, hJ.2.1]
          exact LocF.le_locF 𝔭 L (hxL i)
        rw [← hPc] at hxi
        exact (mem_locF_span_iff hK hF hP _ (x i)).1 hxi
      obtain ⟨c, hc, hdet⟩ := gram_det_of_le (h := h) (isHermSemilocal_locRing hK hP) hx'
      obtain ⟨r, s, hs, hcr⟩ := (mem_locR_iff hP.isPrime c).1 hc
      have hsne := algebraMap_ne_zero_of_mem_hcompl hP.isPrime hs
      have hsz : s * z = r * algebraMap (𝓞 F) (𝓞 K) (∏ i, a i) := by
        apply IsFractionRing.injective (𝓞 K) K
        rw [map_mul, map_mul, hz]
        change _ * (U0.gram h x).det = _
        rw [hdet, hgb, hcr]
        field_simp
      have hAm : algebraMap (𝓞 F) (𝓞 K) (∏ i, a i) ∈ extP K 𝔭 ^ m := by
        rw [extP, ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ ((mem_pow_iff h𝔭 hA0 m).2 hv)
      have hcop := OrthogonalBases.sup_eq_top_of_mem_hcompl hK hF hP hs
      rw [hPc] at hcop
      exact mem_pow_of_coprime hcop m (hsz ▸ Ideal.mul_mem_left _ r hAm)
  have hv : Cnt.vJof 𝔭 a = vF 𝔭 (∏ i, a i) := (vF_prod h𝔭 Finset.univ a hJ.2.2.2.2).symm
  rw [hv]
  unfold vd
  simp_rw [key]
  exact csSup_Iic

end Formalism.L2.SG.Pf.G1
end
end

