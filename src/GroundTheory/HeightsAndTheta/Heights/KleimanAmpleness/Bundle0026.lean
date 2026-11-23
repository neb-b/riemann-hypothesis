module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistBundleToSubSystem
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropFiltStep
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSurjectiveClosed
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0019

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutDimLower
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section CutDimLowerAux

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem exists_monos_mul_mem_twistMod_all (L : LineBundle S x) (I : Chart x) (y : Ω)
    (hy : ∀ δ ∈ L.sub I, y * δ ∈ chartRing S x I) :
    ∃ U ∈ monos (S := S) I.1, ∃ dU : ℕ, U.IsHomogeneous dU ∧
      ∀ (K : Chart x), ∀ δ ∈ L.sub K, aeval x U * (y * δ) ∈ twistMod S x (dU : ℤ) K := by
  classical
  have hyU := mul_mem_chartRing_union L.toSubFamily I
  choose G hG using fun K => L.fg K
  have hgen : ∀ p : Σ K : Chart x, (G K : Set Ω),
      y * (p.2 : Ω) ∈ chartRing S x (chartUnion I p.1) := fun p =>
    hyU p.1 y hy _ (L.mono p.1 (chartUnion I p.1)
      (show p.1.1 ⊆ (chartUnion I p.1).1 from Finset.subset_union_right) _
      (by rw [← hG p.1]; exact Submodule.subset_span p.2.2))
  choose u hu d hd hud using fun p : (Σ K : Chart x, (G K : Set Ω)) =>
    exists_monos_mul_mem_twistMod (S := S) I p.1 (y * (p.2 : Ω)) (hgen p)
  obtain ⟨U, hUdef⟩ : ∃ U : Poly S N, U = ∏ p, u p := ⟨_, rfl⟩
  obtain ⟨dU, hdUdef⟩ : ∃ dU : ℕ, dU = ∑ p, d p := ⟨_, rfl⟩
  have hUm : U ∈ monos (S := S) I.1 := hUdef ▸ prod_mem fun p _ => hu p
  have hUh : U.IsHomogeneous dU := hUdef ▸ hdUdef ▸ IsHomogeneous.prod _ _ _ fun p _ => hd p
  have key : ∀ p : Σ K : Chart x, (G K : Set Ω),
      aeval x U * (y * (p.2 : Ω)) ∈ twistMod S x (dU : ℤ) p.1 := by
    intro p
    have hsplit : U = u p * ∏ q ∈ Finset.univ.erase p, u q := by
      rw [hUdef, Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
    have hdsplit : dU = d p + ∑ q ∈ Finset.univ.erase p, d q := by
      rw [hdUdef, Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have h2 := aeval_mem_twistMod (x := x)
      (IsHomogeneous.prod _ _ _ fun q _ => hd q : (∏ q ∈ Finset.univ.erase p, u q).IsHomogeneous _) p.1
    have h3 := twistMod_mul_mem (hud p) h2
    rw [hsplit, hdsplit, map_mul, Nat.cast_add]
    convert h3 using 1
    ring
  refine ⟨U, hUm, dU, hUh, fun K δ hδ => ?_⟩
  rw [← hG K] at hδ
  induction hδ using Submodule.span_induction with
  | mem δ hδ => exact key ⟨K, ⟨δ, hδ⟩⟩
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add, mul_add]; exact add_mem ha hb
  | smul a b _ hb =>
    rw [chartRing_smul_def, show aeval x U * (y * ((a : Ω) * b)) = (a : Ω) * (aeval x U * (y * b)) by ring,
      ← chartRing_smul_def]
    exact Submodule.smul_mem _ a hb

end CutDimLowerAux

theorem CutDimLower.proof : CutDimLower.Statement.{u, w} := by
  classical
  intro k _ Ω _ _ N x n pp L s qq hW hs hqq hjq
  obtain ⟨j, hj⟩ := hjq
  have hpp : pp.IsPrime := hW.isPrime
  have hqp : qq.IsPrime := hqq.1.1
  have hle : pp ⊔ zeroIdeal L.toSubSystem s ≤ qq := hqq.1.2
  have hppq : pp ≤ qq := le_sup_left.trans hle
  have hZq : zeroIdeal L.toSubSystem s ≤ qq := le_sup_right.trans hle

  have hvan : ∀ {F : Poly k N} {e : ℕ}, F.IsHomogeneous e → aeval x F = 0 → F ∈ pp := fun hF h0 =>
    hW.le ((mem_primeOf_of_isHomogeneous x hF).mpr h0)
  have hxj : x j ≠ 0 := by
    intro h0
    exact hj (hppq (hvan (isHomogeneous_X k j) (by rw [aeval_X, h0])))
  set J : Chart x := singleChart hxj with hJdef
  have hjJ : j ∈ J.1 := Finset.mem_singleton_self j
  have hmono : ∀ {t : Poly k N}, t ∈ monos (S := k) J.1 → t ∉ qq := fun ht =>
    monos_not_mem (fun i hi => by rw [Finset.mem_singleton.mp hi]; exact hj) ht

  have hone : (1 : Ω) ∉ idealMod (x := x) qq J := by
    intro h1
    obtain ⟨g, t, e, hg, ht, hge, hte, h1⟩ := idealMod_mem_form qq J h1
    have ht0 := eval_ne_zero_of_mem_monos J ht
    have hgt : aeval x g = aeval x t := by
      rw [eq_div_iff ht0, one_mul] at h1; exact h1.symm
    have hd : g - t ∈ qq := hppq (hvan (hge.sub hte) (by rw [map_sub, hgt, sub_self]))
    exact hmono ht (by simpa using sub_mem hg hd)

  obtain ⟨Q', hQ'⟩ := L.invertible J
  have hLQ : ∀ l ∈ L.sub J, ∀ q ∈ Q', l * q ∈ chartRing k x J := by
    intro l hl q hq
    have h := Submodule.mul_mem_mul hl hq
    rw [hQ', Submodule.mem_one] at h
    obtain ⟨y, hy⟩ := h
    rw [← hy]
    exact y.2
  obtain ⟨l, hl, q, hq, hu⟩ : ∃ l ∈ L.sub J, ∃ q ∈ Q', l * q ∉ idealMod (x := x) qq J := by
    by_contra hcon
    push Not at hcon
    have h1 : L.sub J * Q' ≤ idealMod (x := x) qq J := Submodule.mul_le.mpr fun l hl q hq => hcon l hl q hq
    rw [hQ'] at h1
    exact hone (h1 (Submodule.mem_one.mpr ⟨1, map_one _⟩))

  have hsJ : s ∈ L.sub J := (Submodule.mem_iInf _).mp hs J
  obtain ⟨f, t0, e, ht0, hf, ht0e, ha⟩ := hLQ s hsJ q hq
  have ht00 := eval_ne_zero_of_mem_monos J ht0
  have hfz : s * q * aeval x t0 = aeval x f := (eq_div_iff ht00).mp ha

  obtain ⟨U, hUm, dU, hUh, hUK⟩ := exists_monos_mul_mem_twistMod_all L J q
    (fun δ hδ => by rw [mul_comm]; exact hLQ δ hδ q hq)
  have hfU : f * U ∈ zeroIdeal L.toSubSystem s := by
    refine Ideal.subset_span ⟨e + dU, hf.mul hUh, fun K δ hδ => ?_⟩
    refine ⟨aeval x t0 * (aeval x U * (q * δ)), ?_, ?_⟩
    · rw [Nat.cast_add]
      exact twistMod_mul_mem (aeval_mem_twistMod ht0e K) (hUK K δ hδ)
    · rw [map_mul, ← hfz]; ring
  have hfq : f ∈ qq := (hqp.mem_or_mem (hZq hfU)).resolve_right (hmono hUm)

  obtain ⟨U', t2, eU, ht2, hU'h, ht2e, hUdef⟩ := hLQ l hl q hq
  have hU'q : U' ∉ qq := fun h => hu (hUdef ▸ Submodule.subset_span ⟨U', t2, eU, h, ht2, hU'h, ht2e, rfl⟩)
  have ht20 := eval_ne_zero_of_mem_monos J ht2
  have hU'v : aeval x U' = l * q * aeval x t2 := ((eq_div_iff ht20).mp hUdef).symm
  have hgen : ∀ h ∈ {f' : Poly k N | ∃ c : ℕ, f'.IsHomogeneous c ∧ ∀ (I : Chart x), ∀ δ ∈ L.toSubSystem.sub I,
      ∃ o ∈ twistMod k x (c : ℤ) I, aeval x f' * δ = s * o},
      ∃ t : Poly k N, t ∉ qq ∧ t * h ∈ pp ⊔ Ideal.span {f} := by
    rintro h ⟨c, hc, hh⟩
    obtain ⟨o, ho, hho⟩ := hh J l hl
    rw [twistMod_eq_span (c : ℤ) J hjJ, Submodule.mem_span_singleton] at ho
    obtain ⟨b, rfl⟩ := ho
    obtain ⟨B, t1, eb, ht1, hB, ht1e, hb⟩ := b.2
    have ht10 := eval_ne_zero_of_mem_monos J ht1
    have hBv : aeval x B = (b : Ω) * aeval x t1 := ((eq_div_iff ht10).mp hb).symm
    rw [chartRing_smul_def, zpow_natCast] at hho
    have hF1 : (U' * h * t0 * t1).IsHomogeneous (eU + c + e + eb) := ((hU'h.mul hc).mul ht0e).mul ht1e
    have hF2 : (f * (B * X j ^ c * t2)).IsHomogeneous (eU + c + e + eb) := by
      have := hf.mul ((hB.mul (isHomogeneous_X_pow j c)).mul ht2e)
      rwa [show e + (eb + c + eU) = eU + c + e + eb by ring] at this
    have hFv : aeval x (U' * h * t0 * t1 - f * (B * X j ^ c * t2)) = 0 := by
      simp only [map_sub, map_mul, map_pow, aeval_X]
      rw [hU'v, hBv, ← hfz]
      linear_combination (q * aeval x t2 * aeval x t0 * aeval x t1) * hho
    refine ⟨U' * t0 * t1, ?_, ?_⟩
    · intro hmem
      rcases hqp.mem_or_mem hmem with h1 | h1
      · rcases hqp.mem_or_mem h1 with h2 | h2
        · exact hU'q h2
        · exact hmono ht0 h2
      · exact hmono ht1 h1
    · have hsplit : U' * t0 * t1 * h =
          (U' * h * t0 * t1 - f * (B * X j ^ c * t2)) + f * (B * X j ^ c * t2) := by ring
      rw [hsplit]
      exact add_mem (Ideal.mem_sup_left (hvan (hF1.sub hF2) hFv))
        (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)))

  have hmin : qq ∈ (pp ⊔ Ideal.span {f}).minimalPrimes := by
    refine ⟨⟨hqp, sup_le hppq ((Ideal.span_singleton_le_iff_mem qq).mpr hfq)⟩, ?_⟩
    rintro r ⟨hr, hfr⟩ hrq
    refine hqq.2 ⟨hr, sup_le (le_sup_left.trans hfr) (Ideal.span_le.mpr ?_)⟩ hrq
    intro h hh
    obtain ⟨t, htq, hth⟩ := hgen h hh
    exact (hr.mem_or_mem (hfr hth)).resolve_left fun h' => htq (hrq h')

  have hQ := Ideal.map_height_le_one_of_mem_minimalPrimes hmin
  have := hpp
  have : (qq.map (Ideal.Quotient.mk pp)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have key := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient k
    (qq.map (Ideal.Quotient.mk pp))
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hppq), hW.dim] at key
  have hnn : (0 : WithBot ℕ∞) ≤ ringKrullDim (Poly k N ⧸ qq) := ringKrullDim_nonneg_of_nontrivial
  generalize ringKrullDim (Poly k N ⧸ qq) = D at key hnn ⊢
  generalize (qq.map (Ideal.Quotient.mk pp)).height = H at key hQ
  induction D using WithBot.recBotCoe with
  | bot => exact absurd hnn (by simp)
  | coe d =>
    have key' : H + d = ((n + 1 + 1 : ℕ) : ℕ∞) := by exact_mod_cast key
    suffices ((n + 1 : ℕ) : ℕ∞) ≤ d by exact_mod_cast this
    induction d using ENat.recTopCoe with
    | top => exact le_top
    | coe m =>
      induction H using ENat.recTopCoe with
      | top => simp at hQ
      | coe h =>
        have h1 : h ≤ 1 := by exact_mod_cast hQ
        have h2 : h + m = n + 1 + 1 := by exact_mod_cast key'
        exact_mod_cast (by omega : n + 1 ≤ m)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCycleSplitFiltStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace CycleSplit.Filt.Step

theorem length_ne_top_of_smul_eq_zero {S : Type u} [CommRing S] {T : Type w} [AddCommGroup T] [Module S T]
    [Module.Finite S T] (𝔪 : Ideal S) [𝔪.IsMaximal] (h : ∀ a ∈ 𝔪, ∀ t : T, a • t = 0) :
    Module.length S T ≠ ⊤ := by
  let := Ideal.Quotient.field 𝔪
  have hT : Module.IsTorsionBySet S T 𝔪 := by
    intro t a
    exact h a a.2 t
  let : Module (S ⧸ 𝔪) T := hT.module
  have : IsScalarTower S (S ⧸ 𝔪) T := hT.isScalarTower
  have : Module.Finite (S ⧸ 𝔪) T := Module.Finite.of_restrictScalars_finite S (S ⧸ 𝔪) T
  rw [Module.length_eq_of_surjective (R := S ⧸ 𝔪) (M := T) Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

theorem proof (hSC : SurjectiveClosed.Statement.{u, w}) (hFS : FiniteSections.Statement.{u, w}) :
    CycleSplit.Filt.Step.Statement.{u, w} := by
  classical
  intro S _ _ Ω _ _ N x 𝔪 h𝔪 K pp g e hKh hK h𝔪K hg hpph hpp Q
  obtain ⟨c₀, hc₀⟩ := hSC S Ω N x Q pp hpph
  filter_upwards [eventually_ge_atTop (c₀ + e).toNat] with c hc
  have hce : c₀ ≤ (c : ℤ) - e := by
    have := Int.toNat_le.mp hc
    omega
  set F : SubSystem S x Ω := Q.twist (twistSys S x (c : ℤ)) with hF
  set F' : SubSystem S x Ω := Q.twist (twistSys S x ((c : ℤ) - e)) with hF'
  have hF'eq : F' = F.twist (twistSys S x (-(e : ℤ))) := by
    rw [hF', hF, SubSystem.twist_assoc, twistSys_twist_eq_add, sub_eq_add_neg]
  have hsub : ∀ (J : Ideal (Poly S N)) (I : Chart x),
      (F.twist (idealSys x J)).sub I = idealMod J I * F.sub I :=
    fun J I ↦ SubSystem.twist_sub_eq_mul_of_line _ _ I
  have hF's : ∀ I, F'.sub I = twistMod S x (-(e : ℤ)) I * F.sub I := fun I ↦ by
    rw [hF'eq]; exact SubSystem.twist_sub_eq_mul_of_line _ _ I
  have hF'p : ∀ I, (F'.twist (idealSys x pp)).sub I =
      idealMod pp I * (twistMod S x (-(e : ℤ)) I * F.sub I) := fun I ↦ by
    rw [SubSystem.twist_sub_eq_mul_of_line, hF's]; rfl
  have hinv : ∀ I, ∃ Q' : Submodule (chartRing S x I) Ω, F.sub I * Q' = 1 :=
    fun I ↦ (Q.tensorProd (twistBundle S x (c : ℤ))).invertible I

  have hgK' : ∀ I : Chart x, ∀ y ∈ F'.sub I,
      aeval x g * y ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).sub I := by
    intro I y hy
    obtain ⟨i, hi⟩ := I.2.1
    rw [hF's, twistMod_eq_span _ I hi] at hy
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_span_singleton_mul.mp hy
    rw [hsub]
    have hγ : aeval x g / x i ^ e ∈ idealMod (K ⊔ Ideal.span {g}) I :=
      Submodule.subset_span ⟨g, X i ^ e, e, Ideal.mem_sup_right (Ideal.mem_span_singleton_self g),
        pow_mem (X_mem_monos hi) e, hg, isHomogeneous_X_pow i e, by simp⟩
    have h1 : aeval x g * (x i ^ (-(e : ℤ)) * q) = aeval x g / x i ^ e * q := by
      rw [← mul_assoc, zpow_neg, zpow_natCast, div_eq_mul_inv]
    rw [h1]
    exact Submodule.mul_mem_mul hγ hq
  have hU : ∀ I (y : Ω), y ∈ F'.sub I → aeval x g * y ∈ (F.twist (idealSys x K)).sub I →
      y ∈ (F'.twist (idealSys x pp)).sub I := by
    intro I y hy hgy
    obtain ⟨i, hi⟩ := I.2.1
    obtain ⟨Q', hQ'⟩ := hinv I
    rw [hF's] at hy
    rw [hsub] at hgy
    rw [hF'p]
    exact SectionCount.Drop.Filt.Step.mem_chart_of_mul_mem hK hpp hg I hi _ Q' hQ' hy hgy
  have hC : ∀ I (y : Ω), y ∈ (F'.twist (idealSys x pp)).sub I →
      aeval x g * y ∈ (F.twist (idealSys x K)).sub I := by
    intro I y hy
    obtain ⟨i, hi⟩ := I.2.1
    rw [hF'p] at hy
    rw [hsub]
    exact SectionCount.Drop.Filt.Step.mul_mem_chart hpp hg I hi _ hy
  have hE : ∀ s ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs, ∀ I,
      ∃ y ∈ F'.sub I, s - aeval x g * y ∈ (F.twist (idealSys x K)).sub I := by
    intro s hs I
    obtain ⟨i, hi⟩ := I.2.1
    have hsI := SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hs I
    rw [hsub] at hsI
    rw [hF's, hsub]
    exact SectionCount.Drop.Filt.Step.exists_chart hKh hg I hi _ hsI

  have hWV : ∀ z, z ∈ (F.twist (idealSys x K)).secs →
      z ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs := by
    intro z hz
    refine SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ ?_
    have h1 := SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hz I
    rw [hsub] at h1 ⊢
    have hle : idealMod K I ≤ idealMod (K ⊔ Ideal.span {g}) I := by
      refine Submodule.span_mono ?_
      rintro _ ⟨f, s, d, hf, hs, hfd, hsd, rfl⟩
      exact ⟨f, s, d, Ideal.mem_sup_left hf, hs, hfd, hsd, rfl⟩
    exact (Submodule.mul_le.mpr fun m hm n hn ↦ Submodule.mul_mem_mul (hle hm) hn) h1
  have hVH : ∀ z, z ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs → z ∈ F.secs := fun z hz ↦
    SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ SurjectiveClosed.twist_idealSys_le F _ I (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hz I)
  have hgsec : ∀ y ∈ F'.secs, aeval x g * y ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs :=
    fun y hy ↦ SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ hgK' I y (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hy I)

  have hlift : ∀ s ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs,
      ∃ t ∈ F'.secs, s - aeval x g * t ∈ (F.twist (idealSys x K)).secs := by
    intro s hs
    choose y hy hys using hE s hs
    have hcomp : ∀ (I₁ I₂ : Chart x), I₁.1 ⊆ I₂.1 →
        y I₁ - y I₂ ∈ (F'.twist (idealSys x pp)).sub I₂ := by
      intro I₁ I₂ h
      refine hU I₂ _ (sub_mem (F'.mono I₁ I₂ h _ (hy I₁)) (hy I₂)) ?_
      have h1 := sub_mem (hys I₂) ((F.twist (idealSys x K)).mono I₁ I₂ h _ (hys I₁))
      convert h1 using 1
      ring
    obtain ⟨t, ht, htI⟩ := hc₀ _ hce y hy hcomp
    refine ⟨t, ht, SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ ?_⟩
    have h1 := add_mem (hys I) (hC I _ (neg_mem (htI I)))
    convert h1 using 1
    ring

  set H := F.secs with hH
  set H' := F'.secs with hH'
  set A := ((F.twist (idealSys x K)).secs).comap H.subtype with hA
  set B := ((F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs).comap H.subtype with hB
  set P := ((F'.twist (idealSys x pp)).secs).comap H'.subtype with hP
  have hAB : A ≤ B := fun z hz ↦ Submodule.mem_comap.mpr (hWV _ (Submodule.mem_comap.mp hz))
  let μ0 : H' →ₗ[S] H := (LinearMap.mulLeft S (aeval x g)).restrict (p := H') (q := H)
    (fun y hy ↦ hVH _ (hgsec y hy))
  let μ : H' →ₗ[S] H ⧸ A := A.mkQ ∘ₗ μ0
  have hμ : ∀ y : H', y ∈ P ↔ μ y = 0 := by
    intro y
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.mem_comap]
    change (y : Ω) ∈ _ ↔ aeval x g * (y : Ω) ∈ _
    constructor
    · intro h
      exact SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ hC I _ (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp h I)
    · intro h
      exact SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ hU I _ (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp y.2 I) (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp h I)
  let μb : (H' ⧸ P) →ₗ[S] H ⧸ A := P.liftQ μ (fun y hy ↦ (hμ y).mp hy)
  have hinj : Function.Injective μb := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (fun y hy ↦ (hμ y).mpr hy)
  let π : (H ⧸ A) →ₗ[S] H ⧸ B := Submodule.factor hAB
  have hsurj : Function.Surjective π := by
    intro z
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective B z
    exact ⟨A.mkQ m, rfl⟩
  have hex : Function.Exact μb π := by
    intro z
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective A z
    change B.mkQ m = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    constructor
    · intro hm
      obtain ⟨t, ht, hst⟩ := hlift _ hm
      change (m : Ω) - aeval x g * t ∈ _ at hst
      refine ⟨P.mkQ ⟨t, ht⟩, ?_⟩
      change A.mkQ (μ0 ⟨t, ht⟩) = A.mkQ m
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap]
      change aeval x g * t - (m : Ω) ∈ _
      have h1 := neg_mem hst
      convert h1 using 1
      ring
    · rintro ⟨w, hw⟩
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective P w
      change A.mkQ (μ0 y) = A.mkQ m at hw
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap] at hw
      change aeval x g * (y : Ω) - m ∈ _ at hw
      change (m : Ω) ∈ _
      have h1 := sub_mem (hgsec _ y.2) (hWV _ hw)
      convert h1 using 1
      ring
  have hlen := Module.length_eq_add_of_exact μb π hinj hsurj hex

  have hfin : Module.length S (H ⧸ A) ≠ ⊤ := by
    by_cases hx : x = 0
    · have hE0 : IsEmpty (Chart x) := ⟨fun I ↦ by
        obtain ⟨i, hi⟩ := I.2.1
        exact (mem_support x).mp (I.2.2 hi) (by simp [hx])⟩
      have hAt : A = ⊤ := eq_top_iff.mpr fun m _ ↦
        Submodule.mem_comap.mpr (SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ isEmptyElim I)
      have : Subsingleton (H ⧸ A) := Submodule.Quotient.subsingleton_iff.mpr hAt
      rw [Module.length_eq_zero]
      exact ENat.zero_ne_top
    · have : Module.Finite S H := (hFS S Ω N x (Q.tensorProd (twistBundle S x (c : ℤ))) hx).1
      have := h𝔪
      refine length_ne_top_of_smul_eq_zero 𝔪 fun a ha z ↦ ?_
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective A z
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      change a • (m : Ω) ∈ _
      refine SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ ?_
      rw [hsub, Algebra.smul_def]
      refine Submodule.mul_mem_mul ?_ (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp m.2 I)
      exact Submodule.subset_span ⟨C a, 1, 0, h𝔪K (Ideal.mem_map_of_mem _ ha), one_mem _,
        isHomogeneous_C _ _, isHomogeneous_one _ _, by simp⟩
  have hB' : Module.length S (H ⧸ B) ≠ ⊤ := fun h ↦ hfin (by rw [hlen, h, add_top])
  have hP' : Module.length S (H' ⧸ P) ≠ ⊤ := fun h ↦ hfin (by rw [hlen, h, top_add])
  change ((Module.length S (H ⧸ A)).toNat : ℤ) =
    ((Module.length S (H ⧸ B)).toNat : ℤ) + ((Module.length S (H' ⧸ P)).toNat : ℤ)
  rw [hlen, ENat.toNat_add hP' hB']
  push_cast
  ring

end CycleSplit.Filt.Step

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefRestrict
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section Helpers

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem tensorSub_single (L : SubSystem S x Ω) (T : Finset (Fin 1)) :
    tensorSub ![L] T = if (0 : Fin 1) ∈ T then L else twistSys S x 0 := by
  have hf : List.finRange 1 = [0] := rfl
  split_ifs with h
  · simp [tensorSub, hf, h, twistSys_zero_twist]
  · simp [tensorSub, hf, h]

end Helpers

theorem NefRestrict.proof (hRT : RestrictTwist.Statement.{u, w})
    (hRL : RestrLenRestrict.Statement.{u, w}) : NefRestrict.Statement.{u, w} := by
  intro k _ Ω _ _ N x K' _ _ y hxy hle M M' r hr hnef pp _ hpp
  have hx : IsSubvar x pp 1 := ⟨hpp.isPrime, hpp.homog, hle.trans hpp.le, hpp.relevant, hpp.dim⟩
  obtain ⟨r₀, hr₀⟩ := hRT.1 k Ω N x K' y hxy hle 0
  have hM := hRL k Ω N x K' y hxy hle pp 1 hpp M M' r hr
  have hO := hRL k Ω N x K' y hxy hle pp 1 hpp (twistBundle k x 0) (twistBundle k y 0) r₀ hr₀
  have heq : interSum pp ![M'.toSubSystem] =ᶠ[atTop] interSum pp ![M.toSubSystem] := by
    filter_upwards [hM, hO] with c hMc hOc
    unfold interSum
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [tensorSub_single, tensorSub_single]
    split_ifs
    · rw [hMc]
    · exact congrArg _ hOc
  have hnum : interNum pp ![M'.toSubSystem] = interNum pp ![M.toSubSystem] := by
    unfold interNum limUnder
    rw [Filter.map_congr heq]
  rw [hnum]
  exact hnef pp bot_le hx

end

end GroundTheory.Heights₂.Heights.Kleiman
end

