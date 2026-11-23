module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.WspOrth
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.EvTSum
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem evT_sum {n : ℕ} (θ : Wt n) (c : FR n) :
    evT θ c = ∑ μ ∈ c.coeff.support, cf c μ * evT θ (ex μ) := by
  simp only [evT, ex, AddMonoidAlgebra.lift_single, one_smul]
  rw [AddMonoidAlgebra.lift_apply]
  simp only [Finsupp.sum, cf, smul_eq_mul]

theorem UpperTheory.RealTr.chEv :
    ∀ (n : ℕ) (N : Type) [NormedAddCommGroup N] [InnerProductSpace ℂ N] [FiniteDimensional ℂ N] (σ : UK n →* (N →ₗ[ℂ] N))
      (F : Fin n → Fin n → Module.End ℂ N), UF F → IsDerivK σ F → ∀ B c, Cm F ⊤ B → IsCh F ⊤ B c → ∀ (θ : Wt n) (k : UK n),
      k.1 = diagonal (fun a => Complex.exp (Complex.I * θ a)) → LinearMap.trace ℂ N (σ k * B) = evT θ c := by
  intro n N _ _ _ σ F hF hσ B c hB hc θ k hk
  classical
  obtain ⟨s, hs0, hsup, hind⟩ := wtDec n N F hF ⊤ inferInstance (fun _ _ _ _ => Submodule.mem_top)
  set W : Wt n → Submodule ℂ N := fun μ => wsp F μ ⊓ ⊤ with hW
  have hBW : ∀ μ, ∀ v ∈ W μ, B v ∈ W μ := by
    intro μ v hv
    rw [Submodule.mem_inf] at hv ⊢
    refine ⟨?_, Submodule.mem_top⟩
    have hv1 : IsWeight F μ v := hv.1
    show IsWeight F μ (B v)
    intro a
    have h1 := congrArg (fun T : Module.End ℂ N => T v) (hB.1 a a)
    simp only [Module.End.mul_apply] at h1
    rw [← h1, hv1 a, map_smul]
  have hσW : ∀ μ, ∀ v ∈ W μ, σ k v = evT θ (ex μ) • v := fun μ v hv =>
    (derAt n N σ F hσ).1 μ θ k v hk (Submodule.mem_inf.1 hv).1
  have hfW : ∀ μ, Set.MapsTo (σ k * B) (W μ) (W μ) := by
    intro μ v hv
    show σ k (B v) ∈ W μ
    rw [hσW μ _ (hBW μ v hv)]
    exact (W μ).smul_mem _ (hBW μ v hv)
  have hint : DirectSum.IsInternal (fun i : s => W i) := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact iSupIndep.comp hind Subtype.val_injective
    · rw [← hsup, iSup_subtype']
  have hterm : ∀ μ, LinearMap.trace ℂ (W μ) ((σ k * B).restrict (hfW μ)) = evT θ (ex μ) * cf c μ := by
    intro μ
    have hr : (σ k * B).restrict (hfW μ) = evT θ (ex μ) • B.restrict (hBW μ) := by
      ext v
      simp only [LinearMap.restrict_coe_apply, LinearMap.smul_apply, Module.End.mul_apply,
        Submodule.coe_smul]
      exact hσW μ _ (hBW μ v v.2)
    rw [hr, map_smul, smul_eq_mul, hc μ]
    unfold trOn
    rw [dite_eq_left (hBW μ)]
  have hz : ∀ μ, μ ∉ s → cf c μ = 0 := by
    intro μ hμ
    rw [hc μ, hs0 μ hμ]
    unfold trOn
    split_ifs with h
    · have h0 : B.restrict h = 0 := by
        ext x
      rw [h0, map_zero]
    · rfl
  rw [LinearMap.trace_eq_sum_trace_restrict hint (fun i => hfW i)]
  simp only [hterm]
  rw [Finset.sum_coe_sort s (fun μ => evT θ (ex μ) * cf c μ)]
  calc ∑ μ ∈ s, evT θ (ex μ) * cf c μ
        = ∑ μ ∈ s ∪ c.coeff.support, evT θ (ex μ) * cf c μ := by
          apply Finset.sum_subset Finset.subset_union_left
          intro μ _ hμ
          rw [hz μ hμ, mul_zero]
    _ = ∑ μ ∈ s ∪ c.coeff.support, cf c μ * evT θ (ex μ) :=
          Finset.sum_congr rfl (fun μ _ => mul_comm _ _)
    _ = ∑ μ ∈ c.coeff.support, cf c μ * evT θ (ex μ) := by
          symm
          apply Finset.sum_subset Finset.subset_union_right
          intro μ _ hμ
          rw [show cf c μ = 0 from Finsupp.notMem_support_iff.1 hμ, zero_mul]
    _ = evT θ c := (evT_sum θ c).symm
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.HarmDom
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem mem_lo {n : ℕ} (S : Finset (Fin n)) (hS : ∀ b ∈ S, ∀ c, c ≤ b → c ∈ S) (c : Fin n) :
    c ∈ S ↔ (c : ℕ) < S.card := by
  constructor
  · intro hc
    have hsub : Finset.Iic c ⊆ S := fun b hb => hS c hc b (Finset.mem_Iic.1 hb)
    have h := Finset.card_le_card hsub
    rw [Fin.card_Iic] at h
    omega
  · intro hlt
    by_contra hc
    have hsub : S ⊆ Finset.Iio c := fun b hb => Finset.mem_Iio.2 (by
      by_contra h
      exact hc (hS b hb c (not_lt.1 h)))
    have h := Finset.card_le_card hsub
    rw [Fin.card_Iio] at h
    omega

private theorem mem_hi {n : ℕ} (S : Finset (Fin n)) (hS : ∀ b ∈ S, ∀ c, b ≤ c → c ∈ S) (c : Fin n) :
    c ∈ S ↔ n ≤ (c : ℕ) + S.card := by
  constructor
  · intro hc
    have hsub : Finset.Ici c ⊆ S := fun b hb => hS c hc b (Finset.mem_Ici.mp hb)
    have := Finset.card_le_card hsub
    rw [Fin.card_Ici] at this
    omega
  · intro hle
    by_contra hc
    have hsub : S ⊆ Finset.Ioi c := by
      intro b hb
      rw [Finset.mem_Ioi]
      by_contra hbc
      exact hc (hS b hb c (not_lt.mp hbc))
    have := Finset.card_le_card hsub
    rw [Fin.card_Ioi] at this
    have := c.isLt
    omega

private theorem harmonic_dominant_weight {n : ℕ} (lam : Fin n → ℤ) (hl : Antitone lam) (L : Fin n → ℕ) (hL : IsLev lam L) :
    Dom (muQ lam L) ∧ domC (muQ lam L - rhoV n) + rhoV n = twoL lam := by
  obtain ⟨hmono, hlev⟩ := hL
  obtain ⟨D, hD⟩ : ∃ D : Fin n → ℕ, ∀ a, D a = #{b | L b < L a} := ⟨_, fun _ => rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Fin n → ℕ, ∀ a, U a = #{b | L a < L b} := ⟨_, fun _ => rfl⟩
  have hDlo : ∀ a c, L c < L a ↔ (c : ℕ) < D a := by
    intro a c
    have h := mem_lo (Finset.filter (fun b => L b < L a) Finset.univ)
      (fun b hb c hcb => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        exact lt_of_le_of_lt (hmono hcb) hb) c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    rw [hD]
    exact h
  have hUhi : ∀ a c, L a < L c ↔ n ≤ (c : ℕ) + U a := by
    intro a c
    have h := mem_hi (Finset.filter (fun b => L a < L b) Finset.univ)
      (fun b hb c hcb => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        exact lt_of_lt_of_le hb (hmono hcb)) c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    rw [hU]
    exact h
  have hDa : ∀ a : Fin n, D a ≤ a := fun a => not_lt.mp (fun h => lt_irrefl _ ((hDlo a a).mpr h))
  have hUa : ∀ a : Fin n, (a : ℕ) + U a < n := fun a => not_le.mp (fun h => lt_irrefl _ ((hUhi a a).mpr h))
  let f : Fin n → Fin n := fun a => ⟨D a + (n - 1 - U a) - a, by
    have := hDa a
    have := hUa a
    omega⟩
  have hfv : ∀ a, ((f a : Fin n) : ℕ) = D a + (n - 1 - U a) - a := fun a => rfl
  have hLf : ∀ a, L (f a) = L a := by
    intro a
    rcases lt_trichotomy (L (f a)) (L a) with h | h | h
    · have h1 := (hDlo a (f a)).mp h
      rw [hfv] at h1
      have := hDa a
      have := hUa a
      omega
    · exact h
    · have h1 := (hUhi a (f a)).mp h
      rw [hfv] at h1
      have := hDa a
      have := hUa a
      omega
  have hDf : ∀ a, D (f a) = D a := by
    intro a
    rw [hD, hD, hLf]
  have hUf : ∀ a, U (f a) = U a := by
    intro a
    rw [hU, hU, hLf]
  have hinv : Function.Involutive f := by
    intro a
    apply Fin.ext
    rw [hfv (f a), hDf, hUf, hfv]
    have := hDa a
    have := hUa a
    omega
  refine ⟨fun a b hab => ?_, ?_⟩
  · have hLab := hmono hab.le
    have hlab := hl hab.le
    have hUab : U b ≤ U a := by
      rw [hU, hU]
      refine Finset.card_le_card (fun c hc => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact lt_of_le_of_lt hLab hc
    have hDab : D a ≤ D b := by
      rw [hD, hD]
      refine Finset.card_le_card (fun c hc => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact lt_of_lt_of_le hc hLab
    have e1 : ((lam a - lam b).toNat : ℤ) = lam a - lam b := Int.toNat_of_nonneg (by omega)
    have e2 : (((lam a - lam b).toNat : ℕ) : ℝ) = (lam a : ℝ) - lam b := by
      have h := congrArg (Int.cast : ℤ → ℝ) e1
      push_cast at h
      exact h
    refine ⟨2 * (lam a - lam b).toNat + (U a - U b) + (D b - D a), ?_⟩
    simp only [muQ, rhoU]
    rw [← hU a, ← hU b, ← hD a, ← hD b]
    push_cast [Nat.cast_sub hUab, Nat.cast_sub hDab, e2]
    ring
  · obtain ⟨y, hy⟩ : ∃ y : Wt n, ∀ a, y a = 2 * (lam a : ℝ) + rhoV n a := ⟨_, fun _ => rfl⟩
    have hyA : Antitone y := by
      intro a b hab
      rw [hy, hy]
      have h1 : (lam b : ℝ) ≤ lam a := by exact_mod_cast hl hab
      have h2 : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
      simp only [rhoV]
      linarith
    have hx : ∀ a, (muQ lam L - rhoV n) (f a) = y a := by
      intro a
      have hnat : ((f a : ℕ)) + a + 1 + U a = D a + n := by
        rw [hfv]
        have := hDa a
        have := hUa a
        omega
      have hreal : (((f a : ℕ)) : ℝ) + ((a : ℕ) : ℝ) + 1 + (U a : ℝ) = (D a : ℝ) + n := by
        exact_mod_cast hnat
      simp only [Pi.sub_apply, muQ, rhoU, rhoV]
      rw [← hU (f a), ← hD (f a), hUf, hDf, hlev _ _ (hLf a), hy]
      simp only [rhoV]
      linarith
    let w : Equiv.Perm (Fin n) := Function.Involutive.toPerm f hinv
    have hxy : muQ lam L - rhoV n = y ∘ w := by
      funext a
      have h := hx (f a)
      rw [hinv a] at h
      exact h
    have R := (rearr n).2.1 y
    rw [hxy, R.2.2.2.1 w, R.2.2.1 hyA]
    funext a
    simp only [Pi.add_apply, twoL, hy]
    ring

theorem UpperTheory.RealTr.harmDom :
    ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ μ ∈ harmSet lam, Dom μ ∧ domC (μ - rhoV n) + rhoV n = twoL lam := by
  intro n lam hl μ hμ
  simp only [harmSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hμ
  obtain ⟨lev, hlev, rfl⟩ := hμ
  exact harmonic_dominant_weight lam hl _ hlev
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SpnAdj
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {J : Type} [Fintype J] [DecidableEq J]

private theorem mt_ap (M : Matrix J J ℂ) (x : Ten J V) (j : J) :
    (UpperTheory.RealTr.mt V M x).ofLp j = ∑ k, M j k • x.ofLp k := rfl

private theorem lf_ap (T : Module.End ℂ V) (x : Ten J V) (j : J) :
    (lf J T x).ofLp j = T (x.ofLp j) := rfl

private theorem mt_mul (M N : Matrix J J ℂ) : UpperTheory.RealTr.mt V (M * N) = UpperTheory.RealTr.mt V M * UpperTheory.RealTr.mt V N := by
  refine LinearMap.ext fun x => PiLp.ext fun j => ?_
  simp only [Module.End.mul_apply, mt_ap, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

private theorem mt_one : UpperTheory.RealTr.mt V (1 : Matrix J J ℂ) = 1 := by
  ext x j
  simp [mt_ap, Matrix.one_apply]

private theorem mt_add (M N : Matrix J J ℂ) : UpperTheory.RealTr.mt V (M + N) = UpperTheory.RealTr.mt V M + UpperTheory.RealTr.mt V N := by
  ext x j
  simp [mt_ap, add_smul, Finset.sum_add_distrib]

private theorem mt_smul (r : ℂ) (M : Matrix J J ℂ) : UpperTheory.RealTr.mt V (r • M) = r • UpperTheory.RealTr.mt V M := by
  ext x j
  simp [mt_ap, smul_smul, Finset.smul_sum]

private theorem lf_mt (M : Matrix J J ℂ) (T : Module.End ℂ V) :
    lf J T * UpperTheory.RealTr.mt V M = UpperTheory.RealTr.mt V M * lf J T := by
  ext x j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [mt_ap, lf_ap, map_sum]

private theorem mt_adj (M : Matrix J J ℂ) (x y : Ten J V) :
    ⟪UpperTheory.RealTr.mt V M x, y⟫_ℂ = ⟪x, UpperTheory.RealTr.mt V Mᴴ y⟫_ℂ := by
  simp only [PiLp.inner_apply, mt_ap, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Matrix.conjTranspose_apply, Complex.star_def]
  exact Finset.sum_comm

private theorem lf_adj (T T' : Module.End ℂ V) (h : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T' y⟫_ℂ) (x y : Ten J V) :
    ⟪lf J T x, y⟫_ℂ = ⟪x, lf J T' y⟫_ℂ := by
  simp only [PiLp.inner_apply, lf_ap, h]

private theorem spn_adj {n : ℕ} (c : Fin n → Fin n → Matrix J J ℂ) (hc : ∀ a b, (c a b)ᴴ = c b a) (a b : Fin n) :
    (spn c a b)ᴴ = spn c b a := by
  simp only [spn, Matrix.conjTranspose_sub, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, hc,
    Algebra.algebraMap_eq_smul_one]
  congr 1
  split_ifs with h1 h2 h2
  · simp [Matrix.conjTranspose_smul, Complex.star_def]
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

private theorem real_trace_matrix_sub {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {J : Type} [Fintype J]
    (M N : Matrix J J ℂ) : UpperTheory.RealTr.mt V (M - N) = UpperTheory.RealTr.mt V M - UpperTheory.RealTr.mt V N := by
  refine LinearMap.ext fun x => PiLp.ext fun j => ?_
  simp [mt_ap, sub_smul, Finset.sum_sub_distrib]

private theorem real_trace_matrix_zero {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {J : Type} [Fintype J] :
    UpperTheory.RealTr.mt V (0 : Matrix J J ℂ) = 0 := by
  refine LinearMap.ext fun x => PiLp.ext fun j => ?_
  simp [mt_ap]

private theorem gl_dg {n : ℕ} (K : Fin n → Fin n → Module.End ℂ V) (c : Fin n → Fin n → Matrix J J ℂ)
    (hK : GlRel K) (hs : GlRel (spn c)) : GlRel (dg K c) := by
  intro a b e d
  have h1 : lf J (K a b) * lf J (K e d) - lf J (K e d) * lf J (K a b) =
      lf J ((if b = e then K a d else 0) - if d = a then K e b else 0) := by
    rw [← hK a b e d, map_sub, map_mul, map_mul]
  have h2 : UpperTheory.RealTr.mt V (spn c a b) * UpperTheory.RealTr.mt V (spn c e d) -
      UpperTheory.RealTr.mt V (spn c e d) * UpperTheory.RealTr.mt V (spn c a b) =
      UpperTheory.RealTr.mt V ((if b = e then spn c a d else 0) - if d = a then spn c e b else 0) := by
    rw [← hs a b e d, real_trace_matrix_sub, mt_mul, mt_mul]
  have h3 := lf_mt (V := V) (spn c e d) (K a b)
  have h4 := lf_mt (V := V) (spn c a b) (K e d)
  have key : dg K c a b * dg K c e d - dg K c e d * dg K c a b =
      lf J ((if b = e then K a d else 0) - if d = a then K e b else 0) +
      UpperTheory.RealTr.mt V ((if b = e then spn c a d else 0) - if d = a then spn c e b else 0) := by
    rw [← h1, ← h2]
    simp only [dg, add_mul, mul_add]
    rw [h3, h4]
    abel
  rw [key]
  split_ifs <;> simp only [dg, map_sub, map_zero, real_trace_matrix_sub, real_trace_matrix_zero, sub_zero] <;> abel
end

theorem UpperTheory.RealTr.tenF :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (J : Type) [Fintype J] [DecidableEq J],
      (∃ φ : Matrix J J ℂ →ₐ[ℂ] Module.End ℂ (Ten J V), ∀ M, φ M = mt V M) ∧ (∀ M (T : Module.End ℂ V), lf J T * mt V M = mt V M * lf J T) ∧
      (∀ M (x y : Ten J V), ⟪mt V M x, y⟫_ℂ = ⟪x, mt V Mᴴ y⟫_ℂ) ∧
      (∀ T T' : Module.End ℂ V, (∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T' y⟫_ℂ) → ∀ x y : Ten J V, ⟪lf J T x, y⟫_ℂ = ⟪x, lf J T' y⟫_ℂ) ∧
      ∀ (K : Fin n → Fin n → Module.End ℂ V) (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n), UF K → ClifMod c η → UF (dg K c) := by
  intro n V _ _ J _ _
  refine ⟨⟨AlgHom.ofLinearMap ⟨⟨UpperTheory.RealTr.mt V, fun M N => mt_add M N⟩, fun r M => mt_smul r M⟩
      mt_one (fun M N => mt_mul M N), fun M => rfl⟩,
    fun M T => lf_mt M T, fun M x y => mt_adj M x y, fun T T' h x y => lf_adj T T' h x y, ?_⟩
  intro K c η hK hc
  refine ⟨gl_dg K c hK.gl (spnRel n _ c hc.rel).1, ?_⟩
  intro a b x y
  simp only [dg, LinearMap.add_apply, inner_add_left, inner_add_right]
  rw [lf_adj _ _ (hK.unit a b), mt_adj, spn_adj c hc.adj]
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.TrOnBot
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem trOn_bot' {V : Type} [AddCommGroup V] [Module ℂ V] (L : V →ₗ[ℂ] V) :
    trOn (⊥ : Submodule ℂ V) L = 0 := by
  unfold trOn
  split_ifs with h
  · have : Subsingleton (⊥ : Submodule ℂ V) := inferInstance
    have h0 : L.restrict h = 0 := Subsingleton.elim _ _
    rw [h0, map_zero]
  · rfl

private theorem cf_sum {n : ℕ} (s : Finset (Wt n)) (g : Wt n → ℂ) (μ : Wt n) :
    cf (∑ x ∈ s, g x • ex x) μ = if μ ∈ s then g μ else 0 := by
  classical
  simp [cf, ex, AddMonoidAlgebra.coeff, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem UpperTheory.RealTr.chEx :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∀ B, ∃ c, IsCh F S B c := by
  intro n V _ _ F hF S hS hSt B
  obtain ⟨s, hs, -, -⟩ := wtDec n V F hF S hS hSt
  refine ⟨∑ μ ∈ s, trOn (wsp F μ ⊓ S) B • ex μ, fun μ => ?_⟩
  rw [cf_sum]
  split_ifs with h
  · rfl
  · rw [hs μ h, trOn_bot']
end
end

