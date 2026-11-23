module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0008

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

universe u w

theorem exists_pos_of_eventually_lower {d : ℕ} {A : ℤ} (hA : 0 < A) {C : ℝ} {f : ℕ → ℝ}
    (h : ∀ᶠ n : ℕ in atTop,
      (A : ℝ) * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤ f n)
    (D : ℕ) (hD : 0 < D) : ∃ n₁ : ℕ, 0 < n₁ ∧ 0 < f (D * n₁) := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp h
  obtain ⟨K, hK⟩ := exists_nat_gt (C * ((d + 1).factorial : ℝ) / A)
  refine ⟨n₀ + K + 1, by omega, ?_⟩
  have hle : n₀ + K + 1 ≤ D * (n₀ + K + 1) := Nat.le_mul_of_pos_left _ hD
  refine lt_of_lt_of_le ?_ (hn₀ _ (le_trans (by omega) hle))
  have hnK : (K : ℝ) < ((D * (n₀ + K + 1) : ℕ) : ℝ) := by
    have : K < D * (n₀ + K + 1) := lt_of_lt_of_le (by omega) hle
    exact_mod_cast this
  generalize ((D * (n₀ + K + 1) : ℕ) : ℝ) = n at hnK ⊢
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  have hF : (0 : ℝ) < ((d + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (Nat.cast_nonneg K) hnK
  have h1 : C * ((d + 1).factorial : ℝ) < A * n := by
    have := lt_trans hK hnK
    rwa [div_lt_iff₀ hA', mul_comm n] at this
  have h2 : C < A * n / ((d + 1).factorial : ℝ) := by rw [lt_div_iff₀ hF]; exact h1
  have h3 : (A : ℝ) * n ^ (d + 1) / ((d + 1).factorial : ℝ) - C * n ^ d =
      n ^ d * (A * n / ((d + 1).factorial : ℝ) - C) := by ring
  rw [h3]
  exact mul_pos (pow_pos hnpos d) (by linarith)

theorem sectionExists_of_gap (hcount : SectionCount.Statement.{u, w})
    (hlead : LeadingCoeffPos.Statement.{u, w}) {k : Type u} [Field k] {Ω : Type w} [Field Ω]
    [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω} {d : ℕ} {M : LineBundle k x} {t s' : ℚ}
    (hZ : IsSubvar x (primeOf (S := k) x) (d + 1)) (hM : Nef M.toSubSystem) (hs' : 0 < s')
    {Q : ℕ} {mQ : ℤ} (hQ : 0 < Q) (hmQ : (mQ : ℚ) = Q * t)
    (hva : IsVeryAmple (twistMul M.toSubSystem Q mQ))
    (hgap : 1 < (Q : ℚ) * (t / (d + 1) - s')) :
    ∃ (p : ℕ) (m c₁ : ℤ), 1 ≤ p ∧ (m : ℚ) = p * (t - s') ∧ 1 ≤ c₁ ∧
      ∃ σ ∈ (twistMul M.toSubSystem p (m - c₁)).secs, σ ≠ 0 := by
  obtain ⟨Nb, hNb⟩ := exists_lineBundle_twistMul M Q mQ
  have hvaN : IsVeryAmple Nb.toSubSystem := hNb ▸ hva

  obtain ⟨b, hb⟩ : ∃ b : ℕ, b = ⌊(Q : ℚ) * s'⌋₊ + 1 := ⟨_, rfl⟩
  have hQs'0 : 0 ≤ (Q : ℚ) * s' := by positivity
  have hb_gt : (Q : ℚ) * s' < b := by rw [hb]; push_cast; exact Nat.lt_floor_add_one _
  have hb_le : (b : ℚ) ≤ Q * s' + 1 := by rw [hb]; push_cast; linarith [Nat.floor_le hQs'0]
  have hd0 : (d : ℚ) + 1 ≠ 0 := by positivity
  have hd : (0 : ℚ) < d + 1 := by positivity
  have hbT : (b : ℚ) < Q * (t / (d + 1)) := by
    have := hgap
    rw [mul_sub] at this
    linarith
  have hbm : ((d + 1 : ℕ) : ℤ) * b < mQ := by
    have h1 : ((d : ℚ) + 1) * b < (d + 1) * (Q * (t / (d + 1))) := mul_lt_mul_of_pos_left hbT hd
    have h2 : ((d : ℚ) + 1) * (Q * (t / (d + 1))) = Q * t := by field_simp
    have h3 : ((((d + 1 : ℕ) : ℤ) * b : ℤ) : ℚ) < (mQ : ℚ) := by
      push_cast
      rw [hmQ]
      linarith
    exact_mod_cast h3
  have hb1 : 1 ≤ b := by omega
  obtain ⟨C, hC⟩ := hcount k Ω N x d Nb b hZ hvaN hb1
  have hcoef := hlead k Ω N x d M Nb Q mQ b hZ hM hNb hvaN hbm

  have hden := Rat.mul_den_eq_num ((Q : ℚ) * s')
  have hD1 : 0 < ((Q : ℚ) * s').den := Rat.den_pos _
  generalize ((Q : ℚ) * s').den = D at hden hD1
  generalize ((Q : ℚ) * s').num = E at hden
  obtain ⟨n₁, hn₁, hpos⟩ := exists_pos_of_eventually_lower hcoef hC D hD1
  have hne : (twistMul Nb.toSubSystem (D * n₁) (-(((D * n₁ : ℕ) : ℤ) * b))).secs ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hpos
    simp at hpos
  obtain ⟨σ, hσ, hσne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [hNb, twistMul_twistMul] at hσ
  refine ⟨D * n₁ * Q, ((D * n₁ : ℕ) : ℤ) * mQ - n₁ * E, ((D * n₁ : ℕ) : ℤ) * b - n₁ * E,
    Nat.mul_pos (Nat.mul_pos hD1 hn₁) hQ, ?_, ?_, σ, ?_, hσne⟩
  · push_cast
    rw [hmQ, ← hden]
    ring
  · have hDn : (0 : ℚ) < (D : ℚ) * n₁ := by positivity
    have hpos' : (0 : ℚ) < ((((D * n₁ : ℕ) : ℤ) * b - n₁ * E : ℤ) : ℚ) := by
      push_cast
      rw [← hden]
      have key : (D : ℚ) * n₁ * (b - Q * s') = D * n₁ * b - n₁ * (Q * s' * D) := by ring
      have := mul_pos hDn (sub_pos.mpr hb_gt)
      linarith
    have : (0 : ℤ) < ((D * n₁ : ℕ) : ℤ) * b - n₁ * E := by exact_mod_cast hpos'
    omega
  · have hm : ((D * n₁ : ℕ) : ℤ) * mQ - n₁ * E - (((D * n₁ : ℕ) : ℤ) * b - n₁ * E) =
        ((D * n₁ : ℕ) : ℤ) * mQ + -(((D * n₁ : ℕ) : ℤ) * b) := by ring
    rw [hm]
    exact hσ

theorem SectionExists.proof (hcount : SectionCount.Statement.{u, w})
    (hpow : VeryAmplePow.Statement.{u, w}) (hlead : LeadingCoeffPos.Statement.{u, w}) :
    SectionExists.Statement.{u, w} := by
  intro k _ Ω _ _ N x d M t s' hZ hM hs' hst hq
  obtain ⟨q, m, hq1, hm, hva⟩ := hq
  have hδ : 0 < t / (d + 1) - s' := by linarith
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hq1
  have hqδ := mul_pos hqpos hδ
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt (1 / ((q : ℚ) * (t / (d + 1) - s')))
  rw [div_lt_iff₀ hqδ] at hj₀
  have hgap : 1 < (((j₀ + 1) * q : ℕ) : ℚ) * (t / (d + 1) - s') := by
    push_cast
    have : ((j₀ : ℚ) + 1) * q * (t / (d + 1) - s') =
        j₀ * (q * (t / (d + 1) - s')) + q * (t / (d + 1) - s') := by ring
    rw [this]
    linarith
  obtain ⟨Nb0, hNb0⟩ := exists_lineBundle_twistMul M q m
  have hvaQ : IsVeryAmple (twistMul M.toSubSystem ((j₀ + 1) * q) (((j₀ + 1 : ℕ) : ℤ) * m)) := by
    have := hpow k Ω N x Nb0 (j₀ + 1) (by rw [hNb0]; exact hva) (by omega)
    rw [hNb0, pow_twistMul] at this
    exact this
  exact sectionExists_of_gap hcount hlead hZ hM hs' (Nat.mul_pos (Nat.succ_pos _) hq1)
    (by push_cast; rw [hm]; ring) hvaQ hgap

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistTilde
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace TwistTildeProof

theorem smul_mem_of_mem_span {R A M : Type*} [CommRing R] [Ring A] [AddCommGroup M] [Module R A]
    [Module A M] [Module R M] [IsScalarTower R A M] [SMulCommClass A R M] {s : Set A} {t : Set M}
    {T : Submodule R M} (h : ∀ a ∈ s, ∀ b ∈ t, a • b ∈ T) {q : A} (hq : q ∈ Submodule.span R s)
    {m : M} (hm : m ∈ Submodule.span R t) : q • m ∈ T := by
  refine Submodule.span_induction (p := fun q _ => q • m ∈ T) ?_ ?_ ?_ ?_ hq
  · intro a ha
    refine Submodule.span_induction (p := fun m _ => a • m ∈ T) ?_ ?_ ?_ ?_ hm
    · exact fun b hb => h a ha b hb
    · rw [smul_zero]; exact T.zero_mem
    · intro b c _ _ hb hc; rw [smul_add]; exact T.add_mem hb hc
    · intro r b _ hb; rw [smul_comm]; exact T.smul_mem r hb
  · rw [zero_smul]; exact T.zero_mem
  · intro a b _ _ ha hb; rw [add_smul]; exact T.add_mem ha hb
  · intro r a _ ha; rw [smul_assoc]; exact T.smul_mem r ha

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]

def prodSet (M : FinGradedSub (S := S) (x := x) E) (Q : FinGradedSub (S := S) (x := x) Ω) (c : ℤ) :
    Set E :=
  {z | ∃ (a b : ℤ) (q : Ω) (m : E), q ∈ Q.piece a ∧ m ∈ M.piece b ∧ a + b = c ∧ z = q • m}

def prod (M : FinGradedSub (S := S) (x := x) E) (Q : FinGradedSub (S := S) (x := x) Ω) :
    FinGradedSub (S := S) (x := x) E where
  piece c := Submodule.span S (prodSet M Q c)
  smul_mem d c f m hf hm := by
    refine Submodule.span_induction (p := fun m _ => aeval x f • m ∈ Submodule.span S
      (prodSet M Q (c + d))) ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨a, b, q, m, hq, hm, hab, rfl⟩
      refine Submodule.subset_span ⟨a, b + d, q, aeval x f • m, hq, M.smul_mem d b f m hf hm,
        by omega, ?_⟩
      rw [smul_smul, smul_smul, mul_comm]
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_mem _ r ha
  fg := by
    obtain ⟨n, deg, gen, hgen, hspan⟩ := M.fg
    obtain ⟨n', deg', gen', hgen', hspan'⟩ := Q.fg
    let e := (finProdFinEquiv : Fin n' × Fin n ≃ Fin (n' * n))
    refine ⟨n' * n, fun k => deg' (e.symm k).1 + deg (e.symm k).2,
      fun k => gen' (e.symm k).1 • gen (e.symm k).2, fun k => Submodule.subset_span
        ⟨_, _, _, _, hgen' _, hgen _, rfl, rfl⟩, fun c => Submodule.span_le.mpr ?_⟩
    rintro _ ⟨a, b, q, m, hq, hm, hab, rfl⟩
    refine smul_mem_of_mem_span ?_ (hspan' a hq) (hspan b hm)
    rintro _ ⟨l, f', e', hf', he', rfl⟩ _ ⟨j, f, e'', hf, he'', rfl⟩
    refine Submodule.subset_span ⟨e (l, j), f' * f, e' + e'', hf'.mul hf, ?_, ?_⟩
    · simp only [Equiv.symm_apply_apply]; push_cast; omega
    · simp only [Equiv.symm_apply_apply, smul_eq_mul, map_mul, smul_smul]
      congr 1; ring

theorem twist_eq (M : FinGradedSub (S := S) (x := x) E) (Q : FinGradedSub (S := S) (x := x) Ω)
    (I : Chart x) : ((M.tildeSys 0).twist (Q.tildeSys 0)).sub I = (prod M Q).tilde 0 I := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    change q ∈ Q.tilde 0 I at hq
    change y ∈ M.tilde 0 I at hy
    refine smul_mem_of_mem_span ?_ hq hy
    rintro _ ⟨q, s₁, a₁, e₁, hs₁, hse₁, hq, ha₁, rfl⟩ _ ⟨m, s₂, a₂, e₂, hs₂, hse₂, hm, ha₂, rfl⟩
    refine Submodule.subset_span ⟨q • m, s₁ * s₂, a₁ + a₂, e₁ + e₂, mul_mem hs₁ hs₂, hse₁.mul hse₂,
      Submodule.subset_span ⟨a₁, a₂, q, m, hq, hm, rfl, rfl⟩, by push_cast; omega, ?_⟩
    simp only [smul_eq_mul, smul_smul, map_mul, mul_inv]
    congr 1; ring
  · obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨p, s, a, e, hs, hse, hp, hae, rfl⟩
    have hs0 := eval_ne_zero_of_mem_monos I hs
    refine Submodule.span_induction (p := fun p _ => (aeval x s)⁻¹ • p ∈
      ((M.tildeSys 0).twist (Q.tildeSys 0)).sub I) ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨a', b', q, m, hq, hm, hab, rfl⟩
      set k := a'.toNat
      set j := (-a').toNat
      have hkj : (k : ℤ) - j = a' := Int.toNat_sub_toNat_neg a'
      have hq' : (aeval x (X i ^ k : Poly S N))⁻¹ • (aeval x (X i ^ j : Poly S N) • q) ∈
          Q.tilde 0 I := by
        have h := Q.smul_mem j a' _ q (isHomogeneous_X_pow i j) hq
        rw [show a' + (j : ℤ) = k by omega] at h
        exact Submodule.subset_span ⟨_, X i ^ k, k, k, pow_mem (X_mem_monos hi) k,
          isHomogeneous_X_pow i k, h, by simp, rfl⟩
      have hm' : (aeval x (s * X i ^ j))⁻¹ • (aeval x (X i ^ k : Poly S N) • m) ∈ M.tilde 0 I := by
        have h := M.smul_mem k b' _ m (isHomogeneous_X_pow i k) hm
        exact Submodule.subset_span ⟨_, s * X i ^ j, b' + k, e + j,
          mul_mem hs (pow_mem (X_mem_monos hi) j), hse.mul (isHomogeneous_X_pow i j), h,
          by push_cast; omega, rfl⟩
      have heq : (aeval x s)⁻¹ • (q • m) = ((aeval x (X i ^ k : Poly S N))⁻¹ •
          (aeval x (X i ^ j : Poly S N) • q)) • ((aeval x (s * X i ^ j))⁻¹ •
          (aeval x (X i ^ k : Poly S N) • m)) := by
        simp only [smul_eq_mul, smul_smul, map_mul, map_pow, aeval_X]
        congr 1
        field_simp
      rw [heq]
      exact Submodule.subset_span ⟨_, hq', _, hm', rfl⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_of_tower_mem _ r ha

end TwistTildeProof


open TwistTildeProof in
theorem TwistTilde.proof : TwistTilde.Statement := by
  intro S _ Ω _ _ N x E _ _ _ _ M Q
  exact ⟨prod M Q, fun c => rfl, twist_eq M Q⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistVanish
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem TwistVanish.proof (hE : Extension.Statement.{u, w, w}) (hV : SerreVanish.Statement.{u, w})
    (hT : TwistSplit.Statement.{u, w}) : TwistVanish.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x G B r η hη hspan
  obtain ⟨M₀, -, hM₀⟩ := hE S Ω N x Ω G.toSubFamily G.fg
  obtain ⟨M, _, _, _, _, 𝓜, hfin, hsplit⟩ :=
    hT S Ω N x M₀ G.toSubSystem B.toSubSystem r η hM₀ hη hspan
  obtain ⟨c₀, hc₀⟩ := hV (MvPolynomial (Fin (r + 1)) S) N M 𝓜 hfin
  refine ⟨c₀, fun b c hc => ?_⟩
  obtain ⟨ι, π, hπ⟩ := hsplit b c 1
  have := hc₀ 1 le_rfl c hc
  exact ⟨fun z z' => by rw [← hπ z, ← hπ z', Subsingleton.elim (ι z) (ι z')]⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistVanishAll
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

theorem TwistVanishAll.proof (hE : Extension.Statement.{u, w, w}) (hV : SerreVanish.Statement.{u, w})
    (hT : TwistSplit.Statement.{u, w}) : TwistVanishAll.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x G B r η hη hspan
  obtain ⟨M₀, -, hM₀⟩ := hE S Ω N x Ω G.toSubFamily G.fg
  obtain ⟨M, _, _, _, _, 𝓜, hfin, hsplit⟩ :=
    hT S Ω N x M₀ G.toSubSystem B.toSubSystem r η hM₀ hη hspan
  obtain ⟨c₀, hc₀⟩ := hV (MvPolynomial (Fin (r + 1)) S) N M 𝓜 hfin
  refine ⟨c₀, fun i b c hi hc => ?_⟩
  obtain ⟨ι, π, hπ⟩ := hsplit b c i
  have := hc₀ i hi c hc
  exact ⟨fun z z' => by rw [← hπ z, ← hπ z', Subsingleton.elim (ι z) (ι z')]⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w

theorem VeryAmpleDegree.proof (hDim : VeryAmpleDim.Statement.{u, w})
    (hSecs : VeryAmpleSecs.Statement.{u, w}) (hHilb : VeryAmpleHilbert.Statement.{u, w}) :
    VeryAmpleDegree.Statement.{u, w} := by
  intro k _ Ω _ _ N x e Nb r h hZ hV
  obtain ⟨-, P, -, hP, hPn⟩ := hHilb k Ω N x e Nb hZ ⟨r, h, hV⟩
  obtain ⟨-, Q, -, hQ, hQn⟩ := hHilb k Ω r h e (twistBundle k h 1) (hDim k Ω N x e Nb r h hZ hV)
    isVeryAmple_twistSys_one
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hPn.and hQn)
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => ((m + n₀ : ℕ) : ℚ)) ?_ ?_
    · intro a b hab
      have : a + n₀ = b + n₀ := by simpa using hab
      omega
    · intro m
      obtain ⟨h1, h2⟩ := hn₀ (m + n₀) (Nat.le_add_left n₀ m)
      change P.eval _ = Q.eval _
      rw [← h1, ← h2, hSecs k Ω N x Nb r h hV (m + n₀)]
      rfl
  have hnum : (interNum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) : ℚ) =
      (interNum (primeOf (S := k) h) (fun _ : Fin e => twistSys k h 1) : ℚ) := by
    rw [← hP, hPQ, hQ]
    rfl
  exact_mod_cast hnum

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.QuotSectionsFiniteSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def QuotSectionsFinite.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Q : LineBundle k x) (J : Ideal (Poly k N)),
    Module.Finite k (SubSystem.quotH Q.toSubSystem (Q.toSubSystem.twist (idealSys x J)) 0)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.QuotTransSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def QuotTrans.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F₁ F₂ F₃ : SubSystem S x E), (∀ I, F₃.sub I ≤ F₂.sub I) → (∀ I, F₂.sub I ≤ F₁.sub I) →
    Subsingleton (SubSystem.quotH F₂ F₃ 1) → Subsingleton (SubSystem.quotH F₁ F₂ 1) →
    Subsingleton (SubSystem.quotH F₁ F₃ 1)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.QuotientH0FiniteHypothesesLine
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def QuotientH0Finite.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F G : SubSystem S x E), (∀ I, G.sub I ≤ F.sub I) →
    Module.Finite S (F.H 0) → Module.Finite S (G.H 1) → Module.Finite S (SubSystem.quotH F G 0)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropFiltFiniteSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def SectionCount.Drop.Filt.Finite.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (Q : LineBundle S x) (pp : Ideal (Poly S N)) (c : ℤ), pp.IsPrime →
    (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) → primeOf (S := S) x ≤ pp →
    Module.Finite S (SubSystem.quotH (Q.twist (twistSys S x c))
      ((Q.twist (twistSys S x c)).twist (idealSys x pp)) 0)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

