module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
public import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle0003
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0055

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.ThetaMove

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H

section Loc

variable {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module (𝓞 E) W]

def Dom (S : Finset (HeightOneSpectrum (𝓞 E))) (M₁ M₂ : Submodule (𝓞 E) W) : Prop :=
  (∀ P ∈ S, localization₂ P.asIdeal M₂ ≤ localization₂ P.asIdeal M₁) ∧ ∀ Q, Q ∉ S → localization₂ Q.asIdeal M₁ ≤ localization₂ Q.asIdeal M₂

def Full (M : Submodule (𝓞 E) W) : Prop := ∀ x : W, ∃ n : ℕ, 0 < n ∧ (n : 𝓞 E) • x ∈ M

theorem Dom.refl (S : Finset (HeightOneSpectrum (𝓞 E))) (M : Submodule (𝓞 E) W) : Dom S M M :=
  ⟨fun _ _ => le_rfl, fun _ _ => le_rfl⟩

theorem Dom.trans {S : Finset (HeightOneSpectrum (𝓞 E))} {M₁ M₂ M₃ : Submodule (𝓞 E) W} (h : Dom S M₁ M₂) (h' : Dom S M₂ M₃) :
    Dom S M₁ M₃ :=
  ⟨fun P hP => (h'.1 P hP).trans (h.1 P hP), fun Q hQ => (h.2 Q hQ).trans (h'.2 Q hQ)⟩

theorem Full.inf {M M' : Submodule (𝓞 E) W} (h : Full M) (h' : Full M') : Full (M ⊓ M') := by
  intro x
  obtain ⟨n, hn, hx⟩ := h x
  obtain ⟨m, hm, hy⟩ := h' x
  refine ⟨n * m, Nat.mul_pos hn hm, ?_, ?_⟩
  · rw [Nat.cast_mul, mul_comm, mul_smul]; exact M.smul_mem _ hx
  · rw [Nat.cast_mul, mul_smul]; exact M'.smul_mem _ hy

theorem localization_mono (Q : HeightOneSpectrum (𝓞 E)) {M M' : Submodule (𝓞 E) W} (h : M ≤ M') :
    localization₂ Q.asIdeal M ≤ localization₂ Q.asIdeal M' := fun _ ⟨s, hs, hx⟩ => ⟨s, hs, h hx⟩

theorem localization_localization₂ (Q : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) W) :
    localization₂ Q.asIdeal (localization₂ Q.asIdeal M) = localization₂ Q.asIdeal M := by
  refine le_antisymm ?_ fun x hx => ⟨1, Q.asIdeal.primeCompl.one_mem, by rwa [one_smul]⟩
  rintro x ⟨s, hs, t, ht, hx⟩
  exact ⟨t * s, Q.asIdeal.primeCompl.mul_mem ht hs, by rwa [mul_smul]⟩

theorem mem_of_locP {M : Submodule (𝓞 E) W} {x : W} (h : ∀ Q : HeightOneSpectrum (𝓞 E), x ∈ localization₂ Q.asIdeal M) : x ∈ M := by
  by_contra hx
  have hne : M.comap (LinearMap.toSpanSingleton (𝓞 E) W x) ≠ ⊤ := fun e => hx (by
    have : (1 : 𝓞 E) ∈ M.comap (LinearMap.toSpanSingleton (𝓞 E) W x) := e ▸ Submodule.mem_top
    simpa using this)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩
  exact hs (hle (by simpa using hsx))

theorem exists_idem (S : Finset (HeightOneSpectrum (𝓞 E))) {a : 𝓞 E} (ha : a ≠ 0) :
    ∃ r : 𝓞 E, (∀ P ∈ S, ∃ s, s ∉ P.asIdeal ∧ a ∣ s * (r - 1)) ∧ ∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ S → ∃ s, s ∉ Q.asIdeal ∧ a ∣ s * r := by
  classical

  have key : ∀ I : Ideal (𝓞 E), I ≠ ⊥ → ∃ J₁ J₂ : Ideal (𝓞 E), I = J₁ * J₂ ∧ (∀ P ∈ S, ¬ J₂ ≤ P.asIdeal) ∧
      ∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ S → ¬ J₁ ≤ Q.asIdeal := by
    intro I
    induction I using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => intro h; exact absurd rfl h
    | h₂ u hu =>
      intro _
      rw [Ideal.isUnit_iff] at hu
      exact ⟨⊤, ⊤, by simp [hu], fun P _ h => P.isPrime.ne_top (top_le_iff.1 h), fun P _ h => P.isPrime.ne_top (top_le_iff.1 h)⟩
    | h₃ I p hI hp ih =>
      intro _
      obtain ⟨J₁, J₂, rfl, h1, h2⟩ := ih hI
      let P₀ : HeightOneSpectrum (𝓞 E) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
      have hmax : ∀ Q : HeightOneSpectrum (𝓞 E), p ≤ Q.asIdeal → Q = P₀ := fun Q h =>
        HeightOneSpectrum.ext (P₀.isMaximal.eq_of_le Q.isPrime.ne_top h).symm
      by_cases hS : P₀ ∈ S
      · refine ⟨p * J₁, J₂, by ring, h1, fun Q hQ h => ?_⟩
        rcases (Q.isPrime.mul_le).1 h with h | h
        · exact hQ (hmax Q h ▸ hS)
        · exact h2 Q hQ h
      · refine ⟨J₁, p * J₂, by ring, fun Q hQ h => ?_, h2⟩
        rcases (Q.isPrime.mul_le).1 h with h | h
        · exact hS (hmax Q h ▸ hQ)
        · exact h1 Q hQ h
  obtain ⟨J₁, J₂, hJ, h1, h2⟩ := key (Ideal.span {a}) (by simpa using ha)
  have hsup : J₁ ⊔ J₂ = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let Q : HeightOneSpectrum (𝓞 E) :=
      ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩
    by_cases hQ : Q ∈ S
    · exact h1 Q hQ (le_sup_right.trans hle)
    · exact h2 Q hQ (le_sup_left.trans hle)
  obtain ⟨u, hu, r, hr, hur⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ J₁ ⊔ J₂)
  refine ⟨r, fun P hP => ?_, fun Q hQ => ?_⟩
  · obtain ⟨s, hs, hs'⟩ := SetLike.not_le_iff_exists.1 (h1 P hP)
    refine ⟨s, hs', Ideal.mem_span_singleton.1 ?_⟩
    rw [hJ, show s * (r - 1) = (-u) * s by rw [← hur]; ring]
    exact Ideal.mul_mem_mul (J₁.neg_mem hu) hs
  · obtain ⟨s, hs, hs'⟩ := SetLike.not_le_iff_exists.1 (h2 Q hQ)
    refine ⟨s, hs', Ideal.mem_span_singleton.1 ?_⟩
    rw [hJ]
    exact Ideal.mul_mem_mul hs hr

theorem Full.approx {M : Submodule (𝓞 E) W} (hM : Full M) (S : Finset (HeightOneSpectrum (𝓞 E))) (x : W) :
    ∃ t : W, (∀ P ∈ S, t - x ∈ localization₂ P.asIdeal M) ∧ ∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ S → t ∈ localization₂ Q.asIdeal M := by
  obtain ⟨n, hn, hx⟩ := hM x
  obtain ⟨r, h1, h2⟩ := exists_idem S (a := (n : 𝓞 E)) (by exact_mod_cast hn.ne')
  refine ⟨r • x, fun P hP => ?_, fun Q hQ => ?_⟩
  · obtain ⟨s, hs, k, hk⟩ := h1 P hP
    refine ⟨s, hs, ?_⟩
    rw [show s • (r • x - x) = (s * (r - 1)) • x by rw [mul_smul, sub_smul, one_smul], hk, mul_comm, mul_smul]
    exact M.smul_mem _ hx
  · obtain ⟨s, hs, k, hk⟩ := h2 Q hQ
    refine ⟨s, hs, ?_⟩
    rw [← mul_smul, hk, mul_comm, mul_smul]
    exact M.smul_mem _ hx

theorem mem_localization_of_mem (Q : HeightOneSpectrum (𝓞 E)) {M : Submodule (𝓞 E) W} {x : W} (hx : x ∈ M) : x ∈ localization₂ Q.asIdeal M :=
  ⟨1, Q.asIdeal.primeCompl.one_mem, by rwa [one_smul]⟩

theorem localization_inf (Q : HeightOneSpectrum (𝓞 E)) (M M' : Submodule (𝓞 E) W) :
    localization₂ Q.asIdeal (M ⊓ M') = localization₂ Q.asIdeal M ⊓ localization₂ Q.asIdeal M' := by
  refine le_antisymm (le_inf (localization_mono Q inf_le_left) (localization_mono Q inf_le_right)) ?_
  rintro x ⟨⟨s, hs, hx⟩, t, ht, hy⟩
  exact ⟨s * t, Q.asIdeal.primeCompl.mul_mem hs ht, by rw [mul_comm, mul_smul]; exact M.smul_mem _ hx,
    by rw [mul_smul]; exact M'.smul_mem _ hy⟩

theorem mem_localization_twist [Module E W] [IsScalarTower (𝓞 E) E W] (M : Submodule (𝓞 E) W) {c : ℕ} (hc : 0 < c)
    {e : HeightOneSpectrum (𝓞 E) → ℤ} (he : ∀ Q, -1 ≤ e Q ∧ e Q ≤ 1) (Q : HeightOneSpectrum (𝓞 E)) (x : W) :
    x ∈ localization₂ Q.asIdeal (twist₂ M c e) ↔ ((c : E) ^ e Q)⁻¹ • x ∈ localization₂ Q.asIdeal M := by
  have hmem : ∀ y : W, y ∈ twist₂ M c e ↔ ∀ Q' : HeightOneSpectrum (𝓞 E), ((c : E) ^ e Q')⁻¹ • y ∈ localization₂ Q'.asIdeal M := fun y => by
    simp [twist₂, Submodule.mem_iInf]
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  constructor
  · rintro ⟨s, hs, hx⟩
    rw [← localization_localization₂]
    exact ⟨s, hs, by rw [smul_comm]; exact (hmem _).1 hx Q⟩
  · rintro ⟨s, hs, hx⟩
    obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot
    obtain ⟨r, h1, h2⟩ := exists_idem {Q} (a := (c : 𝓞 E) ^ 2 * p)
      (mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hc.ne')) hp0)
    obtain ⟨t, ht, k, hk⟩ := h1 Q (Finset.mem_singleton_self Q)
    have hr : r ∉ Q.asIdeal := fun hr => by
      have h3 : t * (r - 1) ∈ Q.asIdeal := hk ▸ Q.asIdeal.mul_mem_right _ (Q.asIdeal.mul_mem_left _ hp)
      have h4 := (Q.isPrime.mem_or_mem h3).resolve_left ht
      exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using Q.asIdeal.sub_mem hr h4))
    refine ⟨r * s, Q.asIdeal.primeCompl.mul_mem hr hs, (hmem _).2 fun Q' => ?_⟩
    by_cases hQ : Q' = Q
    · subst hQ
      refine mem_localization_of_mem _ ?_
      rw [smul_comm, mul_smul]
      exact M.smul_mem _ hx
    · obtain ⟨t', ht', k', hk'⟩ := h2 Q' (by simpa using hQ)
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ 2 - e Q' + e Q by have := he Q; have := he Q'; omega)
      refine ⟨t', ht', ?_⟩
      have h5 : t' • ((c : E) ^ e Q')⁻¹ • (r * s) • x = ((c : 𝓞 E) ^ m * (p * k')) • s • ((c : E) ^ e Q)⁻¹ • x := by
        have h6 := congrArg (algebraMap (𝓞 E) E) hk'
        have h7 : (c : E) ^ m = (c : E) ^ 2 * ((c : E) ^ e Q')⁻¹ * (c : E) ^ e Q := by
          rw [← zpow_natCast, ← hm, zpow_add₀ hcE, zpow_sub₀ hcE, div_eq_mul_inv, zpow_ofNat]
        simp only [map_mul, map_pow, map_natCast] at h6
        simp only [← algebraMap_smul E (_ : 𝓞 E), smul_smul, map_mul, map_pow, map_natCast]
        congr 1
        rw [h7]
        have := zpow_ne_zero (e Q) hcE
        have := zpow_ne_zero (e Q') hcE
        field_simp
        linear_combination (algebraMap (𝓞 E) E s) * h6
      rw [h5]
      exact M.smul_mem _ hx

theorem expS_bound [StarRing E] (S : Finset (HeightOneSpectrum (𝓞 E))) (Q : HeightOneSpectrum (𝓞 E)) :
    -1 ≤ expS S Q ∧ expS S Q ≤ 1 := by
  unfold expS
  split_ifs <;> omega

def cosSum {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (ι : W →+ V) (As L : Submodule (𝓞 E) W)
    (θ : V → ℂ) (Ξ : W → ℂ) (z : V) : ℂ :=
  latSum As L fun t => Ξ t * (α (ι t) * opU H (-(ι t)) θ z)

def volExp {a b : ℕ} (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) : ℤ :=
  (b : ℤ) * ordDet P N - (a : ℤ) * ordDet P N'

end Loc

section Ambient

variable {X : Fields} (A : Amb X) {a b : ℕ}

abbrev lam (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : AddSubgroup (VCx X.Tau a b) :=
  LamC (X.embC A.σ₀) A.δ A.AA N N'

def vac (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : VCx X.Tau a b → ℂ :=
  fun z => (A.chiF a b N N')⁻¹ * A.e a b N N' z


variable (a b) in
def Moves : Prop :=
  A.δ ≠ 0 ∧ Nonempty X.Tau ∧ A.AA.FG ∧ A.AA ≠ ⊥ ∧
  (∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
    A.chiF a b N N' ≠ 0 ∧ vac A N N' ∈ Th (Formalism.L2.Ker.HV A.sc) (alV A.d A.sc) (lam A N N') ∧
      LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N') ∧
  (∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' N'' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' → IsSdLat N'' →
    vac A N N'' = inter (Formalism.L2.Ker.HV A.sc) (alV A.d A.sc) (lam A N N') (lam A N N'') (vac A N N')) ∧
  ∀ (N N₁ : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N₁ → IsSdLat N' →
    vac A N₁ N' = inter (Formalism.L2.Ker.HV A.sc) (alV A.d A.sc) (lam A N N') (lam A N₁ N') (vac A N N')

end Ambient

theorem isHerm_HV {ι : Type} [Fintype ι] {a b : ℕ} (sc : ℝ) : IsHerm (Formalism.L2.Ker.HV (ι := ι) (a := a) (b := b) sc) := by
  intro x y
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Formalism.L2.Ker.HV, map_sum, mul_comm]

theorem embH_injective {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] [Nonempty ι] {a b : ℕ}
    (emb : ι → E →+* ℂ) {δ : ℂ} (hδ : δ ≠ 0) : Function.Injective (embH (a := a) (b := b) emb δ) := by
  intro x y h
  obtain ⟨τ⟩ := ‹Nonempty ι›
  refine LinearMap.pi_ext' fun j => LinearMap.ext_ring (funext fun i => ?_)
  have := congrFun (congrFun (congrFun h τ) i) j
  exact (emb τ).injective (by simpa [embH, hδ] using this)

end GlobalTheory.ThetaMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsFamPOfKits
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

noncomputable section

namespace GlobalTheory.EX


open Classical in
def cutScale {eps x1 la y : ℝ} (S : Scales la) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hx : 1 < x1) (hy : x1 ≤ y) (x : ℝ) : Scale :=
  S.scale (if x1 < x ∧ x ∈ S.Win then x else y) eps (by split_ifs with h; exacts [hx.trans h.1, hx.trans_le hy]) h0 h1

private theorem cutScale_alt {eps x1 la y : ℝ} (S : Scales la) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hx : 1 < x1) (hy : x1 ≤ y)
    (x : ℝ) (h : x1 < x) (hw : x ∈ S.Win) : (cutScale S h0 h1 hx hy x).x = x := if_pos ⟨h, hw⟩

private theorem cutScale_ge {eps x1 la y : ℝ} (S : Scales la) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hx : 1 < x1) (hy : x1 ≤ y)
    (x : ℝ) : x1 ≤ (cutScale S h0 h1 hx hy x).x := by
  unfold cutScale Scales.scale
  dsimp only
  split_ifs with h
  exacts [h.1.le, hy]

private theorem cutScale_mem {eps x1 la y : ℝ} (S : Scales la) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hx : 1 < x1) (hy : x1 ≤ y)
    (hw : y ∈ S.Win) (x : ℝ) : S.Mem (cutScale S h0 h1 hx hy x) := by
  refine ⟨rfl, ?_⟩
  unfold cutScale Scales.scale
  dsimp only
  split_ifs with h
  exacts [h.2, hw]

theorem Kit.bTopOf_eq {C : FC} {cD ch : ℝ} {s : Scale} (k : Kit C cD ch s) (i i' : k.Ix) :
    bTopOf (k.pt i).L = bTopOf (k.pt i').L := by
  unfold bTopOf
  rw [(k.val i).La_eq, (k.val i').La_eq, k.sc_eq i, k.sc_eq i', (k.same i i').1]

theorem bTopOf_ge {D : D7} (L : SizeData₂ D) (h : L.sc.x ^ L.sc.eps ≤ L.LaG) :
    L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ (2 * L.sc.eps) * L.sc.b' / (D.R.k : ℝ) ≤ bTopOf L := by
  have hsx : (0 : ℝ) < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb : 0 ≤ L.sc.b' := by
    unfold Scale.b' Scale.a Scale.b Scale.X'
    positivity
  have hd : 0 ≤ L.sc.delta1 := by
    unfold Scale.delta1
    positivity
  have e : L.sc.x ^ (2 * L.sc.eps) = L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps := by
    rw [two_mul, Real.rpow_add hsx]
  unfold bTopOf
  rw [e, ← mul_assoc]
  gcongr

def famOfKits {eps : ℝ} (C : FC) (cD ch x1 : ℝ) (hx1 : 1 < x1) (hS : Std C) (hG : C.GK.Nonneg)
    (J : ℝ) (Wn : Set ℝ) (hW : ∀ y : ℝ, ∃ x ∈ Wn, y ≤ x)
    (s : ℝ → Scale) (he : ∀ x, (s x).eps = eps) (hJ : ∀ x, (s x).J = J) (hs : ∀ x, x1 < x → x ∈ Wn → (s x).x = x)
    (k : ∀ x, Kit C cD ch (s x)) (nu : ∀ x i, NumAt C ((k x).pt i).L) : FamP eps where
  x1 := x1
  one_lt_family_threshold := hx1
  Ix x := {_i : (k x).Ix // x ≤ x1 ∨ x ∈ Wn}
  Win := Wn
  Win_unb := hW
  Ix_win x hx := ⟨⟨(k x).ne.some, Or.inr hx⟩⟩
  Ix_zero := ⟨⟨(k 0).ne.some, Or.inl (zero_le_one.trans hx1.le)⟩⟩
  D x i := ((k x).pt i.1).D
  L x i := ((k x).pt i.1).L
  L_x x i hx := by rw [(k x).sc_eq i.1, hs x hx (i.2.resolve_left hx.not_ge)]
  L_eps x i := by rw [(k x).sc_eq i.1, he x]
  J := J
  L_J x i := by rw [(k x).sc_eq i.1, hJ x]
  R_eq x i i' := ((k x).same i.1 i'.1).1
  TTn x := ((k x).pt (k x).ne.some).D.host.TT.image Formalism.HC.Frame.A.val
  TT_eq x i := ((k x).same i.1 _).2.1
  realisedChain_torus_eq x i i' := ((k x).same i.1 i'.1).2.2.1
  q_eq x i i' := ((k x).same i.1 i'.1).2.2.2.1
  d_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.1
  QS_eq x i i' := ((k x).same i.1 i'.1).QS_eq
  art_eq x i i' := ((k x).same i.1 i'.1).art_eq
  rd_eq x i i' := ((k x).same i.1 i'.1).rd_eq
  Co := C.P.Cpde
  o_le_Co x i _ := ((k x).val i.1).host.o_le
  QS_le_Co x i _ := ((k x).val i.1).host.QS_le
  g_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.1
  pde_eq x i i' := ⟨((k x).same i.1 i'.1).2.2.2.2.2.2.1, ((k x).same i.1 i'.1).2.2.2.2.2.2.2.1⟩
  W x := (k x).W
  eW x i := (k x).eW i.1
  eW_code x i i' := (k x).eW_code i.1 i'.1
  CGam := C.CGam
  CGam_eq x i := (nu x i.1).CGam_eq
  Cc := C.Cc
  Cc_eq x i := (nu x i.1).Cc_eq
  Ct := C.Ct
  Ct_eq x i := (nu x i.1).Ct_eq
  CT2 := C.CT2
  secondConstant_eq x i := (nu x i.1).secondConstant_eq
  bTop x := bTopOf ((k x).pt (k x).ne.some).L
  bTop_eq x hx i := by
    rw [(k x).bTopOf_eq _ i.1]
    unfold bTopOf
    rw [show ((k x).pt i.1).L.sc.x = x by rw [(k x).sc_eq i.1, hs x hx (i.2.resolve_left hx.not_ge)],
      show ((k x).pt i.1).L.sc.eps = eps by rw [(k x).sc_eq i.1, he x]]
  bTop_ge x hx i := by
    rw [(k x).bTopOf_eq _ i.1]
    have h := bTopOf_ge _ (nu x i.1).LaG_ge
    rwa [show ((k x).pt i.1).L.sc.x = x by rw [(k x).sc_eq i.1, hs x hx (i.2.resolve_left hx.not_ge)],
      show ((k x).pt i.1).L.sc.eps = eps by rw [(k x).sc_eq i.1, he x]] at h
  bT_le x _ i t := by
    rw [(k x).bTopOf_eq _ i.1]
    exact (nu x i.1).bT_le t
  coverS x _ i0 u0 hu := by
    obtain ⟨i, hi⟩ := (k x).cover_weights i0.1 u0 hu
    exact ⟨⟨i, i0.2⟩, hi⟩
  params x _ i := (nu x i.1).params
  PK := C.PK
  params_K x _ i := (nu x i.1).params_K
  parT x _ i := (nu x i.1).parT
  PT := C.PT
  parT_K x _ i := (nu x i.1).parT_K
  CTu := C.CTu
  sizes x _ i := (nu x i.1).sizes
  ties x i := ((k x).pt i.1).xa.ties
  gatT x i := ((k x).pt i.1).gatT
  X x i := ((k x).pt i.1).xa.X
  Gx x i := ((k x).pt i.1).ta.Gx
  Gy x i := ((k x).pt i.1).ta.Gy
  GK := C.GK
  GK_nonneg := hG
  supp_sat x _ i := ((k x).pt i.1).ta.supp_sat
  tw_supp x _ i := ((k x).pt i.1).ta.tw_supp
  fills x _ i := ((k x).pt i.1).ta.fills
  lats0 x _ i := ((k x).pt i.1).ta.lats0
  latTied x _ i := ((k x).pt i.1).ta.latTied
  Csz := C.Csz
  nuDef x _ i := ((k x).pt i.1).xa.nuDef
  nprimeDef x _ i := ((k x).pt i.1).xa.nprimeDef
  rrDef x _ i := ((k x).pt i.1).xa.rrDef
  h_eq x _ i := ((k x).pt i.1).xa.h_eq
  cX := C.cX
  ex x _ i := ((k x).pt i.1).xa.ex
  rho_le x hx i := by
    have h := (nu x i.1).rho_le
    rwa [show ((k x).pt i.1).L.sc.x = x by rw [(k x).sc_eq i.1, hs x hx (i.2.resolve_left hx.not_ge)]] at h
  Cr := C.Cr
  one_le_Cr := hS.1.2.2.2.2.2.2.1.ge
  drop_iff x _ i := ((k x).pt i.1).ta.drop_iff
  fixed := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, _⟩ := hS.1
    exact ⟨a1, a2, a3, a4, a5, a6, a7, fun x _ i => ⟨(nu x i.1).CnW_eq.trans a8, (nu x i.1).eP_eq ▸ a9⟩⟩
  eta_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.1
  Sc_shared x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.1
  hP_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.2.1
  bs_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.2.2.1
  off_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.2.2.2.1
  kapI_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  ep_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem exists_famP_of_kits : ∀ (eps : ℝ) (C : FC) (cD ch x1 la : ℝ) (S : Scales la), 0 < eps → eps < 1 / 52 → 1 < x1 → 1 ≤ la → Std C → C.GK.Nonneg → ∀ k : ∀ s : Scale, s.eps = eps → x1 ≤ s.x → S.Mem s → Kit C cD ch s, (∀ s h h' h'' i, Nonempty (NumAt C ((k s h h' h'').pt i).L)) → ∃ Fm : FamP eps, Fm.x1 = x1 ∧ Fm.cPre = C.cPre ∧ Fm.cOut = C.cOut.set 15 C.P.Cpde ∧ Fm.cMid = C.cMid ∧ Fm.cLast = C.cLast ∧ Fm.CTu = C.CTu ∧ (∀ Q : PtProp, (∀ s h h' h'' i, ((k s h h' h'').pt i).Has Q) → classOf Q Fm) ∧ (∀ Rr : ∀ (D : D7) (L : SizeData₂ D), G.Inst D L → Prop, (∀ s h h' h'' i, Rr ((k s h h' h'').pt i).D ((k s h h' h'').pt i).L ((k s h h' h'').pt i).ta.Gx) → ∀ x, ∀ i : Fm.Ix x, Rr (Fm.D x i) (Fm.L x i) (Fm.Gx x i)) ∧ Fm.J = S.J ∧ Fm.Win = S.Win ∧ Fm.Co = C.P.Cpde := by
  intro eps C cD ch x1 la S h0 h1 hx hla hS hG k hN
  obtain ⟨y, hw, hy⟩ := S.unb hla x1
  have hJ : S.J ≤ C.P.Cpde := by
    have k0 := k (cutScale S h0 h1 hx hy 0) rfl (cutScale_ge S h0 h1 hx hy 0) (cutScale_mem S h0 h1 hx hy hw 0)
    have h := (k0.val k0.ne.some).host.J_le
    rwa [k0.sc_eq] at h
  refine ⟨famOfKits C cD ch x1 hx hS hG S.J S.Win (S.unb hla) (cutScale S h0 h1 hx hy) (fun _ => rfl) (fun _ => rfl)
    (cutScale_alt S h0 h1 hx hy)
    (fun x => k (cutScale S h0 h1 hx hy x) rfl (cutScale_ge S h0 h1 hx hy x) (cutScale_mem S h0 h1 hx hy hw x))
    (fun x i => (hN _ _ _ _ i).some),
    rfl, rfl, ?_, rfl, rfl, rfl, fun Q hQ x _ i => hQ _ _ _ _ i.1, fun Rr hR x i => hR _ _ _ _ i.1, rfl, rfl, rfl⟩
  rw [← congrArg (C.cOut.set 15) (max_eq_left hJ)]
  rfl

end GlobalTheory.EX

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotDvdCardStabilizerForm
section
noncomputable section

namespace GlobalTheory.LvT.StabOrder

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2

theorem rank_le (R : Ranks) {i j : ℕ} (h : i ≤ j) : R.N i ≤ R.N j := by
  unfold Ranks.N
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem prime_le_of_embed {E G : Type} [Field E] [NumberField E] [Group G] [Finite G] {n : ℕ}
    (φ : G →* ((Fin n → E) ≃ₗ[E] (Fin n → E))) (hφ : Function.Injective φ) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card G) : p ≤ Module.finrank ℚ E * n + 1 := by
  haveI : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  have h := prime_le_of_dvd_card φ.range hp (by rwa [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv])
  rwa [Module.finrank_fin_fun] at h

theorem prime_le_of_embed_GL {E G : Type} [Field E] [NumberField E] [Group G] [Finite G] {n : ℕ}
    (φ : G →* GL (Fin n) E) (hφ : Function.Injective φ) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card G) : p ≤ Module.finrank ℚ E * n + 1 :=
  prime_le_of_embed ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).toMonoidHom.comp
      ((Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := E)).toMonoidHom.comp φ))
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).injective.comp
      ((Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := E)).injective.comp hφ)) hp hd

section Concrete

variable {F : Fields} {Pr : Primes F} {R : Ranks} {W : Wts F Pr.Word R} {a : ℝ}

variable {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 F.E))}

variable (sel : HeightOneSpectrum (𝓞 F.F) → HeightOneSpectrum (𝓞 F.E)) {S : Set ℕ} (mu : Tup F.F F.E F.K S)
  (cst : LocCst F (rowSG Pr sel mu)) (L : ChIdx F Pr R (QE sel (mu : Chr F.F F.E F.K)))

end Concrete

section Record

variable {D : D7} {u : D.what₂.Word}

theorem stabUnit_of_embed (X : Ch D u) (E : Type) [Field E] [NumberField E]
    (hT : Module.finrank ℚ E * D.R.N D.R.m + 1 < X.A.T)
    (h : ∀ i, i ≤ D.R.m → ∀ c : X.C.cls i, ∃ j : X.C.stab i c →* GL (Fin (D.R.N i)) E, Function.Injective j) :
    StabUnit X := fun i hi c hd => by
  obtain ⟨j, hj⟩ := h i hi c
  have h1 := prime_le_of_embed_GL j hj X.A.T_prime hd
  have h2 := Nat.mul_le_mul_left (Module.finrank ℚ E) (rank_le D.R hi)
  omega

theorem stabUnit_of_chainIn (X : Ch D u) {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K]
    (I : ChainIn E K D.what₂.Tau D.R) (emb : D.what₂.Tau → E →+* K) (σ : K →+* ℂ) (hI : I.Ok)
    (hC : X.C = I.chain emb σ hI (D.hcW u)) (hT : Module.finrank ℚ E * D.R.N D.R.m + 1 < X.A.T) : StabUnit X := by
  refine stabUnit_of_embed X E hT ?_
  rw [hC]
  intro i _ c
  refine ⟨((I.S i).gam c.1).comp (MulAction.stabilizer _ ((I.S i).rep c)).subtype, ?_⟩
  rw [injective_iff_map_eq_one]
  exact fun g hg => Subtype.ext ((hI.step i).stab_inj c.1 g.1 _ g.2 hg)

end Record

end GlobalTheory.LvT.StabOrder
end
end

