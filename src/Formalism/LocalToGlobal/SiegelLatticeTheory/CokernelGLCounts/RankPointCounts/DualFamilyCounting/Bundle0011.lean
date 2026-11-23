module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0009
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0017
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocFSubspace
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G7

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mem_dual_iff (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 K) K) := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

private lemma mem_locF_lemma {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (𝔭 : Ideal (𝓞 F))
    (L : Submodule (𝓞 K) W) (x : W) :
    x ∈ locF 𝔭 L ↔ ∃ s ∈ Submonoid.closure
      {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}, s • x ∈ L := Iff.rfl

private lemma star_fix_lemma_2 (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} {s : 𝓞 K}
    (hs : s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}) :
    star (algebraMap (𝓞 K) K s) = algebraMap (𝓞 K) K s := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨t, -, rfl⟩ := hx
    exact (hF _).mpr ⟨(t : F), rfl⟩
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul, star_mul', hx, hy]

private lemma smul_smul_lemma_3 (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) {𝔭 : Ideal (𝓞 F)} {s t : 𝓞 K}
    (ht : t ∈ Submonoid.closure {s : 𝓞 K | ∃ u : 𝓞 F, u ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) u = s})
    (x y : V) : h (t • y) (s • x) = (t * s) • h y x := by
  rw [← algebraMap_smul K t y, ← algebraMap_smul K s x]
  simp only [map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, starRingEnd_apply]
  rw [star_fix_lemma_2 hF ht, Algebra.smul_def, map_mul]
  ring

theorem locF_dual_le (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) : locF 𝔭 (Formalism.HermitianLatticesTheory.dual h L) ≤ dualF h 𝔭 (locF 𝔭 L) := by
  intro x hx
  change ∀ y ∈ locF 𝔭 L, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
  intro y hy
  obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 _ x).mp hx
  obtain ⟨t, ht, hty⟩ := (mem_locF_lemma 𝔭 _ y).mp hy
  refine (mem_locF_lemma 𝔭 _ _).mpr ⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩
  rw [← smul_smul_lemma_3 hF h ht x y]
  exact (mem_dual_iff h L (s • x)).mp hsx (t • y) hty

theorem dualF_locF_le (h : V →ₗ⋆[K] V →ₗ[K] K) {L : Submodule (𝓞 K) V} (hL : L.FG)
    {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) : dualF h 𝔭 (locF 𝔭 L) ≤ locF 𝔭 (Formalism.HermitianLatticesTheory.dual h L) := by
  classical
  intro x hx
  have hx' : ∀ y ∈ locF 𝔭 L, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := hx
  obtain ⟨G, rfl⟩ := hL
  have hg : ∀ g ∈ G, ∃ s ∈ Submonoid.closure
      {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s},
      s • h g x ∈ (1 : Submodule (𝓞 K) K) := fun g hg =>
    (mem_locF_lemma 𝔭 _ _).mp (hx' g ((mem_locF_lemma 𝔭 _ g).mpr
      ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.subset_span hg⟩))
  choose! sg hsg hsgx using hg
  refine (mem_locF_lemma 𝔭 _ _).mpr
    ⟨∏ g ∈ G, sg g, Submonoid.prod_mem _ fun g hg => hsg g hg, ?_⟩
  rw [mem_dual_iff]
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    rw [← algebraMap_smul K (∏ g ∈ G, sg g) x, LinearMap.map_smul, smul_eq_mul]
    have e : algebraMap (𝓞 K) K (∏ g ∈ G, sg g) * h y x =
        (∏ g ∈ G.erase y, sg g) • (sg y • h y x) := by
      rw [← Finset.mul_prod_erase G sg hy, Algebra.smul_def, Algebra.smul_def, map_mul]
      ring
    rw [e]
    exact Submodule.smul_mem _ _ (hsgx y hy)
  | zero => rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add (f := _), LinearMap.add_apply]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    obtain ⟨r, hr⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range c
    rw [← algebraMap_smul K c y, map_smulₛₗ h (algebraMap (𝓞 K) K c) y, LinearMap.smul_apply,
      smul_eq_mul, starRingEnd_apply, ← hr, ← smul_eq_mul, algebraMap_smul]
    exact Submodule.smul_mem _ r hy

theorem locF_dual (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) {L : Submodule (𝓞 K) V} (hL : L.FG)
    {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) : locF 𝔭 (Formalism.HermitianLatticesTheory.dual h L) = dualF h 𝔭 (locF 𝔭 L) := le_antisymm (locF_dual_le hF h L hp) (dualF_locF_le h hL hp)

private lemma ne_zero_lemma_4 {𝔭 : Ideal (𝓞 F)} {s : 𝓞 K}
    (hs : s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}) :
    algebraMap (𝓞 K) K s ≠ 0 := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ 𝔭.zero_mem)
    have e : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := rfl
    rw [e]
    exact (map_ne_zero _).mpr (by simpa using ht0)
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_ne_zero hx hy

theorem locF_subspace (U : Submodule K V) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) :
    locF 𝔭 (U.restrictScalars (𝓞 K)) = U.restrictScalars (𝓞 K) := by
  ext x
  rw [mem_locF_lemma]
  constructor
  · rintro ⟨s, hs, hsx⟩
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := ne_zero_lemma_4 hs
    have e : x = (algebraMap (𝓞 K) K s)⁻¹ • (s • x) := by
      rw [← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [e]
    exact U.smul_mem _ hsx
  · intro hx
    exact ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩

private lemma mem_image_lemma_5 {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {s : 𝓞 K}
    (hs : s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}) :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s := by
  induction hs using Submonoid.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨1, (Ideal.ne_top_iff_one 𝔭).mp hp.ne_top, map_one _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a * b, fun hab => (hp.mem_or_mem hab).elim ha hb, map_mul _ _ _⟩

private lemma le_of_locF_lemma_6 (A B : Submodule (𝓞 K) V)
    (hAB : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → locF 𝔭 A = locF 𝔭 B) : A ≤ B := by
  intro x hx
  let J : Ideal (𝓞 F) :=
    Ideal.comap (algebraMap (𝓞 F) (𝓞 K)) (B.comap (LinearMap.toSpanSingleton (𝓞 K) V x))
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨𝔭, hmax, hle⟩ := Ideal.exists_le_maximal J hne
    have hxA : x ∈ locF 𝔭 A :=
      (mem_locF_lemma 𝔭 A x).mpr ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩
    rw [hAB 𝔭 hmax] at hxA
    obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 B x).mp hxA
    obtain ⟨t, ht, rfl⟩ := mem_image_lemma_5 hmax.isPrime hs
    exact ht (hle (show t ∈ J from hsx))
  have h1 : (1 : 𝓞 F) ∈ J := by rw [hJ]; exact Submodule.mem_top
  simpa [J] using h1

theorem eq_of_locF (A B : Submodule (𝓞 K) V)
    (hAB : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → locF 𝔭 A = locF 𝔭 B) : A = B := le_antisymm (le_of_locF_lemma_6 A B hAB) (le_of_locF_lemma_6 B A fun 𝔭 h => (hAB 𝔭 h).symm)

end Formalism.L2.SG.Pf.G7
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXECPfA
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.EC

open Formalism.QuantumDeterminants WlocSk.NB
open Formalism.MainNotions.BridgeCSB (Fil lieN adjH adjH_apply dg)

variable {k r : ℕ}

abbrev J (k r : ℕ) := (CI k r ⊕ CI k r) ⊕ Fin r

def toC (y : J k r → ℝ) : (CI k r → ℂ) × (Fin r → ℝ) :=
  (fun i => ⟨y (Sum.inl (Sum.inl i)), y (Sum.inl (Sum.inr i))⟩, fun a => y (Sum.inr a))

def Lm (t : (CI k r → ℂ) × (Fin r → ℝ)) : Mx k r :=
  mkM (cA t.1 - 1) (cB t.1) (cK t.1 t.2) (-(dD k * (cB t.1)ᴴ)) (-(cA t.1 - 1)ᴴ) - mkM 0 0 0 0 0

def ShearStep : Prop := ∀ k r : ℕ, ∃ σ : (J k r → ℝ) → (CI k r → ℂ) × (Fin r → ℝ),
  MeasurePreserving σ volume volume ∧ ∀ y, phi0 (σ y).1 (σ y).2 = NormedSpace.exp (Lm (toC y))

def ConstStep : Prop := ∀ k r : ℕ, ∃ Λ : (J k r → ℝ) → Formalism.MainNotions.S.lieE (Nset k r), Measurable Λ ∧
  (∀ y, ((Λ y : Formalism.MainNotions.S.lieE (Nset k r)) : EuclideanSpace ℝ _) = Formalism.MainNotions.BridgeCSB.RL (k := k) (r := r) (Lm (toC y))) ∧
  (volume : Measure (Formalism.MainNotions.S.lieE (Nset k r))) = ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k)) • volume.map Λ

theorem dg_eI (a : Fin r) : dg k r (eI k r a) = a.val := by
  have := a.isLt; unfold dg eI; simp only; split_ifs <;> omega
theorem dg_wI (j : Fin (k + 1)) : dg k r (wI k r j) = r := by
  have := j.isLt; unfold dg wI; simp only; split_ifs <;> omega
theorem dg_esI (a : Fin r) : dg k r (esI k r a) = 2 * r - a.val := by
  have := a.isLt; unfold dg esI; simp only; split_ifs <;> omega

theorem gtau_eI (a : Fin r) : Formalism.QuantumDeterminants.WeylGroupFacts.tau k r (eI k r a) = esI k r a := by
  unfold Formalism.QuantumDeterminants.WeylGroupFacts.tau eI esI; apply Fin.ext; simp only; split_ifs <;> omega
theorem gtau_esI (a : Fin r) : Formalism.QuantumDeterminants.WeylGroupFacts.tau k r (esI k r a) = eI k r a := by
  unfold Formalism.QuantumDeterminants.WeylGroupFacts.tau eI esI; apply Fin.ext; simp only; split_ifs <;> omega
theorem gtau_wI (j : Fin (k + 1)) : Formalism.QuantumDeterminants.WeylGroupFacts.tau k r (wI k r j) = wI k r j := by
  unfold Formalism.QuantumDeterminants.WeylGroupFacts.tau wI; apply Fin.ext; simp only; split_ifs <;> omega
theorem gsgn_eI (a : Fin r) : Formalism.QuantumDeterminants.WeylGroupFacts.sgn k r (eI k r a) = 1 := by
  unfold Formalism.QuantumDeterminants.WeylGroupFacts.sgn eI; simp only; split_ifs <;> first | rfl | omega
theorem gsgn_esI (a : Fin r) : Formalism.QuantumDeterminants.WeylGroupFacts.sgn k r (esI k r a) = 1 := by
  unfold Formalism.QuantumDeterminants.WeylGroupFacts.sgn esI; simp only; split_ifs <;> first | rfl | omega
theorem gsgn_wI (j : Fin (k + 1)) : Formalism.QuantumDeterminants.WeylGroupFacts.sgn k r (wI k r j) = dD k j j := by
  unfold Formalism.QuantumDeterminants.WeylGroupFacts.sgn wI dD
  simp only [Matrix.diagonal_apply_eq]
  split_ifs <;> first | rfl | omega

theorem dD_star (j : Fin (k + 1)) : star (dD k j j) = dD k j j := by
  simp only [dD, Matrix.diagonal_apply_eq]; split_ifs <;> simp
theorem dD_sq' (j : Fin (k + 1)) : dD k j j * dD k j j = 1 := by
  simp only [dD, Matrix.diagonal_apply_eq]; split_ifs <;> simp

theorem chart_matrix_lower (x : CI k r → ℂ) {a b : Fin r} (h : b ≤ a) : (cA x - 1) a b = 0 := by
  rw [Matrix.sub_apply, Matrix.one_apply]; unfold cA; rw [dite_eq_right (not_lt.2 h)]; split_ifs <;> simp

theorem chart_matrix_upper (x : CI k r → ℂ) {a b : Fin r} (h : a < b) : (cA x - 1) a b = x (Sum.inl ⟨(a, b), h⟩) := by
  rw [Matrix.sub_apply, Matrix.one_apply, if_neg (ne_of_lt h)]; unfold cA; rw [dite_eq_left h, sub_zero]

theorem cK_skew (x : CI k r → ℂ) (s : Fin r → ℝ) (a b : Fin r) : cK x s a b + star (cK x s b a) = 0 := by
  unfold cK
  rcases lt_trichotomy a b with h | h | h
  · rw [dite_eq_left h, dite_eq_right (not_lt.2 h.le), dite_eq_left h, star_neg, star_star, add_neg_cancel]
  · subst h
    rw [dite_eq_right (lt_irrefl _), dite_eq_right (lt_irrefl _), star_mul', Complex.star_def,
      Complex.conj_ofReal, Complex.conj_I]
    ring
  · rw [dite_eq_right (not_lt.2 h.le), dite_eq_left h, dite_eq_left h, neg_add_cancel]

section entries

variable (t : (CI k r → ℂ) × (Fin r → ℝ))

@[simp] theorem Lm_ee (a b : Fin r) : Lm t (eI k r a) (eI k r b) = (cA t.1 - 1) a b := by
  simp only [Lm, Matrix.sub_apply, mk_ee, Matrix.zero_apply, sub_zero]
@[simp] theorem Lm_ew (a : Fin r) (j : Fin (k + 1)) : Lm t (eI k r a) (wI k r j) = cB t.1 a j := by
  simp only [Lm, Matrix.sub_apply, mk_ew, Matrix.zero_apply, sub_zero]
@[simp] theorem Lm_es (a b : Fin r) : Lm t (eI k r a) (esI k r b) = cK t.1 t.2 a b := by
  simp only [Lm, Matrix.sub_apply, mk_es, Matrix.zero_apply, sub_zero]
@[simp] theorem Lm_we (j : Fin (k + 1)) (b : Fin r) : Lm t (wI k r j) (eI k r b) = 0 := by
  simp only [Lm, Matrix.sub_apply, mk_we, sub_zero]
@[simp] theorem Lm_ww (j c : Fin (k + 1)) : Lm t (wI k r j) (wI k r c) = 0 := by
  simp only [Lm, Matrix.sub_apply, mk_ww, sub_self]
@[simp] theorem Lm_ws (j : Fin (k + 1)) (b : Fin r) :
    Lm t (wI k r j) (esI k r b) = -(dD k j j * star (cB t.1 b j)) := by
  simp only [Lm, Matrix.sub_apply, mk_ws, Matrix.zero_apply, sub_zero, Matrix.neg_apply, dD_mul_apply,
    conjTranspose_apply]
@[simp] theorem Lm_se (a b : Fin r) : Lm t (esI k r a) (eI k r b) = 0 := by
  simp only [Lm, Matrix.sub_apply, mk_se, sub_zero]
@[simp] theorem Lm_sw (a : Fin r) (j : Fin (k + 1)) : Lm t (esI k r a) (wI k r j) = 0 := by
  simp only [Lm, Matrix.sub_apply, mk_sw, sub_zero]
@[simp] theorem Lm_ss (a b : Fin r) : Lm t (esI k r a) (esI k r b) = -star ((cA t.1 - 1) b a) := by
  simp only [Lm, Matrix.sub_apply, mk_ss, Matrix.zero_apply, sub_zero, Matrix.neg_apply, conjTranspose_apply]

end entries

theorem chart_filtration_one (t : (CI k r → ℂ) × (Fin r → ℝ)) : Fil 1 (Lm t) := by
  intro i j h
  obtain ⟨p, rfl⟩ := (posE k r).surjective i
  obtain ⟨q, rfl⟩ := (posE k r).surjective j
  rcases p with a | c | a <;> rcases q with b | c' | b <;>
    simp only [posE_apply, pos, dg_eI, dg_wI, dg_esI] at h <;>
    simp only [posE_apply, pos, Lm_ee, Lm_ew, Lm_es, Lm_we, Lm_ww, Lm_ws, Lm_se, Lm_sw, Lm_ss]
  all_goals first
    | rfl
    | exact chart_matrix_lower _ (Fin.le_iff_val_le_val.2 (by omega))
    | (rw [neg_eq_zero, star_eq_zero]
       exact chart_matrix_lower _ (Fin.le_iff_val_le_val.2 (by have := a.isLt; have := b.isLt; omega)))
    | (exfalso; first
        | (have := a.isLt; have := b.isLt; omega)
        | (have := a.isLt; omega)
        | (have := b.isLt; omega))

theorem Lm_adj (t : (CI k r → ℂ) × (Fin r → ℝ)) : adjH (Lm t) + Lm t = 0 := by
  ext i j
  rw [Matrix.add_apply, adjH_apply, Matrix.zero_apply]
  obtain ⟨p, rfl⟩ := (posE k r).surjective i
  obtain ⟨q, rfl⟩ := (posE k r).surjective j
  rcases p with a | c | a <;> rcases q with b | c' | b <;>
    simp only [posE_apply, pos, gtau_eI, gtau_esI, gtau_wI, gsgn_eI, gsgn_esI, gsgn_wI,
      Lm_ee, Lm_ew, Lm_es, Lm_we, Lm_ww, Lm_ws, Lm_se, Lm_sw, Lm_ss, star_zero, mul_zero, zero_mul,
      add_zero, one_mul, mul_one, star_neg, star_star, neg_add_cancel, star_mul', dD_star]
  all_goals first
    | rw [add_neg_cancel]
    | linear_combination cK_skew t.1 t.2 a b
    | linear_combination (-(cB t.1 a c')) * dD_sq' c'

theorem Lm_mem (t : (CI k r → ℂ) × (Fin r → ℝ)) : Lm t ∈ lieN k r := ⟨chart_filtration_one t, Lm_adj t⟩

def hC : CI k r → ℕ
  | Sum.inl p => p.1.2.val - p.1.1.val
  | Sum.inr (Sum.inl q) => r - q.1.val
  | Sum.inr (Sum.inr p) => 2 * r - p.1.1.val - p.1.2.val

def ht : J k r → ℕ
  | Sum.inl (Sum.inl c) => hC c
  | Sum.inl (Sum.inr c) => hC c
  | Sum.inr a => 2 * r - 2 * a.val

theorem coordinate_first_eq {y y' : J k r → ℝ} {p : ℕ} (h : ∀ j, ht j < p → y j = y' j) {c : CI k r} (hc : hC c < p) :
    (toC y).1 c = (toC y').1 c := by
  simp only [toC]; rw [h (Sum.inl (Sum.inl c)) hc, h (Sum.inl (Sum.inr c)) hc]

theorem coordinate_second_eq {y y' : J k r → ℝ} {p : ℕ} (h : ∀ j, ht j < p → y j = y' j) {a : Fin r}
    (ha : 2 * r - 2 * a.val < p) : (toC y).2 a = (toC y').2 a := by
  simp only [toC]; rw [h (Sum.inr a) ha]

theorem Lm_fil_sub {y y' : J k r → ℝ} {p : ℕ} (h : ∀ j, ht j < p → y j = y' j) :
    Fil p (Lm (toC y) - Lm (toC y')) := by
  intro i j hij
  rw [Matrix.sub_apply, sub_eq_zero]
  obtain ⟨P, rfl⟩ := (posE k r).surjective i
  obtain ⟨Q, rfl⟩ := (posE k r).surjective j
  rcases P with a | c | a <;> rcases Q with b | c' | b <;>
    simp only [posE_apply, pos, dg_eI, dg_wI, dg_esI] at hij <;>
    simp only [posE_apply, pos, Lm_ee, Lm_ew, Lm_es, Lm_we, Lm_ww, Lm_ws, Lm_se, Lm_sw, Lm_ss]
  · by_cases hab : a < b
    · rw [chart_matrix_upper _ hab, chart_matrix_upper _ hab]
      exact coordinate_first_eq h (by simp only [hC]; omega)
    · rw [chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab)]
  · exact coordinate_first_eq h (by simp only [hC]; omega)
  · unfold cK
    split_ifs with h1 h2
    · exact coordinate_first_eq h (by simp only [hC]; have := b.isLt; omega)
    · rw [coordinate_first_eq h (by simp only [hC]; have := a.isLt; omega)]
    · have e : a = b := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
      subst e
      rw [coordinate_second_eq h (by have := a.isLt; omega)]
  · simp only [cB]
    rw [coordinate_first_eq h (c := Sum.inr (Sum.inl (b, c))) (by simp only [hC]; have := b.isLt; omega)]
  · by_cases hab : b < a
    · rw [chart_matrix_upper _ hab, chart_matrix_upper _ hab]
      rw [coordinate_first_eq h (by simp only [hC]; have := a.isLt; have := b.isLt; omega)]
    · rw [chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab)]

theorem Lm_add (t t' : (CI k r → ℂ) × (Fin r → ℝ)) : Lm (t + t') = Lm t + Lm t' := by
  ext i j
  rw [Matrix.add_apply]
  obtain ⟨P, rfl⟩ := (posE k r).surjective i
  obtain ⟨Q, rfl⟩ := (posE k r).surjective j
  rcases P with a | c | a <;> rcases Q with b | c' | b <;>
    simp only [posE_apply, pos, Lm_ee, Lm_ew, Lm_es, Lm_we, Lm_ww, Lm_ws, Lm_se, Lm_sw, Lm_ss, add_zero]
  · by_cases hab : a < b
    · rw [chart_matrix_upper _ hab, chart_matrix_upper _ hab, chart_matrix_upper _ hab]; rfl
    · rw [chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab), add_zero]
  · rfl
  · unfold cK
    split_ifs
    · rfl
    · simp only [Prod.fst_add, Pi.add_apply, star_add]; ring
    · simp only [Prod.snd_add, Pi.add_apply]; push_cast; ring
  · simp only [cB, Prod.fst_add, Pi.add_apply, star_add]; ring
  · by_cases hab : b < a
    · rw [chart_matrix_upper _ hab, chart_matrix_upper _ hab, chart_matrix_upper _ hab]
      simp only [Prod.fst_add, Pi.add_apply, star_add]; ring
    · rw [chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab)]; simp

theorem Lm_smul (c : ℝ) (t : (CI k r → ℂ) × (Fin r → ℝ)) : Lm (c • t) = c • Lm t := by
  ext i j
  rw [Matrix.smul_apply, Complex.real_smul]
  obtain ⟨P, rfl⟩ := (posE k r).surjective i
  obtain ⟨Q, rfl⟩ := (posE k r).surjective j
  rcases P with a | c | a <;> rcases Q with b | c' | b <;>
    simp only [posE_apply, pos, Lm_ee, Lm_ew, Lm_es, Lm_we, Lm_ww, Lm_ws, Lm_se, Lm_sw, Lm_ss, mul_zero]
  · by_cases hab : a < b
    · rw [chart_matrix_upper _ hab, chart_matrix_upper _ hab]; simp [Complex.real_smul]
    · rw [chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab), mul_zero]
  · simp [cB, Complex.real_smul]
  · unfold cK
    split_ifs
    · simp [Complex.real_smul]
    · simp only [Prod.smul_fst, Pi.smul_apply, Complex.real_smul, star_mul', Complex.star_def,
        Complex.conj_ofReal]; ring
    · simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]; push_cast; ring
  · simp only [cB, Prod.smul_fst, Pi.smul_apply, Complex.real_smul, star_mul', Complex.star_def,
      Complex.conj_ofReal]; ring
  · by_cases hab : b < a
    · rw [chart_matrix_upper _ hab, chart_matrix_upper _ hab]
      simp only [Prod.smul_fst, Pi.smul_apply, Complex.real_smul, star_mul', Complex.star_def,
        Complex.conj_ofReal]; ring
    · rw [chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab)]; simp

theorem toC_add (y y' : J k r → ℝ) : toC (y + y') = toC y + toC y' := by
  ext i
  · rfl
  · rfl

theorem toC_smul (c : ℝ) (y : J k r → ℝ) : toC (c • y) = c • toC y := by
  ext i
  · apply Complex.ext <;> simp [toC]
  · rfl

def LJ : (J k r → ℝ) →ₗ[ℝ] Mx k r where
  toFun y := Lm (toC y)
  map_add' y y' := by rw [toC_add, Lm_add]
  map_smul' c y := by rw [toC_smul, Lm_smul]; rfl

theorem continuous_LJ : Continuous (LJ (k := k) (r := r)) := LinearMap.continuous_of_finiteDimensional _

end Formalism.L2.SG.Pf.NcReal.JX.EC
end
end

