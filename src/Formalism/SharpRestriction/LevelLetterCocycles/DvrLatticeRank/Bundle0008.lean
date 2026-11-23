module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0027

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.InvLiftPfA
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem invLiftPf_quot_Δ (π' : LetA O n) (hu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π') (k : ℕ) (r₀ : W.DD T) (hr₀N : r₀ ∈ W.N T)
    (hΔ : ∀ δ ∈ W.DelF, W.γD T δ (π' ^ k • r₀) = π' ^ k • r₀) : r₀ ∈ W.NΔ T := by
  show r₀ ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ r₀ = r₀
  refine ⟨hr₀N, fun δ hδ => ?_⟩
  have h1 := hΔ δ hδ
  rw [← algebraMap_smul W.EE (π' ^ k) r₀, W.γD_smul, W.γE_ext] at h1
  have e : Formalism.BasicNotions.letγ (W.γ₀ δ) (π' ^ k) = π' ^ k := by
    change W.γA δ (π' ^ k) = π' ^ k
    rw [map_pow, hπΔ δ hδ]
  rw [e] at h1
  have hu' : IsUnit (algebraMap (LetA O n) W.EE (π' ^ k)) := by
    rw [map_pow]; exact hu.pow k
  exact hu'.smul_left_cancel.mp h1

private theorem PiNS_iff_lemma_3 (π' : LetA O n) (k : ℕ) (x : W.DD T) :
    x ∈ PiNS W T π' k ↔ (∃ y ∈ W.N T, π' ^ k • y = x) ∧ x ∈ DelS W T := by
  unfold PiNS
  rw [Submodule.mem_inf]
  refine and_congr ?_ Iff.rfl
  show x ∈ (W.N T).map (Formalism.MainNotions.DeltaInvariantLattices.smulA W T (π' ^ k)) ↔ _
  rw [Submodule.mem_map]
  rfl

private theorem DelS_iff_lemma_4 (x : W.DD T) : x ∈ DelS W T ↔ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
  unfold DelS
  simp [Submodule.mem_iInf, sub_eq_zero]

private theorem gamD_smulA_lemma_5 (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  show W.γD T g (a • x) = Formalism.BasicNotions.letγ (W.γ₀ g) a • W.γD T g x
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]

private theorem cancel_lemma_6 (π' : LetA O n) (hu : IsUnit (algebraMap (LetA O n) W.EE π')) (k : ℕ)
    (u v : W.DD T) (h : π' ^ k • u = π' ^ k • v) : u = v := by
  rw [← algebraMap_smul W.EE (π' ^ k) u, ← algebraMap_smul W.EE (π' ^ k) v] at h
  have hu' : IsUnit (algebraMap (LetA O n) W.EE (π' ^ k)) := by rw [map_pow]; exact hu.pow k
  exact hu'.smul_left_cancel.mp h

private theorem PiNS_anti_lemma_7 (π' : LetA O n) {a b : ℕ} (hab : a ≤ b) {z : W.DD T}
    (hz : z ∈ PiNS W T π' b) : z ∈ PiNS W T π' a := by
  obtain ⟨⟨y, hy, hyz⟩, hzD⟩ := (PiNS_iff_lemma_3 W T π' b z).mp hz
  refine (PiNS_iff_lemma_3 W T π' a z).mpr ⟨⟨π' ^ (b - a) • y, (W.N T).smul_mem _ hy, ?_⟩, hzD⟩
  rw [← hyz, smul_smul, ← pow_add, show a + (b - a) = b by omega]

theorem invLiftPf_inj (π' f t : LetA O n) (c₀ : O) (hf : W.γA W.gam π' = π' * f)
    (ht : f - algebraMap O (LetA O n) c₀ = π' * t)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hγN : ∀ x ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam x - x = π' • d)
    (hK : W.gamK = W.gam) (M : ℕ)
    (hnz : ∀ y : ℕ, 1 ≤ y → y < M → ∀ r₀ ∈ W.N T, ∀ d ∈ W.N T,
      (c₀ ^ y - 1) • r₀ = π' • d → ∃ e ∈ W.N T, r₀ = π' • e)
    (x : W.DD T) (hx : x ∈ PiNS W T π' 1) (hgx : W.γD T W.gamK x - x ∈ PiNS W T π' M) :
    x ∈ PiNS W T π' M := by
  have hx' := (PiNS_iff_lemma_3 W T π' 1 x).mp hx
  have hxD : x ∈ DelS W T := hx'.2
  have hxΔ : ∀ δ ∈ W.DelF, W.γD T δ x = x := (DelS_iff_lemma_4 W T x).mp hxD
  obtain ⟨x₁, hx₁, hx₁x⟩ := hx'.1
  have hxN : x ∈ W.N T := by rw [← hx₁x]; exact (W.N T).smul_mem _ hx₁
  rw [hK] at hgx
  have key : ∀ y : ℕ, y ≤ M → x ∈ PiNS W T π' y := by
    intro y
    induction y with
    | zero =>
      intro _
      exact (PiNS_iff_lemma_3 W T π' 0 x).mpr ⟨⟨x, hxN, by simp⟩, hxD⟩
    | succ y ih =>
      intro hyM
      rcases Nat.eq_zero_or_pos y with hy0 | hy0
      · subst hy0; exact hx
      · obtain ⟨⟨r₀, hr₀, hr₀x⟩, -⟩ := (PiNS_iff_lemma_3 W T π' y x).mp (ih (by omega))
        have hr₀Δ : r₀ ∈ W.NΔ T :=
          invLiftPf_quot_Δ W T π' hu hπΔ y r₀ hr₀ (fun δ hδ => by rw [hr₀x]; exact hxΔ δ hδ)
        obtain ⟨d, hd, hdγ⟩ := hγN r₀ hr₀Δ
        have hγr : W.γD T W.gam r₀ = r₀ + π' • d := sub_eq_iff_eq_add'.mp hdγ
        obtain ⟨s, hs⟩ : π' ∣ f ^ y - algebraMap O (LetA O n) c₀ ^ y :=
          (Dvd.intro t ht.symm).trans (sub_dvd_pow_sub_pow _ _ _)
        have hfy : f ^ y = algebraMap O (LetA O n) c₀ ^ y + π' * s := by rw [← hs]; ring
        have hg' := PiNS_anti_lemma_7 W T π' hyM hgx
        obtain ⟨⟨e', he', he'x⟩, -⟩ := (PiNS_iff_lemma_3 W T π' (y + 1) _).mp hg'
        have hγx : W.γD T W.gam x - x = π' ^ y • (algebraMap O (LetA O n) (c₀ ^ y - 1) • r₀ +
            π' • (s • r₀ + f ^ y • d)) := by
          rw [← hr₀x, gamD_smulA_lemma_5, map_pow, hf, hγr, mul_pow, hfy, map_sub, map_pow, map_one]
          set a : LetA O n := algebraMap O (LetA O n) c₀ with ha_def
          have e1 : ∀ (A B A' B' : LetA O n), A = A' → B = B' → A • r₀ + B • d = A' • r₀ + B' • d := by
            intro A B A' B' h1 h2; rw [h1, h2]
          calc _ = (π' ^ y * (a ^ y + π' * s) - π' ^ y) • r₀ + (π' ^ y * (a ^ y + π' * s) * π') • d := by
                  rw [smul_add, sub_smul, smul_smul]; abel
            _ = (π' ^ y * (a ^ y - 1) + π' ^ y * (π' * s)) • r₀ +
                  (π' ^ y * (π' * (a ^ y + π' * s))) • d := e1 _ _ _ _ (by ring) (by ring)
            _ = _ := by
              simp only [smul_add, smul_smul, add_smul, add_assoc, mul_add]
        rw [hγx, pow_succ, ← smul_smul] at he'x
        have h1 := cancel_lemma_6 W T π' hu y _ _ he'x
        have h2 : (c₀ ^ y - 1) • r₀ = π' • (e' - (s • r₀ + f ^ y • d)) := by
          rw [← algebraMap_smul (LetA O n) (c₀ ^ y - 1) r₀, smul_sub, h1]
          abel
        obtain ⟨e, he, hre⟩ := hnz y hy0 (by omega) r₀ hr₀ _
          (Submodule.sub_mem _ he' (Submodule.add_mem _ ((W.N T).smul_mem _ hr₀)
            ((W.N T).smul_mem _ hd))) h2
        refine (PiNS_iff_lemma_3 W T π' (y + 1) x).mpr ⟨⟨e, he, ?_⟩, hxD⟩
        rw [← hr₀x, hre, smul_smul, ← pow_succ]
  exact key M le_rfl

theorem invLiftPf_nzd (π' w : LetA O n) (s' : ℕ) (hw : IsUnit w) (hπ : π' = w * letπ ^ s')
    (ℓ : O) (hℓ : ∀ c : O, ℓ * c = 0 → c = 0)
    (r : ℕ) (b : Fin r → W.DD T) (hbN : ∀ j, b j ∈ W.N T)
    (huniq : ∀ x ∈ W.N T, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j)
    (m : ℕ) (r₀ y : W.DD T) (hr₀ : r₀ ∈ W.N T) (hy : y ∈ W.N T)
    (h : ℓ ^ m • r₀ = π' • y) : ∃ e ∈ W.N T, r₀ = π' • e := by
  classical
  have hℓm : ∀ k : ℕ, ∀ c : O, ℓ ^ k * c = 0 → c = 0 := by
    intro k
    induction k with
    | zero => intro c hc; simpa using hc
    | succ k ih => intro c hc; rw [pow_succ, mul_assoc] at hc; exact hℓ _ (ih _ hc)
  obtain ⟨a, ha, -⟩ := huniq r₀ hr₀
  obtain ⟨cc, hc, -⟩ := huniq y hy
  have hmem : ℓ ^ m • r₀ ∈ W.N T := by
    rw [← algebraMap_smul (LetA O n) (ℓ ^ m) r₀]; exact (W.N T).smul_mem _ hr₀
  have e1 : ℓ ^ m • r₀ = ∑ j, (algebraMap O (LetA O n) (ℓ ^ m) * a j) • b j := by
    rw [ha, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul (LetA O n) (ℓ ^ m), smul_smul]
  have e2 : ℓ ^ m • r₀ = ∑ j, (π' * cc j) • b j := by
    rw [h, hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul]
  have hcoef : (fun j => algebraMap O (LetA O n) (ℓ ^ m) * a j) = fun j => π' * cc j :=
    (huniq _ hmem).unique e1 e2
  have hdiv : ∀ j i, ∃ e : PowerSeries O, a j i = PowerSeries.X ^ s' * e := by
    intro j i
    have h1 : (algebraMap O (LetA O n) (ℓ ^ m) * a j) i = (π' * cc j) i :=
      congrFun (congrFun hcoef j) i
    rw [hπ] at h1
    have h3 : algebraMap O (PowerSeries O) (ℓ ^ m) * a j i =
        (w i * PowerSeries.X ^ s') * cc j i := h1
    have h2 : algebraMap O (PowerSeries O) (ℓ ^ m) * a j i =
        PowerSeries.X ^ s' * (w i * cc j i) := by
      rw [h3]; ring
    have h4 : ∀ d < s', PowerSeries.coeff d (a j i) = 0 := by
      intro d hd
      have h5 : PowerSeries.coeff d (algebraMap O (PowerSeries O) (ℓ ^ m) * a j i) = 0 := by
        rw [h2]; exact PowerSeries.X_pow_dvd_iff.mp (dvd_mul_right _ _) d hd
      rw [← Algebra.smul_def, PowerSeries.coeff_smul, smul_eq_mul] at h5
      exact hℓm m _ h5
    exact PowerSeries.X_pow_dvd_iff.mpr h4
  choose e he using hdiv
  obtain ⟨u, hu⟩ := hw
  have hA : ∀ j, a j = π' * ((↑u⁻¹ : LetA O n) * fun i => e j i) := by
    intro j
    have hx : π' * ((↑u⁻¹ : LetA O n) * fun i => e j i) = letπ ^ s' * fun i => e j i := by
      rw [hπ, ← hu, show ((↑u : LetA O n) * letπ ^ s') * ((↑u⁻¹ : LetA O n) * fun i => e j i)
        = ((↑u : LetA O n) * ↑u⁻¹) * (letπ ^ s' * fun i => e j i) by ring, Units.mul_inv, one_mul]
    rw [hx]
    funext i
    exact he j i
  refine ⟨∑ j, ((↑u⁻¹ : LetA O n) * fun i => e j i) • b j,
    Submodule.sum_mem _ fun j _ => (W.N T).smul_mem _ (hbN j), ?_⟩
  rw [Finset.smul_sum, ha]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, ← hA j]

private theorem letS_mem_lemma (c : ZMod n) (x : W.DD T) :
    x ∈ letS W T c ↔ (letE c : LetA O n) • x = x := by
  unfold letS
  rw [LinearMap.mem_ker]
  simp [sub_eq_zero]

private theorem gam_letE_lemma_2 (g : W.Gam) (c : ZMod n) (x : W.DD T) :
    W.γD T g ((letE c : LetA O n) • x) = (letE c : LetA O n) • W.γD T g x := by
  have e : Formalism.BasicNotions.letγ (W.γ₀ g) (letE c : LetA O n) = letE c := by
    funext i
    show W.γ₀ g ((letE c : LetA O n) i) = (letE c : LetA O n) i
    unfold letE
    by_cases hi : i = c
    · subst hi; simp
    · simp [Pi.single_apply, hi]
  rw [← algebraMap_smul W.EE (letE c : LetA O n) x, W.γD_smul, W.γE_ext, e, algebraMap_smul]

theorem invLiftPf_lift (π' Eπ : LetA O n) (h' M σ : ℕ) (c : ZMod n)
    (hG : GradN W T π' σ M) (hL : NinLam W T Eπ h') :
    ∀ w ∈ InvS W T π' Eπ h' 1 c, ∃ wb ∈ InvS W T π' Eπ h' M c,
      ((PD.p : ℕ) : O) ^ σ • w - wb ∈ PiNS W T π' 1 := by
  intro w hw
  unfold InvS at hw ⊢
  rw [Submodule.mem_inf, Submodule.mem_comap] at hw
  obtain ⟨hwL, hwγ⟩ := hw
  rw [LinearMap.sub_apply, LinearMap.id_apply] at hwγ
  have hwS : w ∈ letS W T c := by
    have h0 := hwL
    unfold LamPS at h0
    exact (Submodule.mem_inf.mp h0).2
  have hzS : W.γD T W.gamK w - w ∈ letS W T c := by
    rw [letS_mem_lemma] at hwS ⊢
    rw [smul_sub, ← gam_letE_lemma_2, hwS]
  obtain ⟨k, hk, hk2⟩ := hG c (W.γD T W.gamK w - w) (Submodule.mem_inf.mpr ⟨hwγ, hzS⟩)
  obtain ⟨hk1, hkS⟩ := Submodule.mem_inf.mp hk
  refine ⟨((PD.p : ℕ) : O) ^ σ • w - k, ?_, ?_⟩
  · rw [Submodule.mem_inf]
    refine ⟨Submodule.sub_mem _ (Submodule.smul_mem _ _ hwL) (hL c ?_), ?_⟩
    · unfold NcS
      refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, hkS⟩
      · have h0 := hk1
        unfold PiNS at h0
        have h1 : k ∈ (W.N T).map (Formalism.MainNotions.DeltaInvariantLattices.smulA W T (π' ^ 1)) := (Submodule.mem_inf.mp h0).1
        obtain ⟨y, hy, hyk⟩ := Submodule.mem_map.mp h1
        rw [← hyk]
        exact (W.N T).smul_mem _ hy
      · have h0 := hk1
        unfold PiNS at h0
        exact (Submodule.mem_inf.mp h0).2
    · rw [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply, map_sub, map_smul]
      convert hk2 using 1
      rw [smul_sub]
      abel
  · rw [sub_sub_cancel]
    exact hk1

end Local

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfA
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.ModelFPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34

section Ser

variable {LL V : Type} [Field LL] [AddCommGroup V] [Module LL V]

theorem finsum_mem_sub {ι : Type} (S : Submodule LL V) (t : ι → V) (ht : ∀ j, t j ∈ S) :
    ∑ᶠ j, t j ∈ S := by
  classical
  by_cases h : (Function.support t).Finite
  · rw [finsum_eq_sum _ h]
    exact Submodule.sum_mem _ fun j _ => ht j
  · rw [finsum_of_infinite_support h]
    exact Submodule.zero_mem _

theorem serMul_eq_sum (g : PowerSeries LL) (f : ℤ → V) (m : ℤ) (hf : ∀ k < m, f k = 0)
    (i : ℤ) (N : ℕ) (hN : i - m < N) :
    serMul g f i = ∑ j ∈ Finset.range N, PowerSeries.coeff j g • f (i - j) := by
  unfold serMul
  apply finsum_eq_sum_of_support_subset
  intro j hj
  simp only [Function.mem_support, Finset.coe_range, Set.mem_Iio] at hj ⊢
  by_contra hjN
  push_neg at hjN
  apply hj
  rw [hf (i - j) (by omega), smul_zero]

theorem serMul_one (f : ℤ → V) (i : ℤ) : serMul (1 : PowerSeries LL) f i = f i := by
  unfold serMul
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_one, hj]

theorem serMul_mem (S : ℤ → Submodule LL V) (hS : Monotone S) (g : PowerSeries LL) (m : ℕ)
    (hg : ∀ j < m, PowerSeries.coeff j g = 0) (f : ℤ → V) (hf : ∀ i, f i ∈ S i) (i : ℤ) :
    serMul g f i ∈ S (i - m) := by
  unfold serMul
  apply finsum_mem_sub
  intro j
  by_cases hj : j < m
  · rw [hg j hj, zero_smul]; exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (hS (by omega) (hf (i - j)))

theorem serMul_inv (S : ℤ → Submodule LL V) (hS : Monotone S) (g : PowerSeries LL) (m : ℕ)
    (hg : ∀ j < m, PowerSeries.coeff j g = 0) (hgm : PowerSeries.coeff m g ≠ 0) (f : ℤ → V)
    (m₀ : ℤ) (hf0 : ∀ k < m₀, f k = 0) (hF : ∀ i, serMul g f (i + m) ∈ S i) (i : ℤ) :
    f i ∈ S i := by
  have key : ∀ i, (∀ i' < i, f i' ∈ S i') → f i ∈ S i := by
    intro i ih
    by_cases hi : i < m₀
    · rw [hf0 i hi]; exact Submodule.zero_mem _
    push_neg at hi
    have hN : i + m - m₀ < (((i + m - m₀).toNat + m + 1 : ℕ) : ℤ) := by omega
    have hsum := serMul_eq_sum g f m₀ hf0 (i + m) ((i + m - m₀).toNat + m + 1) hN
    have hmN : m ∈ Finset.range ((i + m - m₀).toNat + m + 1) := Finset.mem_range.mpr (by omega)
    rw [← Finset.add_sum_erase _ _ hmN] at hsum
    have hrest : ∑ j ∈ (Finset.range ((i + m - m₀).toNat + m + 1)).erase m,
        PowerSeries.coeff j g • f (i + m - j) ∈ S i := by
      refine Submodule.sum_mem _ fun j hj => ?_
      have hjm : j ≠ m := Finset.ne_of_mem_erase hj
      rcases Nat.lt_or_gt_of_ne hjm with hlt | hgt
      · rw [hg j hlt, zero_smul]; exact Submodule.zero_mem _
      · exact Submodule.smul_mem _ _ (hS (by omega) (ih _ (by omega)))
    have hmain : PowerSeries.coeff m g • f i ∈ S i := by
      have h1 := hF i
      rw [hsum] at h1
      have h2 := Submodule.sub_mem _ h1 hrest
      simp only [add_sub_cancel_right] at h2
      simpa using h2
    exact (Submodule.smul_mem_iff _ hgm).mp hmain
  have hall : ∀ n : ℕ, ∀ i, i < m₀ + n → f i ∈ S i := by
    intro n
    induction n with
    | zero =>
      intro i hi
      rw [hf0 i (by simpa using hi)]
      exact Submodule.zero_mem _
    | succ n ihn =>
      intro i hi
      apply key
      intro i' hi'
      exact ihn i' (by push_cast at hi; omega)
  exact hall ((i - m₀).toNat + 1) i (by omega)

end Ser

section Lev

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem lev_letE (c : ZMod n) (ζ : LL) : W.lev c ζ (letE c : LetA O n) = 1 := by
  have h1 : W.lev c ζ (1 - letE c : LetA O n) = 0 :=
    W.lev_letter c ζ _ (by simp [letE])
  rw [map_sub, map_one, sub_eq_zero] at h1
  exact h1.symm

theorem levN_eq_serMul (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) (a : LetA O n) (x : ↥(W.N T))
    (k : ℤ) : W.levN T c ζ (a • x) k = serMul (W.lev c ζ a) (W.levN T c ζ x) k :=
  W.levN_smul T c ζ a x k

theorem levN_letE (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ) :
    W.levN T c ζ ((letE c : LetA O n) • x) k = W.levN T c ζ x k := by
  rw [levN_eq_serMul, lev_letE, serMul_one]

theorem Q_eq_q (hs : W.s = 1) : W.Q = W.q := by
  show (W.φA ^ (W.s - 1)) W.q = W.q
  rw [hs, Nat.sub_self, pow_zero]
  rfl

theorem levQ_pt (hs : W.s = 1) (i : ZMod n) (ζ : LL) (hζ : ζ ^ PD.p = 1) (hζ1 : ζ ≠ 1) :
    PowerSeries.constantCoeff (W.lev i ζ W.Q) = 0 ∧ PowerSeries.coeff 1 (W.lev i ζ W.Q) ≠ 0 := by
  have : Fact PD.p.Prime := ⟨PD.hp⟩
  have hprim : IsPrimitiveRoot ζ (PD.p ^ 1) := by
    have h := IsPrimitiveRoot.orderOf ζ
    rw [orderOf_eq_prime hζ hζ1] at h
    rwa [pow_one]
  obtain ⟨E, hE0, hED, hE⟩ := W.lev_π i ζ ⟨1, hprim⟩
  have hprod : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
    funext j
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.add_apply, Pi.one_apply, letπ,
      LocWach.q]
    exact W.q₀_def
  have hl := congrArg (W.lev i ζ) hprod
  rw [map_mul, map_sub, map_pow, map_add (f := _), map_one, hE] at hl
  rw [Q_eq_q W hs]
  have hp0 : (PD.p : LL) ≠ 0 := by
    intro h
    have := W.v_l
    rw [h, AddValuation.map_zero] at this
    exact WithTop.top_ne_coe this
  have ha0 : PowerSeries.constantCoeff (W.lev i ζ letπ) = ζ - 1 := by
    have h := congrArg PowerSeries.constantCoeff hE
    rw [map_add (f := _), map_one, map_mul, PowerSeries.constantCoeff_C, hE0, mul_one] at h
    linear_combination h
  have hz : ζ - 1 ≠ 0 := sub_ne_zero.2 hζ1
  have hc0 : PowerSeries.constantCoeff (W.lev i ζ W.q) = 0 := by
    have h := congrArg PowerSeries.constantCoeff hl
    rw [map_mul, map_sub, map_one, map_pow, map_mul, PowerSeries.constantCoeff_C, hE0, mul_one,
      hζ, sub_self, ha0] at h
    exact (mul_eq_zero.1 h).resolve_left hz
  refine ⟨hc0, ?_⟩
  obtain ⟨b', hb'⟩ := PowerSeries.X_dvd_iff.2 hc0
  have hEp : PowerSeries.coeff 1 (E ^ PD.p) = (PD.p : LL) := by
    have hd : PowerSeries.derivative (R := LL) (E ^ PD.p) = (PD.p : LL) • E ^ PD.p := by
      rw [Derivation.leibniz_pow, hED, smul_eq_mul, ← pow_succ, Nat.sub_add_cancel PD.hp.one_lt.le,
        Nat.cast_smul_eq_nsmul]
    have h := congrArg (PowerSeries.coeff 0) hd
    have hc : PowerSeries.coeff 0 (E ^ PD.p) = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hE0, one_pow]
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_smul, hc] at h
    simpa using h
  have h1 := congrArg (PowerSeries.coeff 1) hl
  rw [hb', mul_left_comm, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_mul, ha0, mul_pow, ← map_pow, hζ, map_one, one_mul, map_sub, hEp, PowerSeries.coeff_one,
    if_neg one_ne_zero, sub_zero] at h1
  rw [hb', PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  intro h0
  rw [h0, mul_zero] at h1
  exact hp0 h1.symm

end Lev

end Formalism.MainNotions.N.Ln34.ModelFPf

end
end

