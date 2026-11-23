module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0122
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0230

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationFrobeniusMemUpToQPower
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.PhiSat

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem φD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (y : W.DD T) :
    W.φD T (a • y) = W.φA a • W.φD T y := by
  have := W.φD_smul T (algebraMap (LetA O n) W.EE a) y
  rw [algebraMap_smul, W.φE_ext, algebraMap_smul] at this
  exact this

theorem φD_map_Q {T₁ T₂ : LocLat G Qp LL O} (π : LatHom T₁.L T₂.L) (y : W.DD T₂)
    (hy : y ∈ (W.N T₁).map (mapA W π)) : ∃ j : ℕ, W.Q ^ j • W.φD T₂ y ∈ (W.N T₁).map (mapA W π) := by
  obtain ⟨n₁, hn₁, rfl⟩ := hy
  obtain ⟨j, hj⟩ := W.N_φ T₁ n₁ hn₁
  refine ⟨j, W.Q ^ j • W.φD T₁ n₁, hj, ?_⟩
  rw [map_smul]
  congr 1
  exact W.map_φ π n₁

theorem φD_satM_gen (l : ℕ) (hlp : l.Prime) (hp : PD.p = l) {T₁ T₂ : LocLat G Qp LL O}
    (π : LatHom T₁.L T₂.L) (x : W.DD T₂)
    (hx : x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) :
    ∃ k : ℕ, W.Q ^ k • W.φD T₂ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂) := by
  set N'' := (W.N T₁).map (mapA W π) with hN''
  obtain ⟨hxN, k, hk1, hk2⟩ := hx
  let J : Ideal (LetA O n) :=
    { carrier := {a | ∃ j : ℕ, W.Q ^ j • a • W.φD T₂ x ∈ N''}
      add_mem' := by
        rintro a b ⟨i, hi⟩ ⟨j, hj⟩
        refine ⟨i + j, ?_⟩
        rw [add_smul, smul_add, pow_add]
        refine N''.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact N''.smul_mem _ hi
        · rw [mul_smul]; exact N''.smul_mem _ hj
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨j, hj⟩
        refine ⟨j, ?_⟩
        rw [smul_eq_mul, mul_smul, smul_comm]
        exact N''.smul_mem c hj }
  have hJ : ∀ (a : LetA O n) (j : ℕ), W.Q ^ j • a • W.φD T₂ x ∈ N'' → ∀ (b : LetA O n) (E : ℕ), j ≤ E →
      W.Q ^ E • (b * a) • W.φD T₂ x ∈ N'' := by
    intro a j hj b E hjE
    have : W.Q ^ E • (b * a) • W.φD T₂ x = (W.Q ^ (E - j) * b) • (W.Q ^ j • a • W.φD T₂ x) := by
      rw [smul_smul, smul_smul, smul_smul]
      congr 1
      conv_lhs => rw [← Nat.sub_add_cancel hjE, pow_add]
      ring
    rw [this]
    exact N''.smul_mem _ hj
  have hl : ((l : ℕ) : LetA O n) ^ k ∈ J := by
    obtain ⟨j, hj⟩ := φD_map_Q W π _ hk1
    refine ⟨j, ?_⟩
    rw [φD_smulA, map_pow, map_natCast] at hj
    exact hj
  have hπq : (letπ * W.q) ^ k ∈ J := by
    obtain ⟨j, hj⟩ := φD_map_Q W π _ hk2
    refine ⟨j, ?_⟩
    rw [φD_smulA, map_pow, W.φA_π] at hj
    exact hj
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hlp (letπ : LetA O n) 1
  have hq : letπ * W.q = (letπ + 1 : LetA O n) ^ l - 1 := by
    funext i
    have := W.q₀_def
    rw [hp] at this
    simp [letπ, LocWach.q, this, add_comm]
  have hπl : (letπ : LetA O n) ^ l = letπ * W.q - (l : LetA O n) * (letπ * r) := by
    rw [hq, hr]; ring
  have hrad : (letπ : LetA O n) ^ l ∈ J.radical := by
    rw [hπl]
    refine Ideal.sub_mem _ (Ideal.mem_radical_of_pow_mem (Ideal.le_radical hπq)) ?_
    exact Ideal.mul_mem_right _ _ (Ideal.mem_radical_of_pow_mem (Ideal.le_radical hl))
  obtain ⟨m, j₁, hj₁⟩ := hrad
  obtain ⟨j₂, hj₂⟩ := hl
  obtain ⟨a, ha⟩ := W.N_φ T₂ x hxN
  change W.Q ^ a • W.φD T₂ x ∈ W.N T₂ at ha
  refine ⟨a + j₁ + j₂, ?_, k + l * m, ?_, ?_⟩
  · rw [add_assoc, pow_add, mul_comm, mul_smul]
    exact (W.N T₂).smul_mem _ ha
  · have := hJ _ j₂ hj₂ ((l : LetA O n) ^ (l * m)) (a + j₁ + j₂) (by omega)
    rw [← pow_add, Nat.add_comm (l * m) k] at this
    rw [smul_comm]
    exact this
  · have := hJ _ j₁ hj₁ ((letπ : LetA O n) ^ k) (a + j₁ + j₂) (by omega)
    rw [← pow_mul, ← pow_add] at this
    rw [smul_comm]
    exact this

theorem φD_satM_Q : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → ∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), ∃ k : ℕ, W.Q ^ k • W.φD T₂ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂) := by
  intro D HW F l _ K s LL h W T₁ T₂ π _hc₁ _hc₂ x hx
  exact φD_satM_gen W l Fact.out ((D.loc l).PD_p K) π x hx

end GlobalTheory.NL.PhiSat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationGammaStableAndSubOneMemPiSmul
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.GamSat

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem γ_smul (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.γ T (a • x) = W.γA W.gam a • W.γ T x := by
  have := W.γD_smul T W.gam (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem γA_π (g : W.Gam) : ∃ u u' : LetA O n, u * u' = 1 ∧ W.γA g letπ = letπ * u := by
  obtain ⟨h0, h1⟩ := W.γ₀_X g
  obtain ⟨u₀, hu₀⟩ := PowerSeries.X_dvd_iff.mpr h0
  have hc : PowerSeries.constantCoeff u₀ = ((W.χΓ g : Oˣ) : O) := by
    rw [← h1, hu₀, PowerSeries.coeff_succ_X_mul]
    simp
  refine ⟨fun _ => u₀, fun _ => PowerSeries.invOfUnit u₀ (W.χΓ g), ?_, ?_⟩
  · funext i
    exact PowerSeries.mul_invOfUnit u₀ _ hc
  · funext i
    simp [LocWach.γA, letγ, letπ, hu₀]

theorem map_γ_mem {T₁ T₂ : LocLat G Qp LL O} (π : LatHom T₁.L T₂.L) :
    ∀ y ∈ (W.N T₁).map (mapA W π), W.γ T₂ y ∈ (W.N T₁).map (mapA W π) := by
  rintro _ ⟨n₁, hn₁, rfl⟩
  refine ⟨W.γD T₁ W.gam n₁, W.N_Γ T₁ W.gam n₁ hn₁, ?_⟩
  change W.map π (W.γD T₁ W.gam n₁) = W.γD T₂ W.gam (W.map π n₁)
  exact W.map_γ π W.gam n₁

theorem pow_smul_γ_mem (T : LocLat G Qp LL O) (P : Submodule (LetA O n) (W.DD T))
    (hP : ∀ y ∈ P, W.γ T y ∈ P) (p k : ℕ) (x : W.DD T)
    (h1 : ((p : LetA O n)) ^ k • x ∈ P) (h2 : (letπ : LetA O n) ^ k • x ∈ P) :
    ((p : LetA O n)) ^ k • W.γ T x ∈ P ∧ (letπ : LetA O n) ^ k • W.γ T x ∈ P := by
  constructor
  · have := hP _ h1
    rw [γ_smul, map_pow, map_natCast] at this
    exact this
  · obtain ⟨u, u', huu, hu⟩ := γA_π W W.gam
    have := P.smul_mem (u' ^ k) (hP _ h2)
    have e : u' ^ k * (letπ * u) ^ k = letπ ^ k := by
      rw [← mul_pow, mul_left_comm, mul_comm u' u, huu, mul_one]
    rw [γ_smul, map_pow, hu, smul_smul, e] at this
    exact this

theorem gam_sat (p : ℕ) (T₁ T₂ : LocLat G Qp LL O) (π : LatHom T₁.L T₂.L) :
    (∀ x ∈ GlobalTheory.NL.Coker.satM p ((W.N T₁).map (mapA W π)) (W.N T₂),
      W.γ T₂ x ∈ GlobalTheory.NL.Coker.satM p ((W.N T₁).map (mapA W π)) (W.N T₂)) ∧
    ∀ x ∈ GlobalTheory.NL.Coker.satM p ((W.N T₁).map (mapA W π)) (W.N T₂),
      W.γ T₂ x - x ∈ (GlobalTheory.NL.Coker.satM p ((W.N T₁).map (mapA W π)) (W.N T₂)).map
        (smulA W T₂ letπ) := by
  set P := (W.N T₁).map (mapA W π) with hPdef
  have hP := map_γ_mem W π
  refine ⟨?_, ?_⟩
  · rintro x ⟨hx, k, h1, h2⟩
    exact ⟨W.N_Γ T₂ W.gam x hx, k, pow_smul_γ_mem W T₂ P hP p k x h1 h2⟩
  · rintro x ⟨hx, k, h1, h2⟩
    obtain ⟨y, hy, hxy⟩ := W.N_π T₂ W.gam x hx
    obtain ⟨n₁, hn₁, hn₁x⟩ := h1
    obtain ⟨m₁, hm₁, hnm⟩ := W.N_π T₁ W.gam n₁ hn₁
    have hγ := pow_smul_γ_mem W T₂ P hP p k x ⟨n₁, hn₁, hn₁x⟩ h2

    have hinj : ∀ z w : W.DD T₂, (letπ : LetA O n) • z = (letπ : LetA O n) • w → z = w := by
      intro z w hzw
      obtain ⟨u, hu⟩ := W.EE_π
      rw [← algebraMap_smul W.EE (letπ : LetA O n) z, ← algebraMap_smul W.EE (letπ : LetA O n) w,
        ← hu] at hzw
      have := congrArg (fun z => ((u⁻¹ : W.EEˣ) : W.EE) • z) hzw
      simpa [smul_smul] using this
    have hly : ((p : LetA O n)) ^ k • y = mapA W π m₁ := by
      apply hinj
      rw [smul_comm, ← hxy, smul_sub, ← LinearMap.map_smul, ← hnm]
      have e1 : W.γD T₂ W.gam (((p : LetA O n)) ^ k • x) = ((p : LetA O n)) ^ k • W.γD T₂ W.gam x := by
        have := γ_smul W T₂ (((p : LetA O n)) ^ k) x
        rw [map_pow, map_natCast] at this
        exact this
      rw [← e1, ← hn₁x]
      change W.γD T₂ W.gam (W.map π n₁) - W.map π n₁ = W.map π (W.γD T₁ W.gam n₁ - n₁)
      rw [map_sub, W.map_γ]
    refine ⟨y, ⟨hy, k + 1, ?_, ?_⟩, ?_⟩
    · rw [pow_succ', mul_smul, hly]
      exact P.smul_mem _ ⟨m₁, hm₁, rfl⟩
    · rw [pow_succ, mul_smul, ← hxy, smul_sub]
      exact P.sub_mem hγ.2 h2
    · change (letπ : LetA O n) • y = _
      rw [← hxy]
      rfl

end Generic

theorem wachSaturation_gamma_stable_and_sub_one_mem_pi_smul : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → (∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), W.γ T₂ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) ∧ ∀ x ∈ GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂), W.γ T₂ x - x ∈ (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)).map (smulA W T₂ letπ) := by
  intro D HW F l _ K s LL h W T₁ T₂ π _ _
  exact gam_sat W l T₁ T₂ π

end GlobalTheory.NL.GamSat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Xstab
section
noncomputable section

namespace GlobalTheory.NL.XStab

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem γD_smulA (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem φpow_γA (k : ℕ) (g : W.Gam) (a : LetA O n) :
    (W.φA ^ k) (W.γA g a) = W.γA g ((W.φA ^ k) a) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', AlgHom.mul_apply, AlgHom.mul_apply, ih, W.φA_γA]

theorem X_dvd_γX (g : W.Gam) : W.X ∣ W.γA g W.X := by
  obtain ⟨c, hc⟩ : (PowerSeries.X : PowerSeries O) ∣ W.γ₀ g PowerSeries.X :=
    PowerSeries.X_dvd_iff.2 (W.γ₀_X g).1
  have h1 : W.γA g letπ = letπ * (fun _ => c) := by
    funext i
    simp [LocWach.γA, letγ, letπ, hc]
  refine ⟨(W.φA ^ (W.s - 1)) (fun _ => c), ?_⟩
  rw [LocWach.X, ← φpow_γA, h1, map_mul]

theorem γD_mem_aN_X (T : LocLat G Qp LL O) (δ : W.Gam) (x : W.DD T) (hx : x ∈ aN W T W.X) :
    W.γD T δ x ∈ aN W T W.X := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨c, hc⟩ := X_dvd_γX W δ
  refine ⟨c • W.γD T δ y, (W.N T).smul_mem _ (W.N_Γ T δ y hy), ?_⟩
  change W.X • c • W.γD T δ y = W.γD T δ (W.X • y)
  rw [γD_smulA, hc, mul_smul]

end Generic

theorem xstab : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (δ : ((HW l).W K s LL h).Gam) (x : ((HW l).W K s LL h).DD T), x ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X → ((HW l).W K s LL h).γD T δ x ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X :=
  fun _ HW l _ K s LL h T δ x hx => γD_mem_aN_X ((HW l).W K s LL h) T δ x hx

end GlobalTheory.NL.XStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlSpanImageContinuousRepFinite
section
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory

theorem zl_span_image_finite : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous r → ∃ t : Finset Γ, ∀ f : Γ →₀ ℤ_[l], ∃ f' : Γ →₀ ℤ_[l], f'.support ⊆ t ∧ (f.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) = (f'.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) := by
  intro l _ Γ _ _ _ _ a r hr
  classical
  obtain ⟨L, hLfin, hL⟩ := _root_.GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem_of_continuous l Γ a r hr
  let ρ : Γ → Matrix (Fin a) (Fin a) (PadicAlgCl l) := fun g => ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))
  have hρ : Continuous ρ := Units.continuous_val.comp hr
  let e : Matrix (Fin a) (Fin a) L →ₗ[ℚ_[l]] Matrix (Fin a) (Fin a) (PadicAlgCl l) :=
    LinearMap.mapMatrix L.val.toLinearMap
  let V := LinearMap.range e
  haveI : FiniteDimensional ℚ_[l] V := LinearMap.finiteDimensional_range e
  have hρV : ∀ g, ρ g ∈ V := fun g => ⟨fun i j => ⟨ρ g i j, hL g i j⟩, by ext i j; rfl⟩
  let ρV : Γ → V := fun g => ⟨ρ g, hρV g⟩
  have hρVc : Continuous ρV := hρ.subtype_mk _
  let b := Module.finBasis ℚ_[l] V
  let φ : V →ₗ[ℚ_[l]] (Fin (Module.finrank ℚ_[l] V) → ℚ_[l]) := b.equivFun.toLinearMap
  have hφinj : Function.Injective φ := b.equivFun.injective
  have hφ : Continuous φ := LinearMap.continuous_of_finiteDimensional φ
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hφ.comp hρVc).continuousOn
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm ℚ_[l] C
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1 (Set.mem_univ _))
  have hcpos : 0 < ‖c‖ := lt_of_le_of_lt hC0 hc
  have hc0 : c ≠ 0 := norm_pos_iff.mp hcpos
  have hbd : ∀ g i, ‖c⁻¹ * φ (ρV g) i‖ ≤ 1 := by
    intro g i
    rw [norm_mul, norm_inv]
    have h1 := (norm_le_pi_norm (φ (ρV g)) i).trans (hC g (Set.mem_univ _))
    rw [inv_mul_le_iff₀ hcpos]
    linarith
  let ψ : Γ → (Fin (Module.finrank ℚ_[l] V) → ℤ_[l]) := fun g i => ⟨c⁻¹ * φ (ρV g) i, hbd g i⟩
  obtain ⟨G, hG⟩ : (Submodule.span ℤ_[l] (Set.range ψ)).FG := IsNoetherian.noetherian _
  have hGT : ∀ x ∈ G, ∃ T : Finset (Fin (Module.finrank ℚ_[l] V) → ℤ_[l]),
      ↑T ⊆ Set.range ψ ∧ x ∈ Submodule.span ℤ_[l] (T : Set _) := fun x hx =>
    Submodule.mem_span_finite_of_mem_span (hG ▸ Submodule.subset_span hx)
  choose T hT1 hT2 using hGT
  let U := G.attach.biUnion (fun x => T x.1 x.2)
  have hU : ∀ y ∈ U, ∃ g, ψ g = y := by
    intro y hy
    obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.mp hy
    exact hT1 x.1 x.2 hx
  let t : Finset Γ := U.image (fun y => if h : ∃ g, ψ g = y then h.choose else 1)
  refine ⟨t, ?_⟩
  have hspan : Submodule.span ℤ_[l] (Set.range ψ) ≤ Submodule.span ℤ_[l] (ψ '' (t : Set Γ)) := by
    rw [← hG, Submodule.span_le]
    intro x hx
    refine Submodule.span_mono ?_ (hT2 x hx)
    intro y hy
    have hyU : y ∈ U := Finset.mem_biUnion.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, hy⟩
    have hex : ∃ g, ψ g = y := hU y hyU
    refine ⟨hex.choose, ?_, hex.choose_spec⟩
    simp only [t, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨y, hyU, by rw [dite_eq_left hex]⟩

  let A : (Γ →₀ ℤ_[l]) → V := fun f => f.sum fun h c' => ((c' : ℚ_[l])) • ρV h
  have hSM : ∀ f : Γ →₀ ℤ_[l], (f.sum fun h c' => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c' : ℚ_[l])) • ρ h) = ((A f : V) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) := by
    intro f
    simp only [A, Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul, algebraMap_smul]
    rfl
  have hLC : ∀ f : Γ →₀ ℤ_[l], ∀ i, ((Finsupp.linearCombination ℤ_[l] ψ f i : ℤ_[l]) : ℚ_[l]) = c⁻¹ * φ (A f) i := by
    intro f i
    have hcs : ∀ F : Γ → ℤ_[l], ((∑ x ∈ f.support, F x : ℤ_[l]) : ℚ_[l]) = ∑ x ∈ f.support, (F x : ℚ_[l]) :=
      fun F => map_sum PadicInt.Coe.ringHom F f.support
    rw [Finsupp.linearCombination_apply]
    unfold Finsupp.sum
    simp only [A]
    unfold Finsupp.sum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_apply, hcs, map_sum, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, PadicInt.coe_mul]
    simp only [ψ]
    ring
  intro f
  have hx : Finsupp.linearCombination ℤ_[l] ψ f ∈ Submodule.span ℤ_[l] (ψ '' (t : Set Γ)) :=
    hspan (Finsupp.mem_span_range_iff_exists_finsupp.mpr ⟨f, rfl⟩)
  obtain ⟨f', hf'sup, hf'⟩ := (Finsupp.mem_span_image_iff_linearCombination ℤ_[l]).mp hx
  refine ⟨f', ?_, ?_⟩
  · rw [Finsupp.mem_supported] at hf'sup
    exact_mod_cast hf'sup
  · show (f.sum fun h c' => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c' : ℚ_[l])) • ρ h) = (f'.sum fun h c' => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c' : ℚ_[l])) • ρ h)
    rw [hSM, hSM]
    congr 1
    apply hφinj
    funext i
    have h1 := hLC f i
    have h2 := hLC f' i
    rw [hf'] at h2
    have : c⁻¹ * φ (A f) i = c⁻¹ * φ (A f') i := h1.symm.trans h2
    exact mul_left_cancel₀ (inv_ne_zero hc0) this

end GlobalTheory
end

