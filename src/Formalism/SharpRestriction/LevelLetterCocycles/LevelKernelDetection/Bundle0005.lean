module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0027
public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.Bundle0003
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.VSumPowNonneg
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0029
public import Mathlib.NumberTheory.Padics.Hensel

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.CombineProd
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G

section Alg

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]

theorem combine_two (a b l u w : R) (k : ℕ) (hl : u * a + w * b = l ^ k) (y y₁ y₂ : V)
    (ha : y = a • y₁) (hb : y = b • y₂) :
    l ^ k • y = (a * b) • (u • y₂ + w • y₁) := by
  have e1 : (u * a) • y = (a * b * u) • y₂ := by
    rw [hb, smul_smul]
    congr 1
    ring
  have e2 : (w * b) • y = (a * b * w) • y₁ := by
    rw [ha, smul_smul]
    congr 1
    ring
  rw [← hl, add_smul, e1, e2, smul_add, smul_smul, smul_smul]

theorem combine_pow (l x y : R) (hl : l ∈ Ideal.span ({x, y} : Set R)) (a b : ℕ) :
    l ^ (a + b) ∈ Ideal.span ({x ^ a, y ^ b} : Set R) := by
  obtain ⟨u, w, huw⟩ := Ideal.mem_span_pair.1 hl
  rw [← huw]
  refine Ideal.add_pow_mem_of_pow_mem_of_le (m := a) (n := b) (k := a + b) _ ?_ ?_ (by omega)
  · rw [mul_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · rw [mul_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

theorem combine_prod (l q : R) (a : ℕ → R) (m : ℕ)
    (h : ∀ s < m, ∃ j : ℕ, l ^ j ∈ Ideal.span ({a s, q} : Set R)) :
    ∃ j : ℕ, l ^ j ∈ Ideal.span ({∏ s ∈ Finset.range m, a s, q} : Set R) := by
  induction m with
  | zero =>
    refine ⟨0, Ideal.subset_span ?_⟩
    simp
  | succ m ih =>
    obtain ⟨j₁, h₁⟩ := ih (fun s hs => h s (by omega))
    obtain ⟨j₂, h₂⟩ := h m (by omega)
    obtain ⟨u₁, w₁, e₁⟩ := Ideal.mem_span_pair.1 h₁
    obtain ⟨u₂, w₂, e₂⟩ := Ideal.mem_span_pair.1 h₂
    refine ⟨j₁ + j₂, Ideal.mem_span_pair.2 ⟨u₁ * u₂,
      u₁ * (∏ s ∈ Finset.range m, a s) * w₂ + w₁ * u₂ * a m + w₁ * w₂ * q, ?_⟩⟩
    rw [Finset.prod_range_succ, pow_add, ← e₁, ← e₂]
    ring

theorem combine_mod (N : Submodule R V) (l : R) (p : ℕ → R)
    (hcop : ∀ s s' : ℕ, s ≠ s' → l ∈ Ideal.span ({p s, p s'} : Set R)) (E : ℕ → ℕ) (y : V)
    (hy : y ∈ N) (ell : ℕ) (h : ∀ s < ell, ∃ y' ∈ N, y = p s ^ E s • y') :
    ∃ K : ℕ, ∃ z ∈ N, l ^ K • y = (∏ s ∈ Finset.range ell, p s ^ E s) • z := by
  induction ell with
  | zero => exact ⟨0, y, hy, by simp⟩
  | succ m ih =>
    obtain ⟨K, z, hz, hK⟩ := ih (fun s hs => h s (by omega))
    obtain ⟨y₂, hy₂, e₂⟩ := h m (by omega)
    obtain ⟨j, hj⟩ := combine_prod l (p m ^ E m) (fun s => p s ^ E s) m
      (fun s hs => ⟨E s + E m, combine_pow l (p s) (p m) (hcop s m (by omega)) (E s) (E m)⟩)
    obtain ⟨u, w, huw⟩ := Ideal.mem_span_pair.1 hj
    have e := combine_two (∏ s ∈ Finset.range m, p s ^ E s) (p m ^ E m) l u w j huw
      (l ^ K • y) z (l ^ K • y₂) hK (by rw [e₂, smul_comm])
    refine ⟨j + K, u • l ^ K • y₂ + w • z,
      N.add_mem (N.smul_mem _ (N.smul_mem _ hy₂)) (N.smul_mem _ hz), ?_⟩
    rw [Finset.prod_range_succ, pow_add, mul_smul, e]

end Alg

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}

theorem combine_cop [IsDomain O] (hR : Ring9 W) (s s' : ℕ) (hss : s ≠ s') :
    PowerSeries.C (((PD.p : ℕ) : O)) ∈
      Ideal.span ({(baseIdOf hR).Bs.p s, (baseIdOf hR).Bs.p s'} : Set (PowerSeries O)) := by
  obtain ⟨u, hu⟩ := frobenius_uniformizer_identity hR
  have h2 := PD.hp.two_le
  have hℓ : (baseIdOf hR).Bs.ℓ = PD.p := rfl
  have hdvd : (PowerSeries.X * (PowerSeries.X + PowerSeries.C (((baseIdOf hR).Bs.ℓ : ℕ) : O)) :
      PowerSeries O) ∣ (baseIdOf hR).Bs.φ PowerSeries.X := by
    refine ⟨(u : PowerSeries O) * (baseIdOf hR).Bs.q ^ ((baseIdOf hR).Bs.ℓ - 2), ?_⟩
    rw [hu]
    have e : (baseIdOf hR).Bs.ℓ - 1 = ((baseIdOf hR).Bs.ℓ - 2) + 1 := by rw [hℓ]; omega
    rw [e, pow_succ]
    change _ = PowerSeries.X * (baseIdOf hR).Bs.q * _
    ring
  exact (LevelStatements.Lv.psCoprime O (baseIdOf hR).Bs.ℓ (baseIdOf hR).Bs.φ hdvd).2 s s' hss

theorem combine [IsDomain O] (hSat : Sat W) (hcrys : IsCrys PD T.ρ) (ell : ℕ) (E : ℕ → ℕ) (y : C.V)
    (hy : y ∈ (latOf C).N c)
    (h : ∀ s < ell, ∃ y' ∈ (latOf C).N c, y = (baseIdOf hR).Bs.p s ^ E s • y') :
    ∃ y' ∈ (latOf C).N c, y = (∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ E s) • y' := by
  set κ : PowerSeries O := ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ E s with hκ
  obtain ⟨K, z, hz, hK⟩ := combine_mod ((latOf C).N c) (PowerSeries.C (((PD.p : ℕ) : O)))
    (fun s => (baseIdOf hR).Bs.p s) (combine_cop hR) E y hy ell h
  have hd : (baseIdOf hR).d κ = ∏ s ∈ Finset.range ell, pS W s ^ E s := by
    rw [hκ, map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_pow, BaseId.d_p]
  have hdl : (baseIdOf hR).d (PowerSeries.C (((PD.p : ℕ) : O)) ^ K) =
      ((PD.p : ℕ) : LetA O n) ^ K := by
    rw [map_pow, BaseId.d_C, map_natCast]
  have hNΔ : ∀ x : W.DD T, x ∈ W.N T → (∀ δ ∈ W.DelF, W.γD T δ x = x) → x ∈ W.NΔ T :=
    fun x h1 h2 => ⟨h1, h2⟩
  have hx : C.t c y ∈ mulSet W T ((baseIdOf hR).d κ) (W.NΔ T) := by
    refine hSat T ((baseIdOf hR).d κ) 1 hcrys ⟨0, (baseIdOf hR).d κ, ⟨E, ell, hd⟩, by simp⟩
      ⟨0, 1, ⟨fun _ => 0, 0, by simp⟩, by simp⟩ (C.t c y) (fun δ hδ => C.t_Δ c y δ hδ) ?_ ?_
    · rw [one_smul]
      exact hNΔ _ hy (fun δ hδ => C.t_Δ c y δ hδ)
    · refine ⟨K, C.t c z, hNΔ _ hz (fun δ hδ => C.t_Δ c z δ hδ), ?_⟩
      rw [← hdl, ← Coord.t_smul, hK, Coord.t_smul]
  obtain ⟨z', hz', hxz⟩ := hx
  have hlet : (letE c : LetA O n) • ((letE c : LetA O n) • z') = (letE c : LetA O n) • z' := by
    rw [smul_smul, letE_mul_self]
  have hΔ : ∀ δ ∈ W.DelF, W.γD T δ ((letE c : LetA O n) • z') = (letE c : LetA O n) • z' := by
    intro δ hδ
    rw [Formalism.MainNotions.WachCoordinates.Br.γD_smulA, γA_letE, hz'.2 δ hδ]
  obtain ⟨y'', hy''⟩ := C.t_surj c _ hlet hΔ
  refine ⟨y'', ?_, ?_⟩
  · show C.t c y'' ∈ W.N T
    rw [hy'']
    exact (W.N T).smul_mem _ hz'.1
  · apply C.t_inj c
    rw [Coord.t_smul, hy'', smul_smul, mul_comm, ← smul_smul, ← hxz, C.t_letter]

end Formalism.MainNotions.N.Ln03.K8

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.CrystallineToDeRhamInjective
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03
open Formalism.MainNotions.N.Ln03.Pf.ConvolutionAlt

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W}

theorem crystalline_to_deRham_injective (T : LocLat G Qp LL O) : Function.Injective (ιV PD (LL := LL) (V := T.V)) := by
  have h : ∀ y, ιV PD (LL := LL) (V := T.V) y =
      ((PD.ι.toLinearMap.restrictScalars Qp).lTensor T.V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [ιV]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hi : Function.Injective (PD.ι.toLinearMap.restrictScalars Qp) := PD.ι_inj
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hi hab

theorem levelExpansion_smul
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (a : LetA O n) (x : ↥(W.N T)) (k : ℤ) :
    Lb.levB T i ζ (a • x) k = cv (W.lev i ζ a) (Lb.levB T i ζ x) k := by
  obtain ⟨m, hm⟩ := Lb.supp T i ζ x
  apply crystalline_to_deRham_injective (PD := PD) (LL := LL) T
  rw [← levN_eq, W.levN_smul, cv_map _ _ _ m hm]
  unfold cv
  congr 1
  funext j
  rw [levN_eq]

theorem level_pi_constantCoeff_zero (i : ZMod n) :
    PowerSeries.constantCoeff (W.lev i 1 (letπ : LetA O n)) = 0 := by
  obtain ⟨E, hE0, -, hE⟩ := W.lev_π i 1 ⟨0, by simp⟩
  have h := congrArg PowerSeries.constantCoeff hE
  simp only [map_add (f := _), map_mul, hE0, mul_one, map_one] at h
  linear_combination h

theorem levelExpansion_neg_eq_zero
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (hs1 : W.s = 1) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (T : LocLat G Qp LL O)
    (hP4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) (i : ZMod n) (x : ↥(W.N T)) (k : ℤ) (hk : k < 0) :
    Lb.levB T i 1 x k = 0 := by
  have hX : PowerSeries.constantCoeff (W.lev i 1 W.X) = 0 := by
    have : W.X = (letπ : LetA O n) := by
      show (W.φA ^ (W.s - 1)) _ = _
      rw [hs1, Nat.sub_self, pow_zero]
      rfl
    rw [this]
    exact level_pi_constantCoeff_zero (W := W) i
  apply crystalline_to_deRham_injective (PD := PD) (LL := LL) T
  rw [← levN_eq, map_zero]
  exact ((hP4.1 i 1 ⟨0, by simp⟩ hX).1 x k).2 hk

theorem level_pi0_X_pow_dvd
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (i : ZMod n) : (PowerSeries.X : PowerSeries LL) ^ (PD.p - 1) ∣ W.lev i 1 W.π₀ := by
  obtain ⟨w, hw⟩ := hp9.2.2.1
  rw [hw, map_mul, map_pow]
  refine Dvd.dvd.mul_left (pow_dvd_pow_of_dvd ?_ _) _
  rw [PowerSeries.X_dvd_iff]
  exact level_pi_constantCoeff_zero (W := W) i

theorem levelExpansion_gamma
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) (x : ↥(W.N T))
    (hx : W.γD T W.gam (x : W.DD T) ∈ W.N T) (k : ℤ) :
    Lb.levB T i 1 ⟨W.γD T W.gam (x : W.DD T), hx⟩ k =
      (algebraMap O LL (W.χΓ W.gam : O)) ^ k • Lb.levB T i 1 x k := by
  refine levB_Γ T hT W.gam i 1 1 0 1 (by simp) ?_ (by simp) x hx k
  rw [Nat.cast_one, W.gam_gen]
  simp

theorem expansion_at_one
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (hs1 : W.s = 1) (hp2 : PD.p ≠ 2) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (i : ZMod n) (x y : ↥(W.N T)) (M : ℕ) (hx : W.γD T W.gam (x : W.DD T) ∈ W.N T)
    (hxy : W.γD T W.gam (x : W.DD T) - (x : W.DD T) = W.π₀ ^ M • (y : W.DD T))
    (k : ℤ) (hk0 : 0 < k) (hk : k < (((PD.p - 1) * M : ℕ) : ℤ)) : Lb.levB T i 1 x k = 0 := by
  have hsub : (⟨W.γD T W.gam (x : W.DD T), hx⟩ : ↥(W.N T)) - x = W.π₀ ^ M • y := Subtype.ext (by
    rw [Submodule.coe_sub, Submodule.coe_smul]
    exact hxy)
  have hz : Lb.levB T i 1 (W.π₀ ^ M • y) k = 0 := by
    rw [levelExpansion_smul levN_eq]
    refine cv_vanish _ _ (fun k hk => levelExpansion_neg_eq_zero levN_eq hs1 T hP4 i y k hk) ((PD.p - 1) * M) ?_ k hk
    rw [map_pow, pow_mul]
    exact pow_dvd_pow_of_dvd (level_pi0_X_pow_dvd hp9 i) M
  have he : Lb.levB T i 1 ⟨W.γD T W.gam (x : W.DD T), hx⟩ k - Lb.levB T i 1 x k = 0 := by
    rw [← Pi.sub_apply, ← map_sub, hsub]
    exact hz
  rw [levelExpansion_gamma levB_Γ T hT i x hx k] at he
  have he' : ((algebraMap O LL (W.χΓ W.gam : O)) ^ k - 1) • Lb.levB T i 1 x k = 0 := by
    rw [sub_smul, one_smul]
    exact he
  have hu : (algebraMap O LL (W.χΓ W.gam : O)) ^ k ≠ 1 := by
    refine ValuationPow.zpow_ne_one v PD.p PD.hp hp2 W.v_l _ ?_ k hk0.ne'
    rw [W.gam_gen, hs1]
    simp
  exact (smul_eq_zero.1 he').resolve_left (sub_ne_zero.2 hu)

end Formalism.MainNotions.N.Ln03.Pf
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfComplMax
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open IsLocalRing

namespace ComplMaxPf

variable {R : Type} [CommRing R]

theorem isAdicComplete_of_pow {I J : Ideal R} (e : ℕ) (he : 1 ≤ e) (h1 : ∀ k, J ^ (e * k) ≤ I ^ k)
    (h2 : ∀ k, I ^ k ≤ J ^ k) (hI : IsAdicComplete I R) : IsAdicComplete J R := by
  have m1 : ∀ k, (J ^ (e * k) • ⊤ : Submodule R R) ≤ I ^ k • ⊤ := fun k => Submodule.smul_mono_left (h1 k)
  have m2 : ∀ k, (I ^ k • ⊤ : Submodule R R) ≤ J ^ k • ⊤ := fun k => Submodule.smul_mono_left (h2 k)
  refine { haus' := fun x hx => hI.haus' x fun k => SModEq.mono (m1 k) (hx (e * k)),
           prec' := fun f hf => ?_ }
  obtain ⟨L, hL⟩ := hI.prec' (fun k => f (e * k)) fun {m n} hmn =>
    SModEq.mono (m1 m) (hf (Nat.mul_le_mul_left e hmn))
  refine ⟨L, fun n => ?_⟩
  have hn : n ≤ e * n := Nat.le_mul_of_pos_left n he
  exact (hf hn).trans (SModEq.mono (m2 n) (hL n))

end ComplMaxPf

theorem complMax_holds : ComplMax := by
  intro O _ _ _ p hpm hp0 hc
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · exfalso
      rw [pow_zero, mul_one] at hu
      rw [hu] at hpm
      exact (IsLocalRing.mem_maximalIdeal _).1 hpm u.isUnit
    · exact h
  have hIk : ∀ k, Ideal.span {(p : O)} ^ k = maximalIdeal O ^ (e * k) := fun k => by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_pow, hu, mul_pow, ← pow_mul,
      Ideal.span_singleton_mul_left_unit (u.isUnit.pow k)]
  refine ComplMaxPf.isAdicComplete_of_pow e he (fun k => (hIk k).ge) (fun k => ?_) hc
  rw [hIk k]
  exact Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left k he)

end Formalism.MainNotions.N.Ln03.Pf
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfHuZ
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

theorem Pf_HuZ_v_dvd (W : LocWach PD LL O v n) (hv_int : ∀ x : O, 0 ≤ v (algebraMap O LL x))
    (k : ℕ) (z : ℤ_[PD.p]) (hz : (PD.p : ℤ_[PD.p]) ^ k ∣ z) :
    (k : WithTop ℚ) ≤ v (algebraMap O LL (ιZ z)) := by
  obtain ⟨y, rfl⟩ := hz
  rw [map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast, AddValuation.map_mul,
    AddValuation.map_pow, W.v_l, nsmul_one]
  exact le_add_of_nonneg_right (hv_int _)

theorem hv_holds (W : LocWach PD LL O v n) (hv_int : ∀ x : O, 0 ≤ v (algebraMap O LL x)) :
    ∀ (s : ℕ) (z : ℤ_[PD.p]), (PD.p : ℤ_[PD.p]) ^ (s + 1) ∣ z →
      ((s + 1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (ιZ z)) :=
  fun s z hz => Pf_HuZ_v_dvd W hv_int (s + 1) z hz

theorem huZ_holds (hu : ιZ uZ = (W.χΓ W.gam : O)) (hv_int : ∀ x : O, 0 ≤ v (algebraMap O LL x)) :
    ∀ k : ℕ, (k : WithTop ℚ) ≤
      v (algebraMap O LL (W.χΓ W.gam : O) - ((PadicInt.toZModPow k (uZ : ℤ_[PD.p])).val : LL)) := by
  intro k
  have : NeZero (PD.p ^ k) := ⟨pow_ne_zero _ (Fact.out : PD.p.Prime).ne_zero⟩
  have hdvd : (PD.p : ℤ_[PD.p]) ^ k ∣
      (uZ : ℤ_[PD.p]) - ((PadicInt.toZModPow k (uZ : ℤ_[PD.p])).val : ℤ_[PD.p]) := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
      ZMod.natCast_zmod_val, sub_self]
  have h := Pf_HuZ_v_dvd (ιZ := ιZ) W hv_int k _ hdvd
  rwa [map_sub, map_natCast, hu, map_sub, map_natCast] at h

end Formalism.MainNotions.N.Ln03.Pf
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfKapUnit
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

theorem Pf_KapUnit_prod (hR : Ring9 W) (c : ZMod n) (ell : ℕ) (e : ℕ → ℕ) (s : ℕ)
    (hp : ∀ s' < ell, IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s)
      (rhoL hR c s ((baseIdOf hR).Bs.p s')))) :
    IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s)
      (rhoL hR c s (∏ s' ∈ Finset.range ell, (baseIdOf hR).Bs.p s' ^ e s'))) := by
  rw [map_prod, map_prod]
  refine Finset.prod_induction _ IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one ?_
  intro x hx
  rw [map_pow, map_pow]
  exact (hp x (Finset.mem_range.1 hx)).pow _

theorem kapUnit_holds {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ}
    {H : ℕ → ℕ} {κ : PowerSeries O} {r : ℕ} {lam : Fin r → Dc W T c}
    (Hy : LvHyp Lb hR uZ ιZ C c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ lam) (j M g η : ℕ)
    (kind : ℕ → Kind) (b : ℕ → ℕ) (m : ℕ)
    (hκ : κ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m)
    (k1b : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).K1b)
    (unitsAt : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).UnitsAt) :
    ∀ s < ell, IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ)) := by
  intro s hs
  have hp : ∀ s' < ell, IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s)
      (rhoL hR c s ((baseIdOf hR).Bs.p s'))) := by
    intro s' hs'
    by_cases h : s' = s
    · subst h
      obtain ⟨ε, hε⟩ := k1b s' hs
      have hε' : rhoL hR c s' ((baseIdOf hR).Bs.p s') = (ε : PowerSeries (KsW W s')) * PowerSeries.X :=
        hε
      rw [hε', map_mul, HahnSeries.ofPowerSeries_X]
      refine (ε.isUnit.map _).mul (isUnit_iff_exists_inv.2 ⟨HahnSeries.single (-1 : ℤ) 1, ?_⟩)
      rw [HahnSeries.single_mul_single]
      simp
    · exact ((unitsAt s hs).2 s' hs' h).map _
  have hΛ := Pf_KapUnit_prod hR c ell H s hp
  have hP := Pf_KapUnit_prod hR c ell (fun _ => m) s hp
  rw [hκ, map_mul, map_mul]
  refine IsUnit.mul ?_ hP
  rw [Formalism.ExponentWindows.abelian₂]
  exact hΛ

end Formalism.MainNotions.N.Ln03.Pf
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfTeichOnto
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.MainNotions.N.Ln03 Polynomial

theorem teichOnto_toZMod_eq_zero_iff {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) :
    PadicInt.toZMod x = 0 ↔ ‖x‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    ← PadicInt.mem_nonunits, mem_nonunits_iff]

theorem teichOnto_norm_eq_one {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) (h : PadicInt.toZMod x ≠ 0) :
    ‖x‖ = 1 :=
  le_antisymm (PadicInt.norm_le_one x) (not_lt.mp fun h' => h ((teichOnto_toZMod_eq_zero_iff x).mpr h'))

theorem teichOnto_holds (p : ℕ) [Fact p.Prime] : TeichOnto p := by
  intro a ha
  have hp : p.Prime := Fact.out
  set a₀ : ℤ_[p] := ((a.val : ℕ) : ℤ_[p]) with ha₀
  have hres : PadicInt.toZMod a₀ = a := by rw [ha₀, map_natCast, ZMod.natCast_zmod_val]
  set F : Polynomial ℤ_[p] := X ^ (p - 1) - 1 with hF
  have hFa : F.aeval a₀ = a₀ ^ (p - 1) - 1 := by simp [hF]
  have hF'a : F.derivative.aeval a₀ = ((p - 1 : ℕ) : ℤ_[p]) * a₀ ^ (p - 1 - 1) := by
    simp [hF, Polynomial.derivative_X_pow]
  have h1 : ‖F.aeval a₀‖ < 1 := by
    rw [← teichOnto_toZMod_eq_zero_iff, hFa, map_sub, map_pow, hres, map_one,
      ZMod.pow_card_sub_one_eq_one ha, sub_self]
  have h2 : ‖F.derivative.aeval a₀‖ = 1 := by
    apply teichOnto_norm_eq_one
    rw [hF'a, map_mul, map_pow, hres, map_natCast]
    refine mul_ne_zero ?_ (pow_ne_zero _ ha)
    rw [Nat.cast_sub hp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub, neg_ne_zero]
    exact one_ne_zero
  obtain ⟨z, hz, hza, -, -⟩ := hensels_lemma (F := F) (a := a₀) (by rw [h2, one_pow]; exact h1)
  rw [h2] at hza
  have hzp : z ^ (p - 1) = 1 := by
    have : F.aeval z = z ^ (p - 1) - 1 := by simp [hF]
    rw [this, sub_eq_zero] at hz
    exact hz
  have hzz : z * z ^ (p - 2) = 1 := by
    have h2p := hp.two_le
    rw [← pow_succ', show p - 2 + 1 = p - 1 by omega, hzp]
  let u : ℤ_[p]ˣ := ⟨z, z ^ (p - 2), hzz, by rw [mul_comm]; exact hzz⟩
  refine ⟨⟨u, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hzp)⟩, ?_⟩
  show PadicInt.toZMod z = a
  have h3 : PadicInt.toZMod (z - a₀) = 0 := (teichOnto_toZMod_eq_zero_iff _).mpr hza
  rw [map_sub, sub_eq_zero, hres] at h3
  exact h3

end Formalism.MainNotions.N.Ln03.Pf
end
end

