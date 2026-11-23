module

public import Formalism.SharpRestriction.LevelLetterCocycles.CoordHomMapTrace
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0016
public import Formalism.SharpRestriction.LevelLetterCocycles.ExponentWindowSubsetShort
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.FinrankEqOneOfBijective
section
noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

theorem wprime_mono {O : Type} [CommRing O] {Bs : Formalism.ExponentWindows.E.Base O} {n : ℕ} {V₁ V₂ : Type}
    [AddCommGroup V₁] [Module (PowerSeries O) V₁] [AddCommGroup V₂] [Module (PowerSeries O) V₂]
    {L₁ : Formalism.ExponentWindows.E.Lat Bs n V₁} {L₂ : Formalism.ExponentWindows.E.Lat Bs n V₂} (h : Formalism.ExponentWindows.E.LatHom L₁ L₂)
    {c : ZMod n} {r r' : ℕ} (hr : h.WPrime c r) (hle : r ≤ r') : h.WPrime c r' := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hr x hx
  refine ⟨Bs.lc ^ (r' - r) • y, (L₁.N c).smul_mem _ hy, ?_⟩
  rw [map_smul, hxy, smul_smul, ← pow_add, Nat.sub_add_cancel hle]

theorem hmax_eq (n : ℕ) [NeZero n] (Mi hi : ZMod n → ℕ) :
    Formalism.MainNotions.LiftingTheory.Hmax n Mi hi = Hmax n (Mi + hi) := by
  unfold Formalism.MainNotions.LiftingTheory.Hmax Hmax
  apply le_antisymm
  · refine Finset.sup_le fun k _ => ?_
    exact Finset.le_sup (f := Mi + hi) (Finset.mem_univ (k : ZMod n))
  · refine Finset.sup_le fun i _ => ?_
    have h1 : ZMod.val i ∈ Finset.range n := Finset.mem_range.2 (ZMod.val_lt i)
    have h2 := Finset.le_sup (f := fun k : ℕ => Mi (k : ZMod n) + hi (k : ZMod n)) h1
    simpa [ZMod.natCast_zmod_val] using h2

theorem cH_eq (l n : ℕ) [NeZero n] (Mi hi : ZMod n → ℕ) :
    Formalism.MainNotions.LiftingTheory.cH l (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi) = ccPar l (Hmax n (Mi + hi)) := by
  rw [hmax_eq]
  rfl

theorem le_floor_add (l r s c Hm : ℕ) (sb : ℝ) (h1 : (r : ℝ) ≤ (s : ℝ) * l / ((l : ℝ) - 1) ^ 2 + c)
    (h2 : s ≤ Hm) (h3 : (s : ℝ) ≤ sb) :
    r ≤ ⌊min (⌊sb⌋₊ : ℝ) (Hm : ℝ) * l / ((l : ℝ) - 1) ^ 2⌋₊ + c := by
  have hs1 : (s : ℝ) ≤ (⌊sb⌋₊ : ℝ) := by exact_mod_cast Nat.le_floor h3
  have hs2 : (s : ℝ) ≤ (Hm : ℝ) := by exact_mod_cast h2
  have hmin : (s : ℝ) ≤ min (⌊sb⌋₊ : ℝ) (Hm : ℝ) := le_min hs1 hs2
  have hq : 0 ≤ (l : ℝ) / ((l : ℝ) - 1) ^ 2 := by positivity
  have h4 : (s : ℝ) * l / ((l : ℝ) - 1) ^ 2 ≤ min (⌊sb⌋₊ : ℝ) (Hm : ℝ) * l / ((l : ℝ) - 1) ^ 2 := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hmin hq
  by_cases hrc : r ≤ c
  · omega
  · have h5 : r - c ≤ ⌊min (⌊sb⌋₊ : ℝ) (Hm : ℝ) * l / ((l : ℝ) - 1) ^ 2⌋₊ := by
      apply Nat.le_floor
      rw [Nat.cast_sub (by omega : c ≤ r)]
      linarith
    omega

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {I : BaseId W} {T₁ T₂ : LocLat G Qp LL O}

theorem X_eq_letπ (hs : W.s = 1) : W.X = letπ := by
  rw [LocWach.X, hs]
  rfl

theorem sI_le_Hmax (hs : W.s = 1) (hX : Formalism.MainNotions.LiftingTheory.coreWX W) (F : LatHom T₁.L T₂.L)
    (Mi hi : ZMod n → ℕ) (hF : Formalism.MainNotions.LiftingTheory.Sur W F) (hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi hi) (i : ZMod n) :
    Formalism.MainNotions.LiftingTheory.sI W F i ≤ Formalism.MainNotions.LiftingTheory.Hmax n Mi hi := by
  have h := hX T₁ T₂ F Mi hi hF hJ i
  rw [X_eq_letπ hs] at h
  exact Nat.sInf_le h

theorem rI_le_rF {Cc : ℝ} (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hR : Formalism.MainNotions.LiftingTheory.coreWR W Cc)
    (hS : Formalism.MainNotions.LiftingTheory.coreWX W) (F : LatHom T₁.L T₂.L) (Mi hi : ZMod n → ℕ)
    (hF : Formalism.MainNotions.LiftingTheory.Sur W F) (hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi hi) (i : ZMod n) :
    Formalism.MainNotions.LiftingTheory.rI W F i ≤ rF PD.p n (Mi + hi) i := by
  obtain ⟨h1, -, h3, -⟩ := hR hA T₁ T₂ F Mi hi hF hJ i
  have h4 := sI_le_Hmax hA.2.1 hS F Mi hi hF hJ i
  rw [cH_eq] at h1 h3
  rw [hmax_eq] at h4
  unfold rF
  refine le_floor_add PD.p _ (Formalism.MainNotions.LiftingTheory.sI W F i) _ _ _ h3 h4 ?_
  refine le_of_le_of_eq h1 ?_
  unfold sBd
  refine tsum_congr fun a => ?_
  rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
  rfl

theorem DelF_mul {δ δ' : W.Gam} (h : δ ∈ W.DelF) (h' : δ' ∈ W.DelF) : δ * δ' ∈ W.DelF := by
  obtain ⟨k, hk, e⟩ := (W.DelF_def δ).1 h
  obtain ⟨k', hk', e'⟩ := (W.DelF_def δ').1 h'
  refine (W.DelF_def _).2 ⟨k * k', Nat.mul_pos hk hk', ?_⟩
  rw [mul_pow, pow_mul, e, one_pow, mul_comm k k', pow_mul, e', one_pow, one_mul]

theorem DelF_inv {δ : W.Gam} (h : δ ∈ W.DelF) : δ⁻¹ ∈ W.DelF := by
  obtain ⟨k, hk, e⟩ := (W.DelF_def δ).1 h
  exact (W.DelF_def _).2 ⟨k, hk, by rw [inv_pow, e, inv_one]⟩

def trΔ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (x : W.DD T) : W.DD T :=
  ∑ δ ∈ W.DelF, W.γD T δ x

theorem trΔ_inv (T : LocLat G Qp LL O) (x : W.DD T) (δ' : W.Gam) (h' : δ' ∈ W.DelF) :
    W.γD T δ' (trΔ W T x) = trΔ W T x := by
  unfold trΔ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_bij' (fun δ _ => δ' * δ) (fun δ _ => δ'⁻¹ * δ) ?_ ?_ ?_ ?_ ?_
  · intro δ hδ; exact DelF_mul h' hδ
  · intro δ hδ; exact DelF_mul (DelF_inv h') hδ
  · intro δ _; simp
  · intro δ _; simp
  · intro δ _; rw [W.γD_mul]

theorem trΔ_mem_N (T : LocLat G Qp LL O) (x : W.DD T) (hx : x ∈ W.N T) : trΔ W T x ∈ W.N T :=
  (W.N T).sum_mem fun δ _ => W.N_Γ T δ x hx

theorem trΔ_letter (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T)
    (hx : (letE i : LetA O n) • x = x) : (letE i : LetA O n) • trΔ W T x = trΔ W T x := by
  unfold trΔ
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun δ _ => ?_
  conv_lhs => rw [← γA_letE W δ i, ← γD_smulA, hx]

theorem trΔ_map (F : LatHom T₁.L T₂.L) (x : W.DD T₁) :
    W.map F (trΔ W T₁ x) = trΔ W T₂ (W.map F x) := by
  unfold trΔ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun δ _ => W.map_γ F δ x

theorem trΔ_fixed (T : LocLat G Qp LL O) (x : W.DD T) (hx : ∀ δ ∈ W.DelF, W.γD T δ x = x) :
    trΔ W T x = ((W.DelF.card : ℕ) : O) • x := by
  rw [trΔ, Finset.sum_congr rfl hx, Finset.sum_const, Nat.cast_smul_eq_nsmul]

theorem lp_smul (T : LocLat G Qp LL O) (r : ℕ) (x : W.DD T) :
    Formalism.MainNotions.LiftingTheory.lp W r • x = (((PD.p : ℕ) : O) ^ r) • x := by
  rw [← algebraMap_smul (LetA O n) ((((PD.p : ℕ) : O) ^ r)) x, map_pow, map_natCast]
  rfl

theorem map_smulO (F : LatHom T₁.L T₂.L) (m : O) (x : W.DD T₁) : W.map F (m • x) = m • W.map F x := by
  rw [← algebraMap_smul (LetA O n) m x, map_smulA, algebraMap_smul]

theorem wprime_of_kills {F : LatHom T₁.L T₂.L} {C₁ : Coord W I T₁} {C₂ : Coord W I T₂}
    (h : CoordHom C₁ C₂ F) (hΔ : IsUnit ((W.DelF.card : ℕ) : O)) (c : ZMod n) (r : ℕ)
    (hk : Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W r)) : (latHomOf h).WPrime c r := by
  intro x hx
  obtain ⟨u, hu⟩ := hΔ
  have hxN : C₂.t c x ∈ W.N T₂ := hx
  have hxl : C₂.t c x ∈ W.Nl T₂ c := ⟨C₂.t c x, hxN, C₂.t_letter c x⟩
  obtain ⟨Y, hY, hYx⟩ := hk _ hxl (fun δ hδ => C₂.t_Δ c x δ hδ)
  obtain ⟨Y', hY', rfl⟩ := hY
  have hYN : (letE c : LetA O n) • Y' ∈ W.N T₁ := (W.N T₁).smul_mem _ hY'
  have hYl : (letE c : LetA O n) • ((letE c : LetA O n) • Y') = (letE c : LetA O n) • Y' := by
    rw [smul_smul, letE_mul_self]
  have hmap : W.map F ((letE c : LetA O n) • Y') = (((PD.p : ℕ) : O) ^ r) • C₂.t c x := by
    rw [← lp_smul]
    exact hYx

  obtain ⟨y, hy⟩ := C₁.t_surj c (((u⁻¹ : Oˣ) : O) • trΔ W T₁ ((letE c : LetA O n) • Y'))
    (by rw [smul_comm, trΔ_letter T₁ c _ hYl])
    (fun δ hδ => by rw [map_smul, trΔ_inv T₁ _ δ hδ])
  refine ⟨y, ?_, ?_⟩
  · rw [mem_N, hy, ← algebraMap_smul (LetA O n)]
    exact (W.N T₁).smul_mem _ (trΔ_mem_N T₁ _ hYN)
  · apply C₂.t_inj c
    change C₂.t c (h.f y) = _
    rw [h.coord_hom_map_trace, hy, map_smulO, trΔ_map, hmap, C₂.t_smul, lc_pow, I.d_C, algebraMap_smul,
      trΔ_fixed T₂ _ (fun δ hδ => by rw [map_smul, C₂.t_Δ c x δ hδ]), smul_smul, ← hu,
      Units.inv_mul, one_smul]

theorem wprime_of {Cc : ℝ} (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hR : Formalism.MainNotions.LiftingTheory.coreWR W Cc)
    (hS : Formalism.MainNotions.LiftingTheory.coreWX W) {F : LatHom T₁.L T₂.L} {C₁ : Coord W I T₁} {C₂ : Coord W I T₂}
    (h : CoordHom C₁ C₂ F) (hΔ : IsUnit ((W.DelF.card : ℕ) : O)) (Mi hi : ZMod n → ℕ)
    (hF : Formalism.MainNotions.LiftingTheory.Sur W F) (hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi hi) (c : ZMod n) :
    (latHomOf h).WPrime c (rF PD.p n (Mi + hi) c) :=
  wprime_mono _ (wprime_of_kills h hΔ c _ (hR hA T₁ T₂ F Mi hi hF hJ c).2.2.2.1)
    (rI_le_rF hA hR hS F Mi hi hF hJ c)

theorem wprimeCuts_of {Cc : ℝ} (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hR : Formalism.MainNotions.LiftingTheory.coreWR W Cc)
    (hS : Formalism.MainNotions.LiftingTheory.coreWX W) {F : LatHom T₁.L T₂.L} {C₁ : Coord W I T₁} {C₂ : Coord W I T₂}
    (h : CoordHom C₁ C₂ F) (hΔ : IsUnit ((W.DelF.card : ℕ) : O)) (Mi hi H₂ : ZMod n → ℕ)
    (hF : Formalism.MainNotions.LiftingTheory.Sur W F) (hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi hi)
    {j : ℕ} {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (hC : CutsOK n j ty cuts arcLen) :
    Formalism.ExponentWindows.E.WPrimeCuts (latHomOf h) (cutsOf hC) (rrPar PD.p n (Mi + hi) H₂ cuts) := by
  intro c hc
  refine wprime_mono _ (wprime_of hA hR hS h hΔ Mi hi hF hJ c) ?_
  exact le_trans (le_max_left _ _)
    (Finset.le_sup (f := fun c => max (rF PD.p n (Mi + hi) c) (rF PD.p n H₂ c)) hc)

theorem lift_of {Cc : ℝ} (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hR : Formalism.MainNotions.LiftingTheory.coreWR W Cc)
    (hS : Formalism.MainNotions.LiftingTheory.coreWX W) {T : LocLat G Qp LL O} {C : Coord W I T} {C₀ : Coord W I W.one}
    (R : RealExt C C₀) (hE : R.Exact) (hΔ : IsUnit ((W.DelF.card : ℕ) : O)) (H₁ Mi hi : ZMod n → ℕ)
    (hF : Formalism.MainNotions.LiftingTheory.Sur W R.π) (hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W R.Y Mi hi) (e₀ : C₀.V)
    {cuts : Finset (ZMod n)} {c : ZMod n} (hc : c ∈ cuts) (he : e₀ ∈ (latOf C₀).N c) :
    (R.ext hE).Lift e₀ c (rrPar PD.p n H₁ (Mi + hi) cuts) := by
  have hw : (latHomOf R.hπ).WPrime c (rrPar PD.p n H₁ (Mi + hi) cuts) :=
    wprime_mono _ (wprime_of hA hR hS R.hπ hΔ Mi hi hF hJ c)
      (le_trans (le_max_right _ _)
        (Finset.le_sup (f := fun c => max (rF PD.p n H₁ c) (rF PD.p n (Mi + hi) c)) hc))
  exact hw e₀ he

theorem jumpsLet_ext (hH : HodgeExact PD LL O) {T Y : LocLat G Qp LL O} (ι : LatHom T.L Y.L)
    (π : LatHom Y.L W.one.L) (hses : IsSESLat (Qp := Qp) ι π) (hY : CrysLat PD Y)
    (Mi hi : ZMod n → ℕ) (hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T Mi hi) : Formalism.MainNotions.LiftingTheory.JumpsLet W Y Mi hi := by
  intro i τ hτ a ha
  rcases ((hH.2.1 T Y W.one ι π hses hY).2.2 τ a).1 ha with h | h
  · exact hJ i τ hτ a h
  · have h0 : a = 0 := hH.2.2 W.one W.one_triv τ a h
    subst h0
    constructor <;> simp

theorem sur_ext (hH : HodgeExact PD LL O) {T Y : LocLat G Qp LL O} (ι : LatHom T.L Y.L)
    (π : LatHom Y.L W.one.L) (hses : IsSESLat (Qp := Qp) ι π) (hY : CrysLat PD Y) :
    Formalism.MainNotions.LiftingTheory.Sur W π :=
  ⟨hY.2.2.2, (hH.2.1 T Y W.one ι π hses hY).2.1.2.2.2, hses.2.2.1⟩

theorem wprimeCuts_of' {Cc : ℝ} (hK : Function.Bijective (algebraMap K₀ K)) (hs : W.s = 1)
    (hp : PD.p ≠ 2) (hR : Formalism.MainNotions.LiftingTheory.coreWR W Cc) (hS : Formalism.MainNotions.LiftingTheory.coreWX W)
    {F : LatHom T₁.L T₂.L} {C₁ : Coord W I T₁} {C₂ : Coord W I T₂} (h : CoordHom C₁ C₂ F)
    (hΔ : IsUnit ((W.DelF.card : ℕ) : O)) (hc₁ : CrysLat PD T₁) (hc₂ : CrysLat PD T₂) (hon : F.Onto)
    (Mb₁ hb₁ H₂ : ZMod n → ℕ)
    (hJ : ∀ i, JumpsAtE PD T₁ W.emb i (Set.Icc (-(Mb₁ i : ℤ)) (hb₁ i)))
    {j : ℕ} {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (hC : CutsOK n j ty cuts arcLen) :
    Formalism.ExponentWindows.E.WPrimeCuts (latHomOf h) (cutsOf hC) (rrPar PD.p n (Mb₁ + hb₁) H₂ cuts) :=
  wprimeCuts_of ⟨hK, hs, hp⟩ hR hS h hΔ Mb₁ hb₁ H₂ ⟨hc₁.2.2.2, hc₂.2.2.2, hon⟩ hJ hC

theorem lift_of' {Cc : ℝ} (hK : Function.Bijective (algebraMap K₀ K)) (hs : W.s = 1)
    (hp : PD.p ≠ 2) (hR : Formalism.MainNotions.LiftingTheory.coreWR W Cc) (hS : Formalism.MainNotions.LiftingTheory.coreWX W)
    (hH : HodgeExact PD LL O) {C₂ : Coord W I T₂} {C₀ : Coord W I W.one}
    (R : RealExt C₂ C₀) (hE : R.Exact) (hΔ : IsUnit ((W.DelF.card : ℕ) : O))
    (hses : IsSESLat (Qp := Qp) R.ι R.π) (hY : CrysLat PD R.Y) (H₁ Mb₂ hb₂ : ZMod n → ℕ)
    (hJ : ∀ i, JumpsAtE PD T₂ W.emb i (Set.Icc (-(Mb₂ i : ℤ)) (hb₂ i))) (e₀ : C₀.V)
    (he : ∀ i, e₀ ∈ (latOf C₀).N i)
    {j : ℕ} {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (hC : CutsOK n j ty cuts arcLen) :
    ∀ c ∈ (cutsOf hC).cuts, (R.ext hE).Lift e₀ c (rrPar PD.p n H₁ (Mb₂ + hb₂) cuts) :=
  fun c hc => lift_of ⟨hK, hs, hp⟩ hR hS R hE hΔ H₁ Mb₂ hb₂ (sur_ext hH R.ι R.π hses hY)
    (jumpsLet_ext hH R.ι R.π hses hY Mb₂ hb₂ hJ) e₀ hc (he c)

end Formalism.MainNotions.WachCoordinates.Br
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusMemPullbackOfInvariant
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.LiftingTheory Formalism.MainNotions.CrystallineLiftingInputs

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem letE_mul_self_eq (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  unfold letE
  rw [← Pi.single_mul, mul_one]

theorem idempotent_smul_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n)
    (x : W.DD T) : (letE i : LetA O n) • (letE i : LetA O n) • x = (letE i : LetA O n) • x := by
  rw [smul_smul, letE_mul_self_eq]

private theorem phiD_letA_smul_eq_phiA_smul_phiD (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
    (a : LetA O n) (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul] <;> rfl

private theorem phiA_letE_sub_one_eq_letE (W : LocWach PD LL O v n) (i : ZMod n) :
    W.φA (letE (i - 1) : LetA O n) = letE i := by
  funext j
  show W.φ₀ ((letE (i - 1) : LetA O n) (j - 1)) = (letE i : LetA O n) j
  by_cases h : j = i
  · subst h
    simp [letE]
  · have h' : j - 1 ≠ i - 1 := fun e => h (sub_left_inj.mp e)
    simp [letE, Pi.single_apply, h, h']

theorem frobenius_idempotent_shift (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T) :
    W.φD T ((letE (i - 1) : LetA O n) • x) = (letE i : LetA O n) • W.φD T x := by
  rw [phiD_letA_smul_eq_phiA_smul_phiD, phiA_letE_sub_one_eq_letE]

private theorem letGamma_letE_eq_letE (W : LocWach PD LL O v n) (g : W.Gam) (i : ZMod n) :
    letγ (W.γ₀ g) (letE i : LetA O n) = letE i := by
  funext j
  show W.γ₀ g ((letE i : LetA O n) j) = (letE i : LetA O n) j
  by_cases h : j = i
  · subst h
    simp [letE]
  · simp [letE, Pi.single_apply, h]

theorem gammaD_idempotent_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (g : W.Gam) (i : ZMod n)
    (x : W.DD T) : W.γD T g ((letE i : LetA O n) • x) = (letE i : LetA O n) • W.γD T g x := by
  rw [← algebraMap_smul W.EE (letE i : LetA O n) x, W.γD_smul, W.γE_ext, algebraMap_smul,
    letGamma_letE_eq_letE]

theorem natCast_pow_smul_eq_algebra (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (N : ℕ) (x : W.DD T) :
    ((PD.p : ℕ) : O) ^ N • x = ((PD.p : ℕ) : LetA O n) ^ N • x := by
  rw [← algebraMap_smul (LetA O n) (((PD.p : ℕ) : O) ^ N) x, map_pow, map_natCast]

theorem frobeniusA_natCast_pow (W : LocWach PD LL O v n) (N : ℕ) :
    W.φA (((PD.p : ℕ) : LetA O n) ^ N) = ((PD.p : ℕ) : LetA O n) ^ N := by
  rw [map_pow, map_natCast]

theorem gammaA_natCast_pow (W : LocWach PD LL O v n) (g : W.Gam) (N : ℕ) :
    W.γA g (((PD.p : ℕ) : LetA O n) ^ N) = ((PD.p : ℕ) : LetA O n) ^ N := by
  rw [map_pow, map_natCast]

theorem basis_vector_eq_zero_or_torsionFree (W : LocWach PD LL O v n) (e : W.DD W.one)
    (hspan : W.N W.one = Submodule.span (LetA O n) {e}) (π' : LetA O n)
    (hm : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W W.one π') : e = 0 ∨ ∀ β : LetA O n, β • e = 0 → β = 0 := by
  obtain ⟨⟨r, b, hb, huniq, -⟩, -⟩ := hm
  by_cases he : e = 0
  · exact Or.inl he
  right
  intro β hβ
  have heN : e ∈ W.N W.one := by
    rw [hspan]
    exact Submodule.mem_span_singleton_self e
  have hkill : ∀ y ∈ W.N W.one, β • y = 0 := by
    intro y hy
    rw [hspan] at hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [smul_smul, mul_comm, ← smul_smul, hβ, smul_zero]
  obtain ⟨a, ha, hu⟩ := huniq e heN
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0
      exact (he (by simpa using ha)).elim
    · exact h0
  have hz : ∑ j, β • b j = 0 := Finset.sum_eq_zero fun j _ => hkill _ (hb j).1
  have h2 : e = ∑ j, (a j + β) • b j := by
    simp only [add_smul, Finset.sum_add_distrib]
    rw [← ha, hz, add_zero]
  have h3 := congrFun (hu (fun j => a j + β) h2) ⟨0, hr⟩
  simpa using h3

theorem eq_zero_of_natCast_pow_mul (hζ : ∃ ζ : LL, IsPrimitiveRoot ζ PD.p)
    (hO : ∃ _ : IsDomain O, IsDiscreteValuationRing O ∧ IsFractionRing O LL) (N : ℕ) (β : LetA O n)
    (h : ((PD.p : ℕ) : LetA O n) ^ N * β = 0) : β = 0 := by
  obtain ⟨hd, -, hf⟩ := hO
  haveI := hd
  haveI : NeZero PD.p := ⟨PD.hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := hζ
  have hLL : ((PD.p : ℕ) : LL) ≠ 0 := hζ.neZero'.out
  have hpO : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h0
    apply hLL
    rw [← map_natCast (algebraMap O LL), h0, map_zero]
  have hpS : ((PD.p : ℕ) : PowerSeries O) ≠ 0 := by
    intro h0
    apply hpO
    have h1 := congrArg PowerSeries.constantCoeff h0
    rwa [map_natCast, map_zero] at h1
  funext j
  have hj := congrFun h j
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, Pi.zero_apply] at hj
  rcases mul_eq_zero.mp hj with h1 | h1
  · exact ((pow_ne_zero N hpS) h1).elim
  · exact h1

theorem frobenius_mem_pullback_of_invariant (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (π' : LetA O n)
    (hm : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π') (i : ZMod n) (t : W.DD T) (ht : t ∈ W.N T)
    (hl : (letE (i - 1) : LetA O n) • t = t) : W.φD T t ∈ pullJ W T (i - 1) 1 := by
  obtain ⟨⟨r, b, hb, huniq, -⟩, -⟩ := hm
  obtain ⟨a, ha, -⟩ := huniq t ht
  have ht' : t = ∑ j, a j • ((letE (i - 1) : LetA O n) • b j) := by
    calc t = (letE (i - 1) : LetA O n) • t := hl.symm
      _ = (letE (i - 1) : LetA O n) • ∑ j, a j • b j := by rw [← ha]
      _ = _ := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [smul_smul, smul_smul, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ht', map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [phiD_letA_smul_eq_phiA_smul_phiD]
  apply Submodule.smul_mem
  unfold pullJ
  apply Submodule.subset_span
  refine ⟨(letE (i - 1) : LetA O n) • b j,
    ⟨(W.N T).smul_mem _ (hb j).1, idempotent_smul_smul W T (i - 1) (b j), fun δ hδ => ?_⟩, ?_⟩
  · rw [gammaD_idempotent_smul, (hb j).2 δ hδ]
  · simp

private theorem locWach_map_letA_smul_comm (W : LocWach PD LL O v n) {T Y : LocLat G Qp LL O}
    (f : LatHom T.L Y.L) (a : LetA O n) (x : W.DD T) : W.map f (a • x) = a • W.map f x := by
  rw [← algebraMap_smul W.EE a x, map_smul, algebraMap_smul]

theorem pullback_span_of_exact (W : LocWach PD LL O v n) {T Y : LocLat G Qp LL O} (ι : LatHom T.L Y.L)
    (π : LatHom Y.L W.one.L) (hY : IsCrys PD Y.ρ) (hO : IsCrys PD W.one.ρ)
    (hker : ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x) (hsat : ∀ x, W.map ι x ∈ W.N Y → x ∈ W.N T)
    (hinj : Function.Injective (W.map ι)) (π' : LetA O n) (hmT : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π')
    (e' : W.DD W.one) (hspan : W.N W.one = Submodule.span (LetA O n) {e'}) (i : ZMod n) (N : ℕ)
    (ε : W.DD Y) (hεN : ε ∈ W.N Y)
    (hεπ : W.map π ε = ((PD.p : ℕ) : LetA O n) ^ N • (letE (i - 1) : LetA O n) • e') :
    ∀ x ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W Y (W.Nl Y (i - 1)), ∃ p ∈ pullJ W T (i - 1) 1, ∃ β : LetA O n,
      ((PD.p : ℕ) : LetA O n) ^ N • x = W.map ι p + β • W.φD Y ε ∧ (e' = 0 → β = 0) := by
  intro x hx
  unfold Formalism.MainNotions.DeltaInvariantLattices.φspan at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z0, hz0, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := (hz0 : z0 ∈ (W.N Y).map ((letE (i - 1) : LetA O n) • LinearMap.id))
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    set z : W.DD Y := (letE (i - 1) : LetA O n) • y with hzdef
    have hz_idem : (letE (i - 1) : LetA O n) • z = z := by
      rw [hzdef]
      exact idempotent_smul_smul W Y (i - 1) y
    have hzN : z ∈ W.N Y := (W.N Y).smul_mem _ hy
    have hπz := W.map_N π hY hO z hzN
    obtain ⟨c, hc, hc0⟩ : ∃ c : LetA O n, c • e' = W.map π z ∧ (e' = 0 → c = 0) := by
      by_cases he : e' = 0
      · rw [hspan, he, Submodule.span_zero_singleton, Submodule.mem_bot] at hπz
        exact ⟨0, by rw [zero_smul, hπz], fun _ => rfl⟩
      · rw [hspan] at hπz
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hπz
        exact ⟨c, hc, fun h => (he h).elim⟩
    have hπlet : W.map π z = (letE (i - 1) : LetA O n) • W.map π z := by
      rw [← locWach_map_letA_smul_comm, hz_idem]
    have hce : c • e' = ((letE (i - 1) : LetA O n) * c) • e' := by
      rw [← smul_smul, hc]
      exact hπlet
    have hw : W.map π (((PD.p : ℕ) : LetA O n) ^ N • z - c • ε) = 0 := by
      rw [map_sub, locWach_map_letA_smul_comm W π _ z, locWach_map_letA_smul_comm W π c ε, hεπ, ← hc, hce]
      simp only [smul_smul]
      rw [sub_eq_zero]
      congr 1
      ring
    obtain ⟨y', hy'⟩ := (hker _).mp hw
    have hι : W.map ι ((letE (i - 1) : LetA O n) • y') =
        ((PD.p : ℕ) : LetA O n) ^ N • z - c • ((letE (i - 1) : LetA O n) • ε) := by
      rw [locWach_map_letA_smul_comm, hy', smul_sub, smul_comm (letE (i - 1) : LetA O n) _ z, hz_idem,
        smul_comm (letE (i - 1) : LetA O n) c ε]
    have hyN : (letE (i - 1) : LetA O n) • y' ∈ W.N T := by
      apply hsat
      rw [hι]
      exact sub_mem ((W.N Y).smul_mem _ hzN) ((W.N Y).smul_mem _ ((W.N Y).smul_mem _ hεN))
    have hp := frobenius_mem_pullback_of_invariant W T π' hmT i _ hyN (idempotent_smul_smul W T (i - 1) y')
    have e1 : W.φD Y (((PD.p : ℕ) : LetA O n) ^ N • z) = ((PD.p : ℕ) : LetA O n) ^ N • W.φD Y z := by
      rw [phiD_letA_smul_eq_phiA_smul_phiD, frobeniusA_natCast_pow]
    have e2 : W.φD Y (c • (letE (i - 1) : LetA O n) • ε) =
        (W.φA c * (letE i : LetA O n)) • W.φD Y ε := by
      rw [phiD_letA_smul_eq_phiA_smul_phiD, frobenius_idempotent_shift, smul_smul]
    refine ⟨_, hp, W.φA c * (letE i : LetA O n), ?_, fun h => by rw [hc0 h, map_zero, zero_mul]⟩
    rw [W.map_φ, hι, map_sub, e1, e2, sub_add_cancel]
  | zero => exact ⟨0, Submodule.zero_mem _, 0, by simp, fun _ => rfl⟩
  | add a b _ _ ha hb =>
    obtain ⟨q1, hq1, β1, h11, h21⟩ := ha
    obtain ⟨q2, hq2, β2, h12, h22⟩ := hb
    refine ⟨q1 + q2, Submodule.add_mem _ hq1 hq2, β1 + β2, ?_, fun h => by rw [h21 h, h22 h, add_zero]⟩
    rw [smul_add, h11, h12, map_add (f := _), add_smul]
    abel
  | smul c a _ ha =>
    obtain ⟨q, hq, β, h1, h2⟩ := ha
    refine ⟨c • q, Submodule.smul_mem _ _ hq, c * β, ?_, fun h => by rw [h2 h, mul_zero]⟩
    rw [smul_comm, h1, smul_add, locWach_map_letA_smul_comm, smul_smul]

end Formalism.MainNotions.RamifiedCoefficientChains.Sh

end
end

