module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0558
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocLatV
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0543
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0512
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0553
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0498

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqStdPowerSeriesAtZero
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

noncomputable section

namespace GlobalTheory.NL.AtZero

section Series

variable {L M ι : Type} [Field L] [AddCommGroup M] [Module L M]

theorem conv_mem (e : PowerSeries L) {u : ℤ → M} {m : ℤ} (hm : ∀ k < m, u k = 0) (k : ℤ)
    (S : Submodule L M) (hS : ∀ j : ℕ, PowerSeries.coeff j e ≠ 0 → u (k - j) ∈ S) :
    conv e u k ∈ S := by
  unfold conv
  rw [finsum_eq_sum _ (Model.conv_finite e hm k)]
  refine S.sum_mem fun j _ => ?_
  by_cases hj : PowerSeries.coeff j e = 0
  · rw [hj, zero_smul]; exact S.zero_mem
  · exact S.smul_mem _ (hS j hj)

theorem conv_X_pow (u : ℤ → M) (n : ℕ) (k : ℤ) :
    conv ((PowerSeries.X : PowerSeries L) ^ n) u k = u (k - n) := by
  unfold conv
  rw [finsum_eq_single _ n]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_X_pow, hj]

theorem std_of_lower (ex : ι → ℤ → M) (D : Submodule L M) (hD : ∀ x k, ex x k ∈ D) (m₀ : ℤ)
    (hs : ∀ x, ∀ k < m₀, ex x k = 0)
    (hlow : ∀ (S : Submodule L M) (k : ℤ), k ≠ 0 → (∀ y, ∀ j < k, ex y j ∈ S) → ∀ x, ex x k ∈ S)
    (hF : Full D (latSpan ex)) (hG : Graded (latSpan (LL := L) ex)) : Std D (latSpan ex) := by
  have up : ∀ (S : Submodule L M) (a : ℤ) (n : ℕ), (∀ y, ∀ j < a, ex y j ∈ S) →
      (∀ j, a ≤ j → j < a + n → j ≠ 0) → ∀ y, ∀ j < a + n, ex y j ∈ S := by
    intro S a n h0
    induction n with
    | zero => intro _ y j hj; exact h0 y j (by omega)
    | succ n ih =>
      intro hne y j hj
      have ih' := ih fun j h1 h2 => hne j h1 (by omega)
      by_cases hlt : j < a + n
      · exact ih' y j hlt
      · obtain rfl : j = a + n := by omega
        exact hlow S _ (hne _ (by omega) (by omega)) ih' y
  have hneg : ∀ y, ∀ j < (0 : ℤ), ex y j = 0 := by
    intro y j hj
    by_cases hj' : j < m₀
    · exact hs y j hj'
    · exact (Submodule.mem_bot L).1 (up ⊥ m₀ (-m₀).toNat (fun y j hj => by simp [hs y j hj])
        (fun j h1 h2 => by omega) y j (by omega))
  let S : Submodule L M := Submodule.span L (Set.range fun x => ex x 0)
  have hS : ∀ y j, ex y j ∈ S := by
    intro y j
    refine up S 1 j.toNat (fun y j hj => ?_) (fun j h1 h2 => by omega) y j (by omega)
    by_cases h0 : j = 0
    · subst h0; exact Submodule.subset_span ⟨y, rfl⟩
    · rw [hneg y j (by omega)]; exact S.zero_mem
  have hDS : D ≤ S := by
    intro d hd
    obtain ⟨m, hm⟩ := hF
    have h1 := hm (Pi.single (m : ℤ) d) (fun k => by
      by_cases hk : k = m
      · subst hk; simpa using hd
      · simp [Pi.single_eq_of_ne hk]) (fun k hk => Pi.single_eq_of_ne hk.ne _)
    simpa using (Model.latSpan_coeff ex S hS (fun x => ⟨m₀, hs x⟩) _ h1).1 m
  have hsingle : ∀ (n : ℕ), ∀ d ∈ S, (Pi.single (n : ℤ) d : ℤ → M) ∈ latSpan (LL := L) ex := by
    intro n d hd
    induction hd using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨x, rfl⟩ := hd
      have h1 : conv ((PowerSeries.X : PowerSeries L) ^ n) (ex x) ∈ latSpan (LL := L) ex :=
        Submodule.subset_span ⟨_, x, rfl⟩
      have h2 := ((hG _).1 h1).2 n
      rwa [conv_X_pow, sub_self] at h2
    | zero => simp
    | add a b _ _ ha hb => rw [Pi.single_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [Pi.single_smul]; exact Submodule.smul_mem _ c ha
  intro f
  constructor
  · intro hf
    refine ⟨(Model.latSpan_coeff ex D hD (fun x => ⟨m₀, hs x⟩) f hf).1, ?_⟩
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨e, x, rfl⟩ := hf
      intro k hk
      apply finsum_eq_zero_of_forall_eq_zero
      intro j
      rw [hneg x _ (by omega), smul_zero]
    | zero => exact fun _ _ => rfl
    | add f g _ _ hf hg => intro k hk; simp [hf k hk, hg k hk]
    | smul c f _ hf => intro k hk; simp [hf k hk]
  · rintro ⟨h1, h2⟩
    refine (hG f).2 ⟨⟨0, h2⟩, fun k => ?_⟩
    by_cases hk : k < 0
    · rw [h2 k hk]; simp
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n := ⟨k.toNat, by omega⟩
      exact hsingle n _ (hDS (h1 _))

theorem uniform_supp {A N : Type} [CommRing A] [AddCommGroup N] [Module A N] [Module.Finite A N]
    (ex : N →+ ℤ → M) (lev : A → PowerSeries L) (hs : ∀ x, ∃ m : ℤ, ∀ k < m, ex x k = 0)
    (hsm : ∀ a x, ex (a • x) = conv (lev a) (ex x)) : ∃ m₀ : ℤ, ∀ x, ∀ k < m₀, ex x k = 0 := by
  obtain ⟨s, hsp⟩ := Module.Finite.fg_top (R := A) (M := N)
  choose m hm using hs
  obtain ⟨b, hb⟩ := (s.finite_toSet.image m).bddBelow
  refine ⟨b, fun x => ?_⟩
  have hx : x ∈ Submodule.span A (s : Set N) := hsp ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact fun k hk => hm x k (lt_of_lt_of_le hk (hb ⟨x, hx, rfl⟩))
  | zero => intro k _; simp
  | add x y _ _ hx hy => intro k hk; simp [hx k hk, hy k hk]
  | smul a x _ hx =>
    intro k hk
    rw [hsm]
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    rw [hx _ (by omega), smul_zero]

end Series

section Concrete

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P} {F : LocFon l P AI H}
  {K : FinExt l} {s : ℕ} {LL : FinExt l}

theorem chi_gam_zpow_ne_one
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) (k : ℤ) (hk : k ≠ 0) :
    algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL)) ^ k ≠ 1 := by
  obtain ⟨g, hg⟩ := W.resΓ_onto W.gam
  have h1 := W.gam_gen
  rw [← hg, W.χΓ_res] at h1 ⊢
  rw [← map_one (algebraMap ℚ_[l] ↥LL.1), ← map_sub] at h1
  have h2 := GlobalTheory.Cyc.DictKs.norm_eq_of_v P LL _ _ h1
  have h3 := GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one l W.s
    ⟨W.s_pos, fun h => W.s_two ((P.PD_p K).trans h)⟩ _ h2 k hk
  intro h
  rw [← map_zpow₀, map_eq_one_iff _ (algebraMap ℚ_[l] ↥LL.1).injective] at h
  rw [h, sub_self, norm_zero] at h3
  exact (zpow_pos (Nat.cast_pos.mpr (Fact.out : l.Prime).pos) _).ne h3


set_option maxHeartbeats 4000000 in
theorem lower (C : LocCmpT l P AI H F) (h : Good K s LL) (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ)
    (i : Let K) (S : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.B)) (k : ℤ) (hk : k ≠ 0)
    (hS : ∀ y, ∀ j < k, ex C h T i 1 y j ∈ S) (x : ↥((H.W K s LL h).N T)) :
    ex C h T i 1 x k ∈ S := by
  have hmem := (H.W K s LL h).N_Γ T (H.W K s LL h).gam x x.2
  obtain ⟨y, hy, hxy⟩ := (H.W K s LL h).N_π T (H.W K s LL h).gam x x.2
  have h1 := (C.C K s LL h).tie.levB_Γ T hT (H.W K s LL h).gam i 1 1 0 0 (by simp)
    (by
      rw [Nat.cast_zero, Nat.cast_zero, sub_zero, P.v_O]
      exact Subtype.property _) (pow_zero _).symm x hmem k
  have h2 : (⟨_, hmem⟩ : ↥((H.W K s LL h).N T)) = x + (letπ : AA K LL) • ⟨y, hy⟩ := by
    apply Subtype.ext
    change _ = (x : (H.W K s LL h).DD T) + (letπ : AA K LL) • y
    rw [← hxy]; simp
  rw [h2, (C.C K s LL h).tie.levB T i 1 |>.map_add] at h1
  have h3 : ex C h T i 1 x k + ex C h T i 1 ((letπ : AA K LL) • ⟨y, hy⟩) k =
      (algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ (H.W K s LL h).gam : ↥(OL LL))) ^ k •
        ex C h T i 1 x k := h1
  have hex : ∀ (a : AA K LL) (x : ↥((H.W K s LL h).N T)),
      ex C h T i 1 (a • x) = conv ((H.W K s LL h).lev i 1 a) (ex C h T i 1 x) := by
    intro a x
    funext k
    have hinj : Function.Injective (ιV (P.PD K) : T.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.BdR) := by
      have hf : Function.Injective (((P.PD K).ι.toLinearMap).restrictScalars ℚ_[l]) := (P.PD K).ι_inj
      exact Module.Flat.lTensor_preserves_injective_linearMap (M := T.V) _ hf
    apply hinj
    obtain ⟨m, hm⟩ := (C.C K s LL h).tie.levB_supp T i 1 x
    unfold ex
    rw [← (C.C K s LL h).tie.levN_eq, (H.W K s LL h).levN_smul, conv,
      map_finsum _ (Model.conv_finite _ hm k)]
    simp only [map_smul]
    congr 1
    funext j
    exact congrArg (fun z => PowerSeries.coeff j ((H.W K s LL h).lev i 1 a) • z)
      ((C.C K s LL h).tie.levN_eq T i 1 x (k - j))
  have h4 : ex C h T i 1 ((letπ : AA K LL) • ⟨y, hy⟩) k ∈ S := by
    rw [hex (letπ : AA K LL) ⟨y, hy⟩]
    obtain ⟨m, hm⟩ := (C.C K s LL h).tie.levB_supp T i 1 ⟨y, hy⟩
    refine conv_mem _ hm k S fun j hj => hS _ _ ?_
    have h0 := (Model.mem_van _ _ _ _ _).1 (Model.pi_van_one (H.W K s LL h) i).1 0 (by omega)
    have : j ≠ 0 := by rintro rfl; exact hj h0
    omega
  have h5 := sub_ne_zero.2 (chi_gam_zpow_ne_one (H.W K s LL h) k hk)
  rw [← S.smul_mem_iff h5, sub_smul, one_smul, ← h3, add_sub_cancel_left]
  exact h4

end Concrete

theorem lat_one_std : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ i : Let K, Std (Di (HW l) h T i) (Lat C h T i 1) := by
  intro D HW F Cm l _ K s LL h W E C T hT i
  have down : ∀ (n : ℕ) (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ n) →
      Full (Di (HW l) h T (i + n)) (Lat C h T (i + n) ζ) → Full (Di (HW l) h T i) (Lat C h T i 1) := by
    intro n
    induction n with
    | zero =>
      intro i ζ hζ hF
      obtain rfl : ζ = 1 := by simpa using hζ
      simpa using hF
    | succ n ih =>
      intro i ζ hζ hF
      have h1 := GlobalTheory.T.wachExpansionLattice_full_descends D HW F Cm l K s LL h T hT _ ζ ⟨_, hζ⟩ hF
      have e : i + ((n + 1 : ℕ) : Let K) - 1 = i + n := by push_cast; ring
      rw [e] at h1
      exact ih i (ζ ^ l) (hζ.pow (pow_pos (Fact.out : l.Prime).pos _) (pow_succ' l n)) h1
  obtain ⟨ζ, -, -, hζ⟩ := GlobalTheory.exists_isPt_primitiveRoot (HW l) h i
  have hF := down s i ζ hζ (GlobalTheory.T.wach_expansions_span_full_lattice D HW F Cm l K s LL h T hT _ ζ hζ)
  have hG := GlobalTheory.T.wachExpansionLattice_graded_of_level_le D HW F Cm l K s LL h T hT i 1 (one_pow _) hF
  haveI : Module.Finite (AA K LL) ↥(W.N T) := Module.Finite.iff_fg.2 (W.N_fg T)
  set_option synthInstance.maxHeartbeats 200000 in
  have hex : ∀ (a : AA K LL) (x : ↥(W.N T)),
      ex C h T i 1 (a • x) = conv (W.lev i 1 a) (ex C h T i 1 x) := by
    intro a x
    funext k
    have hinj : Function.Injective (ιV ((D.loc l).PD K) : T.V ⊗[ℚ_[l]] (D.loc l).R.B →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] (D.loc l).R.BdR) := by
      have hf : Function.Injective ((((D.loc l).PD K).ι.toLinearMap).restrictScalars ℚ_[l]) := ((D.loc l).PD K).ι_inj
      exact Module.Flat.lTensor_preserves_injective_linearMap (M := T.V) _ hf
    apply hinj
    obtain ⟨m, hm⟩ := (C.C K s LL h).tie.levB_supp T i 1 x
    unfold ex
    rw [← (C.C K s LL h).tie.levN_eq, W.levN_smul, conv,
      map_finsum _ (Model.conv_finite _ hm k)]
    simp only [map_smul]
    congr 1
    funext j
    exact congrArg (fun z => PowerSeries.coeff j (W.lev i 1 a) • z)
      ((C.C K s LL h).tie.levN_eq T i 1 x (k - j))
  obtain ⟨m₀, hm₀⟩ := uniform_supp ((C.C K s LL h).tie.levB T i 1) (W.lev i 1)
    ((C.C K s LL h).tie.levB_supp T i 1) hex
  exact std_of_lower (ex C h T i 1) _ (fun x k => (C.C K s LL h).tie.levB_mem T i 1 x k) m₀ hm₀
    (lower C h T hT i) hF hG

end GlobalTheory.NL.AtZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiValueGaloisSubMemFilZero
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per


open GlobalTheory.BKGal.XiFil GlobalTheory.BKGal.ValueFil in
theorem GlobalTheory.BKGal.XiFil.xi_value_gal_sub_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∃ m₀ : ℕ, ∀ w ∈ D.Mext (invL l (A O K)), (∀ τ i, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (w τ i) = E K l e ^ m₀ * h) → ∀ (hw : D.xiExt w ∈ D.MMl) (g : Gl l), sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩)) - R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩) ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ _ ι _ _ η H D T R
  haveI : FiniteDimensional ℚ_[l] K := TameDescentExponentData.finite (l := l) (e := e) (a := a)
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  refine ⟨η, fun w hwA hN hw g hg C => ?_⟩
  have hwS : ∀ τ j, w τ j ∈ invL l (S O K e) := fun τ j =>
    away_mono (A_le_S l e) (by simp) (mem_tot.1 hwA τ j)
  have hd : ∀ j : ι, D.xi (fun _ => Pi.single j (1 : K)) ∈ D.MMl := fun j =>
    ((_root_.GlobalTheory.BK.xi_trivialises_invL_S O K l e a ι D.toPhiMod).2 _).2 (mem_tot.2 fun τ i => by
      rw [cst_apply]
      exact HasK.C_mem _)
  obtain ⟨V, hV⟩ : ∃ V : ι → TW (OB l O) T,
      V = fun j => R.jB (toBcris t ϖ D.toPhiMod ⟨D.xi (fun _ => Pi.single j 1), hd j⟩) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ι → OB l O, c = fun j => ϖ.iB t K (fun τ => ⟨w τ j, hwS τ j⟩) := ⟨_, rfl⟩
  have hval : R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩) = ∑ j, c j • V j := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [_root_.GlobalTheory.XiDecomp.toBcris_xiExt_eq_sum l a e O K t ϖ ι D.toPhiMod w hwS hw hd, map_sum, hV, hc]
    simp only [map_smul]
  have hfix : ∀ j, actB (sQ l) T g (V j) = V j := fun j => by
    rw [hV]
    exact R.horiz g hg _ (hd j)
  have hgval : actB (sQ l) T g (∑ j, c j • V j) = ∑ j, galOB O (sQ l g) (c j) • V j := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change TWact (galOB O (sQ l g)) T g (c j • V j) = _
    rw [TWact_smul]
    change _ • actB (sQ l) T g (V j) = _
    rw [hfix j]
  rw [hval, hgval, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [← sub_smul]
  have h1 : galOB O (sQ l g) (c j) - c j ∈ filO O C η := by
    rw [hc]
    refine _root_.GlobalTheory.BKGal.TaylorFil.gal_iB_sub_mem_filO l a e O K t ϖ C η (fun τ => ⟨w τ j, hwS τ j⟩) (fun τ => mem_tot.1 hwA τ j)
      (fun τ => ?_) g hg
    obtain ⟨h, hh, k, hk⟩ := hN τ j
    exact ⟨h, hh, k, hk⟩
  have h2 : V j ∈ filT C T (-(η : ℤ)) := by
    rw [hV]
    dsimp only
    obtain ⟨u, hu⟩ : ∃ u, u = toBcris t ϖ D.toPhiMod ⟨D.xi (fun _ => Pi.single j 1), hd j⟩ := ⟨_, rfl⟩
    rw [← hu]
    have hsum : u = ∑ i, u i • Pi.single i (1 : OB l O) := by
      ext1 k
      simp [Finset.sum_apply, Pi.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    refine smul_mem_filT_of_zero ?_ (_root_.GlobalTheory.BKGal.XiPole.jB_single_mem_filT l a e O K t ϖ ι η H D T R C i)
    rw [hu, toBcris_apply]
    exact GlobalTheory.T.invariant_lattice_filtration_zero l a e O K t ϖ C _
  exact smul_mem_filT_neg h1 h2
end

