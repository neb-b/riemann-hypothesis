module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0025
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0021
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.PhibOLComplete

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrobeniusSpanDecomposition
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section KerLam2Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

private theorem kl2_dec_lemma (W : LocWach PD LL O v n) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    (T : LocLat G Qp LL O) (S : Submodule (LetA O n) (W.DD T)) (a : LetA O n) (s : W.DD T) (hs : s ∈ S) :
    ∃ t : Fin PD.p → W.DD T, (∀ k, t k ∈ S) ∧
      a • W.φD T s = ∑ k : Fin PD.p, (letπ : LetA O n) ^ (k : ℕ) • W.φD T (t k) := by
  obtain ⟨e, he⟩ := Formalism.MainNotions.LiftingTheory.PhiBasis_of W a
  refine ⟨fun k => e k • s, fun k => S.smul_mem _ hs, ?_⟩
  rw [he, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Formalism.MainNotions.LiftingTheory.wmap_φD_smul, mul_smul]

theorem frobenius_span_decomposition (W : LocWach PD LL O v n) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    (T : LocLat G Qp LL O) (S : Submodule (LetA O n) (W.DD T)) (z : W.DD T)
    (hz : z ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T S) :
    ∃ s : Fin PD.p → W.DD T, (∀ k, s k ∈ S) ∧
      z = ∑ k : Fin PD.p, (letπ : LetA O n) ^ (k : ℕ) • W.φD T (s k) := by
  unfold Formalism.MainNotions.DeltaInvariantLattices.φspan at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, he⟩ := kl2_dec_lemma W T S 1 s hs
    exact ⟨t, ht, by rw [← he, one_smul]⟩
  | zero => exact ⟨fun _ => 0, fun _ => S.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨s', hs', rfl⟩ := hy
    exact ⟨fun k => s k + s' k, fun k => S.add_mem (hs k) (hs' k),
      by simp only [map_add (f := _), smul_add, Finset.sum_add_distrib]⟩
  | smul a x _ hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    choose t ht he using fun k : Fin PD.p =>
      kl2_dec_lemma W T S (a * (letπ : LetA O n) ^ (k : ℕ)) (s k) (hs k)
    refine ⟨fun j => ∑ k, t k j, fun j => S.sum_mem fun k _ => ht k j, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.smul_sum, ← mul_smul, he, map_sum]
    rw [Finset.sum_comm]

theorem frobenius_span_exact_lift (W : LocWach PD LL O v n) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    {T Tp T'' : LocLat G Qp LL O} (ι : LatHom T.L Tp.L) (π : LatHom Tp.L T''.L)
    (c'' : IsCrys PD T''.ρ) (hinj : Function.Injective (W.map ι))
    (hex : ∀ x, W.map π x = 0 → ∃ y, W.map ι y = x)
    (h4 : ∀ x : W.DD T, W.map ι x ∈ W.N Tp → x ∈ W.N T) (i : ZMod n)
    (z : W.DD Tp) (hz : z ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W Tp (W.Nl Tp i)) (h0 : W.map π z = 0) :
    ∃ z' ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T i), W.map ι z' = z := by
  obtain ⟨s, hs, rfl⟩ := frobenius_span_decomposition W Tp (W.Nl Tp i) z hz
  have hπs : ∀ k, W.map π (s k) = 0 := by
    refine Formalism.MainNotions.LiftingTheory.phii_DD W T'' c'' (fun k => W.map π (s k)) ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h0, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, W.map_φ]
  choose y hy using fun k => hex (s k) (hπs k)
  have hyNl : ∀ k, y k ∈ W.Nl T i := by
    intro k
    obtain ⟨w, hw, hwe⟩ := (Formalism.MainNotions.LiftingTheory.wmap_mem_Nl W Tp i (s k)).1 (hs k)
    have hyN : y k ∈ W.N T := by
      apply h4
      rw [hy k, ← hwe]
      exact (W.N Tp).smul_mem _ hw
    rw [Formalism.MainNotions.LiftingTheory.wmap_mem_Nl]
    refine ⟨y k, hyN, ?_⟩
    apply hinj
    rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, hy k, Formalism.MainNotions.LiftingTheory.wmap_Nl_fix W Tp i (s k) (hs k)]
  refine ⟨∑ k : Fin PD.p, (letπ : LetA O n) ^ (k : ℕ) • W.φD T (y k), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    unfold Formalism.MainNotions.DeltaInvariantLattices.φspan
    exact Submodule.subset_span ⟨y k, hyNl k, rfl⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, W.map_φ, hy k]

theorem frobenius_span_exact_local (W : LocWach PD LL O v n) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    {T Tp T'' : LocLat G Qp LL O} (ι : LatHom T.L Tp.L) (π : LatHom Tp.L T''.L)
    (π' Eπ : LetA O n) (h' : ℕ) (c'' : IsCrys PD T''.ρ)
    (hinj : Function.Injective (W.map ι))
    (hex : ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x)
    (h4 : ∀ x : W.DD T, W.map ι x ∈ W.N Tp → x ∈ W.N T)
    (hπ' : IsUnit (algebraMap (LetA O n) W.EE π')) :
    KerLam W ι π π' Eπ h' := by
  have hex' : ∀ x, W.map π x = 0 → ∃ y, W.map ι y = x := fun x hx => (hex x).1 hx
  have hΔ : ∀ x : W.DD T, (∀ δ ∈ W.DelF, W.γD Tp δ (W.map ι x) = W.map ι x) →
      ∀ δ ∈ W.DelF, W.γD T δ x = x := by
    intro x hx δ hδ
    apply hinj
    rw [W.map_γ, hx δ hδ]
  have hL : ∀ (x : W.DD T) (a : LetA O n), a • W.map ι x = W.map ι x → a • x = x := by
    intro x a hx
    apply hinj
    rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, hx]
  refine ⟨hinj, ?_, fun c => ⟨?_, ?_⟩⟩
  · intro k y hy hyπ
    rw [mem_PiNS] at hy
    obtain ⟨⟨y0, hy0N, rfl⟩, hyΔ⟩ := hy
    have hz : W.map π y0 = 0 := by
      have hu : IsUnit (algebraMap (LetA O n) W.EE (π' ^ k)) := by
        rw [map_pow]
        exact hπ'.pow k
      rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, ← algebraMap_smul W.EE] at hyπ
      exact (hu.smul_eq_zero).1 hyπ
    obtain ⟨x0, rfl⟩ := hex' y0 hz
    refine ⟨π' ^ k • x0, ?_, Formalism.MainNotions.LiftingTheory.wmap_map_smul W ι _ _⟩
    rw [mem_PiNS]
    refine ⟨⟨x0, h4 x0 hy0N, rfl⟩, hΔ _ ?_⟩
    rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul]
    exact hyΔ
  · intro y hy hyπ
    rw [mem_LamPS] at hy
    obtain ⟨hyE, hyΔ, hyL⟩ := hy
    obtain ⟨x, rfl⟩ := hex' y hyπ
    obtain ⟨z', hz', hz'e⟩ := frobenius_span_exact_lift W ι π c'' hinj hex' h4 (c - 1) (Eπ ^ h' • W.map ι x) hyE
      (by rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, hyπ, smul_zero])
    refine ⟨x, ?_, rfl⟩
    rw [mem_LamPS]
    refine ⟨?_, hΔ x hyΔ, hL x _ hyL⟩
    have e : z' = Eπ ^ h' • x := hinj (by rw [hz'e, Formalism.MainNotions.LiftingTheory.wmap_map_smul])
    rw [← e]
    exact hz'
  · intro y hy hyπ
    rw [mem_NcS] at hy
    obtain ⟨hyN, hyΔ, hyL⟩ := hy
    obtain ⟨x, rfl⟩ := hex' y hyπ
    refine ⟨x, ?_, rfl⟩
    rw [mem_NcS]
    exact ⟨h4 x hyN, hΔ x hyΔ, hL x _ hyL⟩

end KerLam2Local

theorem kerlam2_pf : KerLamStep := by
  unfold KerLamStep kerLamR
  intro D HW F Cm CA CB CK hA hF l _ hl K LL hG π' E hp9 T Tp T'' ι π h' hses hT hTp hT'' hJ
  obtain ⟨hW, -⟩ := hA
  obtain ⟨-, -, -, -, -, h6W, -⟩ := hW l K 1 LL hG
  obtain ⟨-, -, h6ses⟩ := h6W
  obtain ⟨-, -, -, hsat, -⟩ := h6ses T Tp T'' ι π hT hTp hT'' hses
  have hEx := hF l K 1 LL hG T Tp T'' ι π hses
  obtain ⟨-, -, ⟨w, hw⟩, -⟩ := hp9
  have e : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  letI : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [e]
    exact Formalism.MainNotions.LiftingTheory.phib_OL_complete LL
  refine frobenius_span_exact_local _ ι π π' _ h' hT'' hEx.1 hEx.2.2 hsat ?_
  rw [hw, map_mul, map_pow]
  exact (w.isUnit.map _).mul (by simpa using (Formalism.MainNotions.LiftingTheory.wmap_unit _ 0).pow _)

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GamPiPf
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

theorem gampi_delta {x : W.DD T} (hx : ∀ δ ∈ W.DelF, W.γD T δ x = x) :
    ∀ δ ∈ W.DelF, W.γD T δ (W.γD T W.gamK x - x) = W.γD T W.gamK x - x := by
  intro δ hδ
  rw [map_sub, ← W.γD_mul, mul_comm, W.γD_mul, hx δ hδ]

theorem gampi_letter (c : ZMod n) {x : W.DD T} (hx : x ∈ letS W T c) :
    W.γD T W.gamK x - x ∈ letS W T c := by
  have hl : letγ (W.γ₀ W.gamK) (letE c : LetA O n) = letE c := by
    funext j
    show W.γ₀ W.gamK ((letE c : LetA O n) j) = (letE c : LetA O n) j
    rcases eq_or_ne j c with rfl | h
    · simp [letE]
    · simp [letE, Pi.single_apply, h]
  have key : ∀ y : W.DD T, W.γD T W.gamK ((letE c : LetA O n) • y) = (letE c : LetA O n) • W.γD T W.gamK y := by
    intro y
    rw [← algebraMap_smul W.EE (letE c : LetA O n) y, W.γD_smul, W.γE_ext, hl, algebraMap_smul]
  unfold letS at hx ⊢
  rw [LinearMap.mem_ker] at hx ⊢
  simp only [LinearMap.restrictScalars_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at hx ⊢
  rw [smul_sub, ← key, sub_eq_zero.1 hx, sub_self]

theorem gampi_local (π' π'₀ u : LetA O n) (hu : π'₀ = u * π')
    (hm : ∀ x ∈ W.NΔ T, ∃ x' ∈ W.NΔ T, W.γD T W.gamK x - x = π'₀ • x') :
    GamPi W T π' := by
  intro c x hx
  unfold NcS at hx
  rw [Submodule.mem_inf, Submodule.mem_inf] at hx
  obtain ⟨⟨hxN, hxD⟩, hxL⟩ := hx
  rw [Submodule.restrictScalars_mem] at hxN
  have hxfix : ∀ δ ∈ W.DelF, W.γD T δ x = x := by
    intro δ hδ
    unfold DelS at hxD
    have h1 := (Submodule.mem_iInf _).1 hxD δ
    have h2 := (Submodule.mem_iInf _).1 h1 hδ
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h2
    exact h2
  have hxΔ : x ∈ W.NΔ T := show x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x from ⟨hxN, hxfix⟩
  obtain ⟨x', hx'mem, hx'⟩ := hm x hxΔ
  have hx'N : x' ∈ W.N T := (show x' ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ x' = x' from hx'mem).1
  rw [Submodule.mem_inf]
  refine ⟨?_, gampi_letter W T c hxL⟩
  unfold PiNS
  rw [Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [Submodule.restrictScalars_mem]
    unfold Formalism.MainNotions.DeltaInvariantLattices.aN
    refine Submodule.mem_map.2 ⟨u • x', (W.N T).smul_mem u hx'N, ?_⟩
    unfold Formalism.MainNotions.DeltaInvariantLattices.smulA
    rw [LinearMap.smul_apply, LinearMap.id_apply, hx', hu, pow_one, smul_smul, mul_comm]
  · unfold DelS
    rw [Submodule.mem_iInf]
    intro δ
    rw [Submodule.mem_iInf]
    intro hδ
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    exact gampi_delta W T hxfix δ hδ

end Local

theorem gamPiCondition : GamPiStep := by
  intro D HW F Cm CA CB CK hA l _ hl K LL hG π' E hp9 T hcrys
  have hT1 := hA.1 l K 1 LL hG
  have hP9 := hT1.2.2.2.2.2.2.2.2.1
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp2 : ((D.loc l).PD K).p ≠ 2 := by rw [hp]; exact hl
  obtain ⟨-, ⟨π₁, E₁, hr₁, hm₁⟩, -⟩ := hP9 T hcrys hs1 hp2
  obtain ⟨w₁, hw₁⟩ := hr₁.2.2.1
  obtain ⟨w, hw⟩ := hp9.2.2.1
  have hgam : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs1 hp2
  refine gampi_local _ T π' π₁ ((w₁ * w⁻¹ : (LetA _ _)ˣ) : LetA _ _) ?_ ?_
  · rw [hw₁, hw, hp, Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
  · intro x hx
    obtain ⟨x', hx', h⟩ := hm₁.2 x hx
    exact ⟨x', hx', by rw [hgam]; exact h⟩

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfA
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

private theorem gammaA_letE_eq_letE (g : W.Gam) (c : ZMod n) : W.γA g (letE c) = (letE c : LetA O n) := by
  funext i
  change (W.γ₀ g) ((letE c : LetA O n) i) = (letE c : LetA O n) i
  by_cases h : i = c
  · subst h; simp [letE]
  · simp [letE, h]

theorem gradNPf_γD_smul (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have h := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at h
  first
  | exact h
  | simpa [Formalism.BasicNotions.LocWach.γA] using h

theorem gradNPf_tf (a : LetA O n) (ha : IsUnit (algebraMap (LetA O n) W.EE a)) (x : W.DD T)
    (hx : a • x = 0) : x = 0 := by
  obtain ⟨u, hu⟩ := ha
  have h1 : (algebraMap (LetA O n) W.EE a) • x = 0 := by rw [algebraMap_smul]; exact hx
  calc x = (↑(u⁻¹) : W.EE) • ((↑u : W.EE) • x) := by rw [smul_smul, Units.inv_mul, one_smul]
    _ = 0 := by rw [hu, h1, smul_zero]

private theorem mem_DelS_iff_forall_gammaD_fixed {x : W.DD T} : x ∈ DelS W T ↔ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
  first
  | exact mem_DelS W T x
  | simp only [DelS, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]

theorem gradNPf_DelS_γ (g : W.Gam) {x : W.DD T} (hx : x ∈ DelS W T) : W.γD T g x ∈ DelS W T := by
  have hx' := (mem_DelS_iff_forall_gammaD_fixed W T).mp hx
  refine (mem_DelS_iff_forall_gammaD_fixed W T).mpr fun δ hδ => ?_
  rw [← W.γD_mul, mul_comm, W.γD_mul, hx' δ hδ]

private theorem mem_letS_iff_letE_smul_eq (c : ZMod n) {x : W.DD T} :
    x ∈ letS W T c ↔ (letE c : LetA O n) • x = x := by
  first
  | exact mem_letS W T c x
  | simp only [letS, LinearMap.mem_ker, LinearMap.restrictScalars_apply, LinearMap.coe_restrictScalars,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem gradNPf_letS_γ (g : W.Gam) (c : ZMod n) {x : W.DD T} (hx : x ∈ letS W T c) :
    W.γD T g x ∈ letS W T c := by
  have hx' := (mem_letS_iff_letE_smul_eq W T c).mp hx
  refine (mem_letS_iff_letE_smul_eq W T c).mpr ?_
  rw [← gammaA_letE_eq_letE W g c, ← gradNPf_γD_smul W T g (letE c) x, hx']

theorem gradNPf_PiNS_DelS (π' : LetA O n) (k : ℕ) {x : W.DD T} (hx : x ∈ PiNS W T π' k) :
    x ∈ DelS W T := by
  first
  | exact (Submodule.mem_inf.mp hx).2
  | (simp only [PiNS, Submodule.mem_inf] at hx; exact hx.2)

theorem gradNPf_PiNS_anti (π' : LetA O n) {j k : ℕ} (h : j ≤ k) {x : W.DD T}
    (hx : x ∈ PiNS W T π' k) : x ∈ PiNS W T π' j := by
  simp only [PiNS, Formalism.MainNotions.DeltaInvariantLattices.aN, Submodule.mem_inf, Submodule.restrictScalars_mem,
    Submodule.mem_map] at hx ⊢
  obtain ⟨⟨y, hy, rfl⟩, h2⟩ := hx
  refine ⟨⟨π' ^ (k - j) • y, Submodule.smul_mem _ _ hy, ?_⟩, h2⟩
  change π' ^ j • (π' ^ (k - j) • y) = π' ^ k • y
  rw [smul_smul, ← pow_add, Nat.add_sub_of_le h]

theorem exists_gam_pow_smul_sub_eq (π' f t : LetA O n) (c₀ : O) (hf : W.γA W.gam π' = π' * f)
    (ht : f - algebraMap O (LetA O n) c₀ = π' * t)
    (hγN : ∀ x ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam x - x = π' • d)
    (y : ℕ) (r₀ : W.DD T) (hr₀ : r₀ ∈ W.NΔ T) :
    ∃ w ∈ W.N T, W.γD T W.gam (π' ^ y • r₀) - π' ^ y • r₀ - (c₀ ^ y - 1) • (π' ^ y • r₀) =
      π' ^ (y + 1) • w := by
  have hr₀N : r₀ ∈ W.N T := hr₀.1
  obtain ⟨d, hdN, hd⟩ := hγN r₀ hr₀
  have hd' : W.γD T W.gam r₀ = r₀ + π' • d := sub_eq_iff_eq_add'.mp hd
  obtain ⟨e, he⟩ := sub_dvd_pow_sub_pow f (algebraMap O (LetA O n) c₀) y
  rw [ht] at he
  have hs : f ^ y = algebraMap O (LetA O n) c₀ ^ y + π' * (t * e) := by linear_combination he
  refine ⟨(t * e) • r₀ + f ^ y • d, Submodule.add_mem _ (Submodule.smul_mem _ _ hr₀N)
    (Submodule.smul_mem _ _ hdN), ?_⟩
  rw [gradNPf_γD_smul, map_pow, hf, mul_pow, hd', ← algebraMap_smul (LetA O n) (c₀ ^ y - 1)]
  simp only [map_sub, map_pow, map_one]
  simp only [smul_add, smul_smul]
  have c2 : π' ^ y * f ^ y * π' = π' ^ (y + 1) * f ^ y := by ring
  have c1 : π' ^ (y + 1) * (t * e) =
      π' ^ y * f ^ y - π' ^ y - (algebraMap O (LetA O n) c₀ ^ y - 1) * π' ^ y := by
    rw [hs]; ring
  rw [c2, c1, sub_smul, sub_smul]
  abel

theorem gradNPf_coker (π' f t : LetA O n) (c₀ : O) (hf : W.γA W.gam π' = π' * f)
    (ht : f - algebraMap O (LetA O n) c₀ = π' * t)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hγN : ∀ x ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam x - x = π' • d)
    (c : ZMod n) (z : W.DD T) (hz : z ∈ PiNS W T π' 1 ⊓ letS W T c) (k : ℕ) (hk : 1 ≤ k) :
    ∃ x ∈ PiNS W T π' 1 ⊓ letS W T c,
      (∏ y ∈ Finset.Ico 1 k, (c₀ ^ y - 1)) • z - (W.γD T W.gam x - x) ∈
        PiNS W T π' k ⊓ letS W T c := by
  induction k, hk using Nat.le_induction with
  | base =>
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    simp only [Finset.Ico_self, Finset.prod_empty, one_smul, map_zero, sub_zero]
    exact hz
  | succ k hk ih =>
    obtain ⟨xk, hxk, hr⟩ := ih
    set R := (∏ y ∈ Finset.Ico 1 k, (c₀ ^ y - 1)) • z - (W.γD T W.gam xk - xk) with hR
    have hrP := (Submodule.mem_inf.mp hr).1
    have hrL := (Submodule.mem_inf.mp hr).2
    have hrP' := hrP
    simp only [PiNS, Formalism.MainNotions.DeltaInvariantLattices.aN, Submodule.mem_inf, Submodule.restrictScalars_mem,
      Submodule.mem_map] at hrP'
    obtain ⟨⟨r', hr'N, hr'eq⟩, hrΔ⟩ := hrP'
    have hr'eq' : π' ^ k • r' = R := hr'eq
    have hΔr := (mem_DelS_iff_forall_gammaD_fixed W T).mp hrΔ
    have hr'Δ : r' ∈ W.NΔ T := by
      show r' ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ r' = r'
      refine ⟨hr'N, fun δ hδ => ?_⟩
      have h2 : W.γA δ (π' ^ k) = π' ^ k := by rw [map_pow, hπΔ δ hδ]
      have h1 : π' ^ k • (W.γD T δ r' - r') = 0 := by
        rw [smul_sub, ← h2, ← gradNPf_γD_smul, h2, hr'eq', hΔr δ hδ, sub_self]
      have hu' : IsUnit (algebraMap (LetA O n) W.EE (π' ^ k)) := by
        rw [map_pow]; exact hu.pow k
      exact sub_eq_zero.mp (gradNPf_tf W T (π' ^ k) hu' _ h1)
    obtain ⟨w, hwN, hw⟩ := exists_gam_pow_smul_sub_eq W T π' f t c₀ hf ht hγN k r' hr'Δ
    rw [hr'eq'] at hw
    have hxkP := (Submodule.mem_inf.mp hxk).1
    have hxkL := (Submodule.mem_inf.mp hxk).2
    have hzP := (Submodule.mem_inf.mp hz).1
    have hzL := (Submodule.mem_inf.mp hz).2
    have hRP1 : R ∈ PiNS W T π' 1 := gradNPf_PiNS_anti W T π' hk hrP
    have hxP : (c₀ ^ k - 1) • xk + R ∈ PiNS W T π' 1 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ hxkP) hRP1
    have hxL : (c₀ ^ k - 1) • xk + R ∈ letS W T c :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ hxkL) hrL
    refine ⟨(c₀ ^ k - 1) • xk + R, Submodule.mem_inf.mpr ⟨hxP, hxL⟩, ?_⟩
    have hPz : (∏ y ∈ Finset.Ico 1 k, (c₀ ^ y - 1)) • z = R + (W.γD T W.gam xk - xk) := by
      rw [hR]; abel
    have hE : (∏ y ∈ Finset.Ico 1 (k + 1), (c₀ ^ y - 1)) • z -
        (W.γD T W.gam ((c₀ ^ k - 1) • xk + R) - ((c₀ ^ k - 1) • xk + R)) = π' ^ (k + 1) • (-w) := by
      rw [Finset.prod_Ico_succ_top hk, mul_comm, mul_smul, hPz, map_add (f := _), map_smul, smul_neg, ← hw]
      simp only [smul_add, smul_sub]
      abel
    have hγxP : W.γD T W.gam ((c₀ ^ k - 1) • xk + R) ∈ DelS W T :=
      gradNPf_DelS_γ W T W.gam (gradNPf_PiNS_DelS W T π' 1 hxP)
    have hγxL := gradNPf_letS_γ W T W.gam c hxL
    have hzΔ := gradNPf_PiNS_DelS W T π' 1 hzP
    have hxΔ := gradNPf_PiNS_DelS W T π' 1 hxP
    rw [PiNS]
    refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [hE]
      exact (Submodule.restrictScalars_mem _ _ _).mpr
        (Submodule.mem_map.mpr ⟨-w, Submodule.neg_mem _ hwN, rfl⟩)
    · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hzΔ) (Submodule.sub_mem _ hγxP hxΔ)
    · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hzL) (Submodule.sub_mem _ hγxL hxL)

theorem gradNPf_local (π' f t : LetA O n) (c₀ : O) (hf : W.γA W.gam π' = π' * f)
    (ht : f - algebraMap O (LetA O n) c₀ = π' * t)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hγN : ∀ x ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam x - x = π' • d)
    (hK : W.gamK = W.gam) (σ M : ℕ) (hM : 1 ≤ M) (a : O)
    (ha : ((PD.p : ℕ) : O) ^ σ = a * ∏ y ∈ Finset.Ico 1 M, (c₀ ^ y - 1)) :
    GradN W T π' σ M := by
  intro c z hz
  obtain ⟨x, hx, hr⟩ := gradNPf_coker W T π' f t c₀ hf ht hu hπΔ hγN c z hz M hM
  refine ⟨a • x, Submodule.smul_mem _ _ hx, ?_⟩
  have e : ((PD.p : ℕ) : O) ^ σ • z - (W.γD T W.gamK (a • x) - a • x) =
      a • ((∏ y ∈ Finset.Ico 1 M, (c₀ ^ y - 1)) • z - (W.γD T W.gam x - x)) := by
    rw [hK, ha, map_smul, mul_smul, smul_sub, smul_sub]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.mem_inf.1 hr).1

theorem gradNPf_small (π' : LetA O n) (σ M : ℕ) (hM : M ≤ 1) : GradN W T π' σ M := by
  unfold GradN
  intro c z hz
  refine ⟨0, Submodule.zero_mem _, ?_⟩
  simp only [map_zero, sub_zero]
  exact gradNPf_PiNS_anti W T π' hM (Submodule.smul_mem _ _ (Submodule.mem_inf.mp hz).1)

end Local

end Formalism.MainNotions.N.Ln34

end
end

