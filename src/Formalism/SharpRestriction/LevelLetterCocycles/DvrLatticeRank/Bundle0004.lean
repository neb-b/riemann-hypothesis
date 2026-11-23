module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LiftPfB
public import Formalism.SharpRestriction.LevelLetterCocycles.MixedPositionHypothesis
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LiftPf
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules Formalism.MainNotions.N.Ln34.CyclotomicLifting

theorem padicValNat_le_of_dvd' (p : ℕ) {a b : ℕ} (hab : a ∣ b) (hb : b ≠ 0) :
    padicValNat p a ≤ padicValNat p b := by
  by_cases hp1 : p = 1
  · subst hp1
    first
      | simp
      | simp [padicValNat]
      | (unfold padicValNat; simp)
  · nth_rw 2 [Nat.padicValNat_def]
    have hd : p ^ padicValNat p a ∣ b := (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _)).trans hab
    have hf : FiniteMultiplicity p b := Nat.finiteMultiplicity_iff.2 ⟨hp1, Nat.pos_of_ne_zero hb⟩
    first
      | exact hf.le_multiplicity_of_pow_dvd hd
      | exact (hf.pow_dvd_iff_le_multiplicity).mp hd

theorem ePB_le_expLift_pf (l M H h : ℕ) (jumps : Finset ℤ) (hM : M ≤ h) (hH : H ≤ 2 * h) :
    Formalism.MainNotions.LiftingTheory.ePB l 1 M H jumps ≤ expLift l h (Formalism.MainNotions.LiftingTheory.JSet jumps M) := by
  unfold Formalism.MainNotions.LiftingTheory.ePB expLift LiftingTheory.eWB LIFT.eU
  have h1 : padicValNat l (2 * H).factorial ≤ padicValNat l (2 * (2 * h)).factorial :=
    padicValNat_le_of_dvd' l (Nat.factorial_dvd_factorial (by omega)) (Nat.factorial_ne_zero _)
  have h2 : padicValNat l M.factorial ≤ padicValNat l h.factorial :=
    padicValNat_le_of_dvd' l (Nat.factorial_dvd_factorial hM) (Nat.factorial_ne_zero _)
  omega

theorem JSet_sub_pf (jumps : Finset ℤ) (M h : ℕ) (hj : ∀ a ∈ jumps, -(h : ℤ) ≤ a ∧ a ≤ h)
    (hM : M ≤ h) :
    Formalism.MainNotions.LiftingTheory.JSet jumps M ⊆ Finset.Icc (-(h : ℤ)) (2 * h) ∧
      (0 : ℤ) ∉ Formalism.MainNotions.LiftingTheory.JSet jumps M := by
  unfold Formalism.MainNotions.LiftingTheory.JSet
  constructor
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨hx, -⟩ := Finset.mem_filter.mp hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
      obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.mp hb
      obtain ⟨ha1, ha2⟩ := hj _ ha
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hx
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro h0
    rcases Finset.mem_union.mp h0 with h0 | h0
    · exact (Finset.mem_filter.mp h0).2 rfl
    · have h1 := (Finset.mem_Icc.mp h0).1
      omega

theorem pow_smul_mem_of_le {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M]
    (S : Submodule O M) (p : O) {e e' : ℕ} (he : e ≤ e') {c : M} (hc : p ^ e • c ∈ S) :
    p ^ e' • c ∈ S := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add, mul_comm, mul_smul]
  exact S.smul_mem _ hc

theorem jumpSet_bound {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (M h : ℕ) (hM : M ≤ h) : ∀ a ∈ Formalism.MainNotions.LiftingTheory.jumpSet W T M M, -(h : ℤ) ≤ a ∧ a ≤ h := by
  classical
  unfold Formalism.MainNotions.LiftingTheory.jumpSet
  intro a ha
  have ha' : a ∈ Finset.Icc (-(M : ℤ)) M := by
    first
      | exact Finset.mem_of_mem_filter a ha
      | (simp only [Finset.mem_filter] at ha; exact ha.1)
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha'
  constructor <;> omega

theorem lift_jumps_bounded {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l)
    {T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)} (Fm : LatHom T₁.L T₂.L) (h n : ℕ)
    (Js : Finset ℤ) (hJb : ∀ a ∈ Js, -(h : ℤ) ≤ a ∧ a ≤ h)
    (hL : Fm.LiftF (P.PD K) (Formalism.MainNotions.LiftingTheory.ePB l 1 (Formalism.MainNotions.LiftingTheory.Mmax n fun _ => h)
      (Formalism.MainNotions.LiftingTheory.Hmax n (fun _ => h) fun _ => h) Js)) :
    ∃ J : Finset ℤ, J ⊆ Finset.Icc (-(h : ℤ)) (2 * h) ∧ (0 : ℤ) ∉ J ∧
      Fm.LiftF (P.PD K) (expLift l h J) := by
  have hMm : Formalism.MainNotions.LiftingTheory.Mmax n (fun _ => h) ≤ h := by
    unfold Formalism.MainNotions.LiftingTheory.Mmax
    exact Finset.sup_le fun _ _ => le_rfl
  have hHm : Formalism.MainNotions.LiftingTheory.Hmax n (fun _ => h) (fun _ => h) ≤ 2 * h := by
    unfold Formalism.MainNotions.LiftingTheory.Hmax
    exact Finset.sup_le fun _ _ => by dsimp only; omega
  obtain ⟨hJ1, hJ2⟩ := JSet_sub_pf Js _ h hJb hMm
  refine ⟨_, hJ1, hJ2, ?_⟩
  have he := ePB_le_expLift_pf l _ _ h Js hMm hHm
  unfold Formalism.WeaklyAdmissibleFiltrations.LatHom.LiftF at hL ⊢
  intro c hc
  exact pow_smul_mem_of_le _ _ he (hL c hc)

theorem lift_bound_of_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ) (hA : Adm1 D HW F Cm CA CB CK) : liftR D := by
  obtain ⟨-, -, -, -, -, -, hA4, -, -, -, hA8, -, hA12⟩ := hA
  obtain ⟨-, -, -, -, hDesc⟩ := hA4
  intro l _ hl K LL hg T₁ T₂ Fm r S η m h up b hH
  have hKK : K.1 ≤ (cycL K).1 := hg.2.2.1
  have hle : GK (cycL K) ≤ GK K := GK_le hKK
  have hg1 : Good (cycL K) 1 LL := by
    refine ⟨le_rfl, fun h2 => absurd h2 hl, ?_, ?_⟩
    · rw [Ks_cycL K]; exact le_rfl
    · rw [Ks_cycL K]; exact hg.2.2.2
  have hD := hDesc l (cycL K) K hKK hle (GKin_normal K hKK) 1 LL hg1
  have hs : ((HW l).W (cycL K) 1 LL hg1).s = 1 := (HW l).W_s _ _ _ _
  have hCB : Formalism.MainNotions.LiftingTheory.CaseB ((HW l).W (cycL K) 1 LL hg1) := by
    refine ⟨?_, ?_⟩
    · rw [eq_top_iff]
      intro g _
      rw [((HW l).W (cycL K) 1 LL hg1).GKs_def, hs, Nat.cast_one, (D.loc l).PD_χ,
        ← map_one (algebraMap ℚ_[l] ↥LL.1), ← map_sub]
      exact v_ge_one _ LL _ (chi_cong (D.loc l) K g g.2)
    · rw [(D.loc l).PD_p, hs, finrank_cycL]
      simp
  have hv0 := hD.2 hCB rfl (by rw [max_unramified_cyclotomic_eq K]; exact inf_le_left)
  have hrange : (Subgroup.inclusion hle).range.Normal := by
    rw [range_inclusion_eq K hKK hle]
    exact GKin_normal K hKK
  have hres := hA12 l (cycL K) K hKK hle LL T₁ hH.1
  have hres2 := hA12 l (cycL K) K hKK hle LL T₂ hH.2.1
  have hL := (hD.1 hrange T₁ T₂ Fm (fun _ => h) (fun _ => h) ⟨hres.1, hres2.1, hH.2.2.1⟩
    (by
      intro i τ _ a ha
      have hm := multV_ne_zero (D.loc l) (cycL K) LL _ τ a ((hA8 l (cycL K) LL _).2 τ).1 ha
      rw [hres.2 τ a] at hm
      have := hH.2.2.2.2.2.2.2.1 (τ.comp (IntermediateField.inclusion hKK)) a
        (isJump_of_multV (D.loc l) K LL T₁ _ a hm)
      simpa using this)).2 hCB
  rw [(D.loc l).PD_p, hv0, add_zero, hs] at hL
  exact lift_jumps_bounded (D.loc l) K LL Fm h _ _
    (jumpSet_bound (D.loc l) (cycL K) LL _ _ _ h (Finset.sup_le fun _ _ => le_rfl)) hL

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.QuotPf
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem qpf_filV_succ_le (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  have h : (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp := fun x hx => PD.Fil_anti a hx
  intro x hx
  rw [FilV, LinearMap.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine ⟨AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion h) y, ?_⟩
  rw [← LinearMap.comp_apply, ← AlgebraTensorModule.map_comp, LinearMap.id_comp, Submodule.subtype_comp_inclusion]

theorem qpf_fildR_succ_le (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a := by
  unfold FildR
  exact inf_le_inf_left _ (qpf_filV_succ_le PD a)

theorem qpf_isJumpV_iff_pos (τ : K →ₐ[Qp] LL) (hfin : Module.Finite LL ↥(DdRE PD ρ τ)) (a : ℤ) :
    IsJumpV PD ρ τ a ↔ 0 < multV PD ρ τ a := by
  have hle := qpf_fildR_succ_le PD ρ τ a
  haveI := hfin
  haveI : Module.Finite LL ↥(FildR PD ρ τ a) :=
    Module.Finite.of_injective (Submodule.inclusion (inf_le_left : FildR PD ρ τ a ≤ DdRE PD ρ τ))
      (Submodule.inclusion_injective _)
  unfold IsJumpV multV
  constructor
  · intro hne
    have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)
    omega
  · intro hpos heq
    rw [heq] at hpos
    simp at hpos

theorem qpf_multV_nonneg (τ : K →ₐ[Qp] LL) (hfin : Module.Finite LL ↥(DdRE PD ρ τ)) (a : ℤ) :
    0 ≤ multV PD ρ τ a := by
  by_cases h : FildR PD ρ τ (a + 1) = FildR PD ρ τ a
  · unfold multV
    rw [h]
    simp
  · exact le_of_lt ((qpf_isJumpV_iff_pos PD ρ τ hfin a).1 h)

end Gen

theorem quotient_jumps_subset (D : D7) (h8 : adm8 D) (h11 : adm11 D) : quotR D := by
  unfold quotR
  intro l _ hl2 K LL hG
  unfold quotA
  intro T₁ T₂ F hc1 hc2 hon τ X hJ a ha
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  have hden : Formalism.MainNotions.LiftingTheory.lker_Den ↥LL.1 ↥(OL LL) := by
    intro c
    have hint : IsIntegral ℚ_[l] c := Algebra.IsIntegral.isIntegral c
    have halg : IsAlgebraic ℤ_[l] c := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 hint.isAlgebraic
    have hinj : Function.Injective (algebraMap ℤ_[l] ↥LL.1) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1]
      exact (algebraMap ℚ_[l] ↥LL.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
    obtain ⟨y, hy, hyc⟩ : ∃ y ≠ (0 : ℤ_[l]), IsIntegral ℤ_[l] (y • c) := by
      exact IsAlgebraic.exists_integral_multiple halg
    refine ⟨algebraMap ℤ_[l] ↥(OL LL) y, ?_, ⟨y • c, hyc⟩, ?_⟩
    · rw [← IsScalarTower.algebraMap_apply]
      exact fun h => hy (hinj (h.trans (map_zero _).symm))
    · rw [← IsScalarTower.algebraMap_apply]
      change _ = y • c
      rw [Algebra.smul_def]
  have hses : IsSESLat (Qp := ℚ_[l]) (Formalism.MainNotions.LiftingTheory.lker_ι F hon hden) F := by
    refine ⟨(LinearMap.ker F.f).injective_subtype, Formalism.MainNotions.LiftingTheory.lker_surj F hon, hon,
      fun x => ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, ?_⟩, fun y hy => hy⟩
    rintro ⟨y, rfl⟩
    exact LinearMap.mem_ker.1 y.2
  obtain ⟨-, -, hmult⟩ := h11 l K LL _ T₁ T₂ (Formalism.MainNotions.LiftingTheory.lker_ι F hon hden) F hses hc1
  apply hJ
  rw [qpf_isJumpV_iff_pos _ _ τ ((h8 l K LL T₂).2 τ).1] at ha
  rw [qpf_isJumpV_iff_pos _ _ τ ((h8 l K LL T₁).2 τ).1, hmult τ a]
  have h0 := qpf_multV_nonneg _ _ τ ((h8 l K LL (Formalism.MainNotions.LiftingTheory.lker_T₀ F hon hden)).2 τ).1 a
  omega

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniformiserRingOfHypotheses
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem uniformiser_ring_of_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : adm1 D HW F Cm) : p9R D HW := by
  unfold adm1 Formalism.MainNotions.DeltaInvariantLattices.deltaInvariantLatticeGlobal Formalism.MainNotions.DeltaInvariantLattices.deltaInvariantLatticeLocal at h1
  intro l _ hl K LL hG T hT
  have h9 := (h1 l K 1 LL hG).2.2.2.2.2.2.2.2.1 T hT
  unfold Formalism.MainNotions.DeltaInvariantLattices.p9 at h9
  have hpe : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hs : ((HW l).W K 1 LL hG).s = 1 := by
    first
    | exact (HW l).W_s K 1 LL hG
    | exact (HW l).hs K 1 LL hG
    | exact (HW l).s_eq K 1 LL hG
    | exact (HW l).W_s
    | rfl
  obtain ⟨-, ⟨π', E, hr, -⟩, -⟩ := h9 hs (by rw [hpe]; exact hl)
  refine ⟨π', E, ?_⟩
  convert hr using 2 <;> first | rfl | (simp only [eK, sK, hpe]) | (unfold eK sK; simp [hpe])

end Formalism.MainNotions.N.Ln34

end
end

