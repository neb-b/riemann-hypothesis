module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0014
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0012
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0003

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfD
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.ModelFPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' M σ : ℕ) (c : ZMod n) (α : FrA W π' Eπ h' M c) (β : FrB W π' Eπ h' M c)

theorem alpha_core (hfr : IsFrame W Pt π' Eπ h' M σ c α β) (hcry : IsCrys PD T.ρ)
    (hjmp : ∀ τ, JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) (hs : W.s = 1) {w w' : LetA O n}
    (hww : w' * w = 1) (hQ : W.Q = w * Eπ)
    (h5a : ∀ x ∈ W.Nl T (c - 1), W.Q ^ h' • W.φD T x ∈ W.N T) (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hpt : ∀ ζ τ, Pt c ζ τ → ζ ^ PD.p = 1 ∧ ζ ≠ 1) (hexp : ExpansionFormLetter W T Pt)
    (x : LA W T π' c) (hx : x ∈ LamLA W T π' Eπ h' c ⊤) (hxS : x ∈ NLset W T Pt π' Eπ h' c)
    (y0 : W.DD T) (hy0 : y0 ∈ LamPS W T Eπ h' c) (hα : α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y0 hy0) :
    y0 ∈ W.N T := by
  obtain ⟨h1, h2, h3⟩ := (mem_LamPS W T Eπ h' c y0).1 hy0
  have hE2 : Eπ ^ h' • (Eπ ^ h' • y0) ∈ W.N T := Eπ_φspan W T Eπ h' c hww hQ h5a h1
  have eEQ : Eπ ^ h' = w' ^ h' * W.Q ^ h' := by
    rw [hQ, mul_pow, ← mul_assoc, ← mul_pow, hww, one_pow, one_mul]
  refine hexp c y0 ((mem_DelS W T y0).2 h2) ((mem_letS W T c y0).2 h3) ⟨2 * h', ?_⟩ ?_
  · rw [hQ, mul_pow, mul_smul, show Eπ ^ (2 * h') = Eπ ^ h' * Eπ ^ h' by rw [two_mul, pow_add],
      mul_smul]
    exact Submodule.smul_mem _ _ hE2
  · intro ζ τ hPt k hk i
    obtain ⟨hc0, hc1⟩ := levQ_pt W hs c ζ (hpt ζ τ hPt).1 (hpt ζ τ hPt).2
    obtain ⟨m, a, z, hrep, hfil⟩ := hxS
    have e1 : W.Q ^ k • (Eπ ^ h' • y0) = (w' ^ h' * W.Q ^ h') • (W.Q ^ k • y0) := by
      rw [eEQ, smul_smul, smul_smul, mul_comm (W.Q ^ k)]
    have hQΛ : W.Q ^ k • (Eπ ^ h' • y0) ∈ W.N T := e1 ▸ Submodule.smul_mem _ _ hk
    have hF : ∀ i' : ℤ, W.levN T c ζ ⟨_, hQΛ⟩ i' ∈
        Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((k : ℤ) + h' - i') := by
      intro i'
      rcases lt_or_ge i' ((k : ℤ) + 4 * h') with hi | hi
      · rw [(hfr.1 T hcry hjmp).2.2.2.2.2.2.2.2 τ ζ hPt x hx y0 hy0 hα m a z hrep k hQΛ i' hi]
        refine nsmul_mem ?_ _
        have := serMul_mem (fun i => Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((h' : ℤ) - i))
          (FilC_mono_shift T τ _) (W.lev c ζ (W.Q ^ k)) k
          (by rw [map_pow]; exact pow_vanish' _ hc0 k) _ (hfil τ ζ hPt) i'
        convert this using 2
        ring
      · have h0 := (Submodule.mem_inf.1 (levN_fil W T c hp4 hPt ⟨_, hQΛ⟩ i')).2
        exact FilC_anti T τ (by omega) (FilC_top T h' τ (hjmp τ) _ h0)
    have hsub : (⟨_, hQΛ⟩ : ↥(W.N T)) = (w' ^ h' * W.Q ^ h') • (⟨_, hk⟩ : ↥(W.N T)) :=
      Subtype.ext e1
    obtain ⟨m₀, hm₀⟩ := W.levN_supp T c ζ ⟨_, hk⟩
    obtain ⟨B', hB'⟩ := PowerSeries.X_dvd_iff.2 hc0
    have hw0 : PowerSeries.constantCoeff (W.lev c ζ w') ≠ 0 := by
      intro h
      have hw : PowerSeries.constantCoeff (W.lev c ζ w') *
          PowerSeries.constantCoeff (W.lev c ζ w) = 1 := by
        rw [← map_mul, ← map_mul, hww, map_one, map_one]
      rw [h, zero_mul] at hw
      exact zero_ne_one hw
    have hB0 : PowerSeries.constantCoeff B' ≠ 0 := by
      rw [hB', PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply] at hc1
      exact hc1
    have eg : W.lev c ζ (w' ^ h' * W.Q ^ h') =
        PowerSeries.X ^ h' * (W.lev c ζ w' ^ h' * B' ^ h') := by
      rw [map_mul, map_pow, map_pow, hB', mul_pow]
      ring
    refine serMul_inv (fun i => Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((k : ℤ) - i)) (FilC_mono_shift T τ _)
      (W.lev c ζ (w' ^ h' * W.Q ^ h')) h' ?_ ?_ (W.levN T c ζ ⟨_, hk⟩) m₀ hm₀ ?_ i
    · intro j hj
      rw [eg, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
    · rw [eg, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, map_pow]
      exact mul_ne_zero (pow_ne_zero _ hw0) (pow_ne_zero _ hB0)
    · intro i''
      rw [← levN_eq_serMul, ← hsub]
      have := hF (i'' + h')
      convert this using 2
      ring

end Core

end Formalism.MainNotions.N.Ln34.ModelFPf

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfC
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem filC_le_bot (τ : K →ₐ[Qp] LL) (h' : ℕ)
    (hJ : JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) (a : ℤ) :
    Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a ≤ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-(h' : ℤ)) := by
  by_cases ha : -(h' : ℤ) ≤ a
  · exact u3upPf_FilC_anti (PD := PD) T τ ha
  · have hc : ∀ j : ℕ, FildR PD T.ρ τ (-(h' : ℤ) - j) = FildR PD T.ρ τ (-(h' : ℤ)) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hnj : ¬ IsJumpV PD T.ρ τ (-(h' : ℤ) - (j + 1 : ℕ)) := by
          intro hj
          have := (hJ _ hj).1
          push_cast at this
          omega
        unfold IsJumpV at hnj
        push Not at hnj
        rw [← ih, ← hnj]
        congr 1
        push_cast
        ring
    obtain ⟨j, hj⟩ : ∃ j : ℕ, a = -(h' : ℤ) - j := ⟨(-(h' : ℤ) - a).toNat, by omega⟩
    unfold Formalism.MainNotions.DeltaInvariantLattices.FilC
    rw [hj, hc j]

theorem φD_letter' {i : ZMod n} {x : W.DD T} (hx : (letE (O := O) i : LetA O n) • x = x) :
    (letE (O := O) (i + 1) : LetA O n) • W.φD T x = W.φD T x := by
  have hφ : W.φA (letE (O := O) i) = letE (i + 1) := by
    funext j
    simp only [LocWach.φA, letφ]
    by_cases h : j = i + 1
    · subst h
      simp [letE]
    · have h' : j - 1 ≠ i := fun h'' => h (by rw [← h'']; ring)
      simp [letE, h, h']
  rw [← hφ, ← algebraMap_smul W.EE (W.φA (letE i)) (W.φD T x)]
  have h : algebraMap (LetA O n) W.EE (W.φA (letE (O := O) i)) =
      W.φE (algebraMap (LetA O n) W.EE (letE i)) := (W.φE_ext _).symm
  rw [h, ← W.φD_smul, algebraMap_smul, hx]

end Generic

end Formalism.MainNotions.N.Ln34.MLC

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPfD
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.MQ

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries

theorem dvd_pow_of_dvr {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : O) (hp0 : p ≠ 0)
    (hpu : ¬ IsUnit p) : ∀ a : O, a ≠ 0 → ∃ (k : ℕ) (b : O), p ^ k = b * a := by
  intro a ha
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hp0 hϖ
  have hk1 : k ≠ 0 := by
    rintro rfl
    exact hpu (associated_one_iff_isUnit.1 (by simpa using hk))
  have h1 : ϖ ^ m ∣ ϖ ^ (k * m) := pow_dvd_pow ϖ (Nat.le_mul_of_pos_left m (Nat.pos_of_ne_zero hk1))
  have hdvd : a ∣ p ^ m :=
    hm.dvd.trans (h1.trans (by rw [pow_mul]; exact (hk.symm.pow_pow).dvd))
  obtain ⟨b, hb⟩ := hdvd
  exact ⟨m, b, by rw [hb, mul_comm]⟩

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem mem_DelS' {x : W.DD T} : x ∈ DelS W T ↔ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
  simp [DelS, Submodule.mem_iInf, sub_eq_zero]

theorem mem_letS' {c : ZMod n} {x : W.DD T} : x ∈ letS W T c ↔ (letE c : LetA O n) • x = x := by
  simp [letS, sub_eq_zero]

theorem γD_smulA' (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem expand_at (π' a : LetA O n) (i : ZMod n) (hπ0 : PowerSeries.constantCoeff (π' i) = 0)
    (F : PowerSeries O) (hF : a i = PowerSeries.subst (π' i) F) :
    a i = π' i * PowerSeries.subst (π' i) (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) F) +
      PowerSeries.C (PowerSeries.constantCoeff F) := by
  have hS : PowerSeries.HasSubst (π' i) := PowerSeries.HasSubst.of_constantCoeff_zero' hπ0
  conv_lhs => rw [hF, PowerSeries.eq_X_mul_shift_add_const F]
  rw [PowerSeries.subst_add hS, PowerSeries.subst_mul hS, PowerSeries.subst_X hS, PowerSeries.subst_C]
  rfl


set_option maxHeartbeats 1000000 in
theorem basis_L [IsDomain O] (π' : LetA O n) (s' : ℕ) (hs : 1 ≤ s') (w₁ : (LetA O n)ˣ)
    (hπ : π' = w₁ * (letπ : LetA O n) ^ s')
    (huniq : ∀ a, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W a → ∃! f : ZMod n → PowerSeries O, ∀ i, a i = PowerSeries.subst (π' i) (f i))
    {r : ℕ} (b : Fin r → W.DD T) (hbΔ : ∀ j, b j ∈ W.NΔ T)
    (hbu : ∀ x ∈ W.N T, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j)
    (hbe : ∀ x ∈ W.NΔ T, ∃ a : Fin r → LetA O n, (∀ j, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W (a j)) ∧ x = ∑ j, a j • b j)
    (c : ZMod n) : Nonempty (Module.Basis (Fin r) O (LcQ W T π' c)) := by
  classical
  set d : ZMod n := c - 1 with hd
  have hπd : ∀ i, π' i = (w₁ : LetA O n) i * PowerSeries.X ^ s' := fun i => π_at s' π' w₁ hπ i
  have hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0 := by
    intro i
    rw [hπd i, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero]
  have hmem : ∀ j, (letE d : LetA O n) • b j ∈ NcS W T d := by
    intro j
    obtain ⟨hN, hΔ⟩ := hbΔ j
    refine ⟨⟨(W.N T).smul_mem _ hN, (mem_DelS' W T).2 fun δ hδ => ?_⟩, (mem_letS' W T).2 ?_⟩
    · rw [γD_smulA', hΔ δ hδ, (show ∀ δ ∈ W.DelF, W.γA δ (letE d : LetA O n) = letE d from letE_mem W d) δ hδ]
    · rw [smul_smul, letE_mul_self']
  let v : Fin r → LcQ W T π' c := fun j => Submodule.Quotient.mk ⟨_, hmem j⟩
  have hli : LinearIndependent O v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h0 : (∑ j, g j • (⟨_, hmem j⟩ : ↥(NcS W T d))) ∈
        (PiNS W T π' 1).comap (NcS W T d).subtype := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum]
      simpa only [map_smul, Submodule.mkQ_apply] using hg
    rw [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_sum] at h0
    simp only [Submodule.coe_smul] at h0
    obtain ⟨⟨y, hyN, hy⟩, -⟩ := h0
    obtain ⟨a', ha'⟩ := (hbu y hyN).exists
    have hxN : π' • y ∈ W.N T := (W.N T).smul_mem _ hyN
    have hrep1 : π' • y = ∑ j, (π' * a' j) • b j := by
      rw [ha', Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_smul _ _ _
    have hrep2 : π' • y = ∑ j, (algebraMap O (LetA O n) (g j) * (letE d : LetA O n)) • b j := by
      have hy' : π' • y = ∑ j, g j • ((letE d : LetA O n) • b j) := by
        rw [← hy]
        show π' • y = ((π' ^ 1 : LetA O n) • LinearMap.id : W.DD T →ₗ[LetA O n] W.DD T) y
        rw [pow_one]
        rfl
      rw [hy']
      exact Finset.sum_congr rfl fun j _ => by rw [← smul_smul, algebraMap_smul]
    have huq := (hbu _ hxN).unique hrep1 hrep2
    have hj := congrFun (congrFun huq j) d
    simp only [Pi.mul_apply, letE, Pi.single_eq_same, mul_one] at hj
    have hcc := congrArg PowerSeries.constantCoeff hj
    rw [map_mul, hπ0 d, zero_mul] at hcc
    have : PowerSeries.constantCoeff ((algebraMap O (LetA O n) (g j)) d) = g j := by
      show PowerSeries.constantCoeff (algebraMap O (PowerSeries O) (g j)) = g j
      rw [PowerSeries.algebraMap_apply]
      simp
    rw [this] at hcc
    exact hcc.symm
  have hsp : ⊤ ≤ Submodule.span O (Set.range v) := by
    rintro q -
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨⟨hxN, hxΔ⟩, hxl⟩ := hx
    have hxΔ' := (mem_DelS' W T).1 hxΔ
    have hxl' := (mem_letS' W T).1 hxl
    obtain ⟨a, haΔ, hxa⟩ := hbe x ⟨hxN, hxΔ'⟩
    choose F hF using fun j => (huniq (a j) (haΔ j)).exists
    let κ : Fin r → O := fun j => PowerSeries.constantCoeff (F j d)
    let t : Fin r → LetA O n := fun j _ => PowerSeries.subst (π' d) (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F j d))
    have hkey : ∀ j, (letE d : LetA O n) * a j = algebraMap O (LetA O n) (κ j) * letE d + π' * ((letE d : LetA O n) * t j) := by
      intro j
      funext i
      by_cases hi : i = d
      · subst hi
        simp only [Pi.mul_apply, Pi.add_apply, letE, Pi.single_eq_same, one_mul, mul_one]
        rw [expand_at π' (a j) _ (hπ0 _) (F j _) (hF j _)]
        show _ = algebraMap O (PowerSeries O) (κ j) + _
        rw [PowerSeries.algebraMap_apply]
        simp only [Algebra.algebraMap_self, RingHom.id_apply, t, κ]
        ring
      · simp [letE, Pi.single_apply, hi]
    set y : W.DD T := ∑ j, ((letE d : LetA O n) * t j) • b j with hydef
    have hyN : y ∈ W.N T := Submodule.sum_mem _ fun j _ => (W.N T).smul_mem _ (hbΔ j).1
    have hxe : x = ∑ j, κ j • ((letE d : LetA O n) • b j) + π' • y := by
      conv_lhs => rw [← hxl', hxa, Finset.smul_sum]
      rw [hydef, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, hkey j, add_smul, smul_smul, ← algebraMap_smul (LetA O n) (κ j), smul_smul]
    have hdiff : (⟨x, ⟨⟨hxN, hxΔ⟩, hxl⟩⟩ : ↥(NcS W T d)) - ∑ j, κ j • ⟨_, hmem j⟩ ∈
        (PiNS W T π' 1).comap (NcS W T d).subtype := by
      rw [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_sub, Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      have he : x - ∑ j, κ j • ((letE d : LetA O n) • b j) = π' • y := by rw [hxe]; abel
      rw [he]
      refine ⟨⟨y, hyN, ?_⟩, ?_⟩
      · show ((π' ^ 1 : LetA O n) • LinearMap.id : W.DD T →ₗ[LetA O n] W.DD T) y = π' • y
        rw [pow_one]; rfl
      · rw [← he]
        refine sub_mem hxΔ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmem j).1.2)
    have hq : (Submodule.Quotient.mk (⟨x, ⟨⟨hxN, hxΔ⟩, hxl⟩⟩ : ↥(NcS W T d)) : LcQ W T π' c) = ∑ j, κ j • v j := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [(Submodule.Quotient.eq _).2 hdiff, ← Submodule.mkQ_apply, map_sum]
      simp only [map_smul, Submodule.mkQ_apply]
      rfl
    rw [hq]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp⟩

theorem finite_L [IsDomain O] (π' : LetA O n) (s' : ℕ) (hs : 1 ≤ s') (w₁ : (LetA O n)ˣ)
    (hπ : π' = w₁ * (letπ : LetA O n) ^ s')
    (huniq : ∀ a, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W a → ∃! f : ZMod n → PowerSeries O, ∀ i, a i = PowerSeries.subst (π' i) (f i))
    {r : ℕ} (b : Fin r → W.DD T) (hbΔ : ∀ j, b j ∈ W.NΔ T)
    (hbu : ∀ x ∈ W.N T, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j)
    (hbe : ∀ x ∈ W.NΔ T, ∃ a : Fin r → LetA O n, (∀ j, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W (a j)) ∧ x = ∑ j, a j • b j)
    (c : ZMod n) : Module.Finite O (LcQ W T π' c) := by
  exact Module.Finite.of_basis (basis_L W T π' s' hs w₁ hπ huniq b hbΔ hbu hbe c).some

end Formalism.MainNotions.N.Ln34.MQ
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.OthDisj
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalFiltration

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34
open scoped TensorProduct

section DiscreteGroups

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem oth_disj [CharZero Qp] [FiniteDimensional Qp K] (τ : K →ₐ[Qp] LL) :
    Disjoint (DdRE PD ρ τ) (⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD ρ τ') := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element Qp K
  have hint : IsIntegral Qp α := IsIntegral.of_finite Qp α
  have hadj : Algebra.adjoin Qp {α} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hα,
      IntermediateField.top_toSubalgebra]
  have hinj : Function.Injective (fun τ : K →ₐ[Qp] LL => τ α) := by
    intro τ₁ τ₂ h
    have hle := AlgHom.adjoin_le_equalizer τ₁ τ₂ (s := {α}) (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h)
    rw [hadj] at hle
    exact AlgHom.ext fun y => hle (Algebra.mem_top (x := y))
  set f : Module.End LL (V ⊗[Qp] BdR) := mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) α
  have hE : ∀ τ' : K →ₐ[Qp] LL, DdRE PD ρ τ' ≤ f.eigenspace (τ' α) := by
    intro τ' x hx
    rw [Module.End.mem_eigenspace_iff]
    have h := (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 hx).2 α
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at h
    exact h
  have hind := Module.End.eigenspaces_iSupIndep f (τ α)
  refine Disjoint.mono (hE τ) ?_ hind
  refine iSup₂_le fun τ' hτ' => ?_
  exact le_trans (hE τ') (le_iSup₂_of_le (τ' α) (fun h => hτ' (hinj h)) le_rfl)

end DiscreteGroups

section Pt

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop}

theorem dR_le (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {ζ : LL} {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ)
    [FiniteDimensional LL ↥(DdRE PD T.ρ τ)] :
    DdRE PD T.ρ τ ≤ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ' := by
  obtain ⟨hi, hhi⟩ := fr_fildR_hi PD T.ρ τ
  obtain ⟨lo, hlo⟩ := fr_fildR_lo PD T.ρ τ
  have key : ∀ d : ℕ, FildR PD T.ρ τ (hi - d) ≤
      Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ' := by
    intro d
    induction d with
    | zero =>
      rw [Nat.cast_zero, sub_zero, hhi hi le_rfl]
      exact bot_le
    | succ d ih =>
      intro w hw
      have e1 : -(-(hi - ((d + 1 : ℕ) : ℤ))) = hi - ((d + 1 : ℕ) : ℤ) := neg_neg _
      obtain ⟨x, a, -, -, hx⟩ := (hp4.2 c ζ τ hPt).2.2 (-(hi - ((d + 1 : ℕ) : ℤ))) w (by rwa [e1])
      have e2 : -(-(hi - ((d + 1 : ℕ) : ℤ))) + 1 = hi - (d : ℤ) := by push_cast; ring
      rw [e2] at hx
      have hmem1 : a • W.levN T c ζ ((letE c : LetA O n) • x) (-(hi - ((d + 1 : ℕ) : ℤ))) ∈
          Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ' :=
        Submodule.mem_sup_left (Submodule.smul_mem _ _
          (Submodule.mem_inf.1 ((hp4.2 c ζ τ hPt).2.1 x (-(hi - ((d + 1 : ℕ) : ℤ))))).1)
      have hF : Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (hi - (d : ℤ)) ≤
          Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ' := by
        unfold Formalism.MainNotions.DeltaInvariantLattices.FilC
        exact sup_le ih le_sup_right
      have := Submodule.sub_mem _ hmem1 (hF hx)
      rwa [sub_sub_cancel] at this
  have h := key (hi - lo).toNat
  rwa [hlo _ (by omega)] at h

end Pt

end Formalism.MainNotions.N.Ln34.UniversalFiltration

end
end

