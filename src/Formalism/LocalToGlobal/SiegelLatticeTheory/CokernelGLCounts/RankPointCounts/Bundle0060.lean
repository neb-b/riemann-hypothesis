module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Bundle0003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0056
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfG
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfLocalAgreement

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocEqOfLocFEq
section
noncomputable section

open scoped Classical
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LatPatch : Prop :=
  ∀ (D : D7) (Zd : LocDat D) (Λ₀ : Submodule (𝓞 D.host.E) (VS D).V), Submodule.IsFullLattice D.host.E Λ₀ →
    ∀ Mf : ∀ p : PlF D, Submodule (Zd.M p).L.O (Vp D p),
      (∀ p, ∃ Λ' : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsFullLattice D.host.E Λ' ∧ Mf p = lattice₂ D Zd.M p Λ') →
      {p | Mf p ≠ lattice₂ D Zd.M p Λ₀}.Finite →
      ∃! Λ : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsFullLattice D.host.E Λ ∧ ∀ p, lattice₂ D Zd.M p Λ = Mf p

end Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.LocalDenominators

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem localLattice_eq_iff (Zd : LocDat D) (p : PlF D) {Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (h₁ : Submodule.IsFullLattice D.host.E Λ₁) (h₂ : Submodule.IsFullLattice D.host.E Λ₂) :
    lattice₂ D Zd.M p Λ₁ = lattice₂ D Zd.M p Λ₂ ↔
      Formalism.HermitianLattices.Ext.L3.locF p.asIdeal Λ₁ = Formalism.HermitianLattices.Ext.L3.locF p.asIdeal Λ₂ := by
  haveI := p.isPrime
  letI := h₁
  letI := h₂
  have mem_iff {Λ : Submodule (𝓞 D.host.E) (VS D).V} [Submodule.IsFullLattice D.host.E Λ] (x : (VS D).V) :
      baseChange₂ D p x ∈ lattice₂ D Zd.M p Λ ↔ x ∈ Formalism.HermitianLattices.Ext.L3.locF p.asIdeal Λ :=
    baseChangeAt_mem_localLattice_iff Zd p (by infer_instance) x
  constructor
  · intro h
    ext x
    rw [← mem_iff (Λ := Λ₁), ← mem_iff (Λ := Λ₂), h]
  · intro h
    have key {A B : Submodule (𝓞 D.host.E) (VS D).V} [Submodule.IsFullLattice D.host.E B]
        (hAB : Formalism.HermitianLattices.Ext.L3.locF p.asIdeal A = Formalism.HermitianLattices.Ext.L3.locF p.asIdeal B) :
        lattice₂ D Zd.M p A ≤ lattice₂ D Zd.M p B := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, mem_iff, ← hAB]
      exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal A y).2
        ⟨1, fun h1 => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simpa using hy⟩
    exact le_antisymm (key h) (key h.symm)

section Loc

variable {V : Type} [AddCommGroup V] [Module (𝓞 D.host.E) V]

theorem loc_of_locF (p : PlF D) {P : Ideal (𝓞 D.host.E)} (hP : P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal)
    (B : Submodule (𝓞 D.host.E) V) {x : V} (hx : x ∈ Formalism.HermitianLattices.Ext.L3.locF p.asIdeal B) :
    x ∈ PI.LatLocGlob.loc P B := by
  haveI := p.isPrime
  obtain ⟨t, ht, htx⟩ := (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal B x).1 hx
  refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t, fun h => ht ?_, htx⟩
  rw [← hP]; exact h

theorem locF_of_loc (p : PlF D) (B : Submodule (𝓞 D.host.E) V) {x : V}
    (hx : ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal →
      x ∈ PI.LatLocGlob.loc P B) :
    x ∈ Formalism.HermitianLattices.Ext.L3.locF p.asIdeal B := by
  haveI := p.isPrime
  let I : Ideal (𝓞 D.host.E) :=
    { carrier := {a | a • x ∈ B}
      add_mem' := fun {a c} ha hc => by simp only [Set.mem_setOf_eq, add_smul] at *; exact B.add_mem ha hc
      zero_mem' := by simp
      smul_mem' := fun c a ha => by simp only [Set.mem_setOf_eq, smul_eq_mul, mul_smul] at *; exact B.smul_mem c ha }
  by_contra hnot
  have hle : I.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ p.asIdeal := by
    intro t ht
    by_contra htp
    exact hnot ((Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal B x).2 ⟨t, htp, ht⟩)
  obtain ⟨Q, hIQ, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal I hle
  have hQm : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := 𝓞 D.host.F) Q (by rw [hQp]; exact p.isMaximal)
  obtain ⟨s, hs, hsx⟩ := hx Q hQm hQp
  exact hs (hIQ hsx)

end Loc

section Patch

variable {V : Type} [AddCommGroup V] [Module (𝓞 D.host.E) V]

theorem loc_locF (p : PlF D) {P : Ideal (𝓞 D.host.E)} (hPp : P.IsPrime)
    (hP : P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal) (A : Submodule (𝓞 D.host.E) V) {x : V}
    (hx : x ∈ PI.LatLocGlob.loc P (Formalism.HermitianLattices.Ext.L3.locF p.asIdeal A)) : x ∈ PI.LatLocGlob.loc P A := by
  haveI := p.isPrime
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, htx⟩ := (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal A _).1 hsx
  refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t * s, fun h => (hPp.mem_or_mem h).elim (fun h1 => ht ?_) hs, ?_⟩
  · rw [← hP]; exact h1
  · rw [mul_smul]; exact htx

theorem loc_eq_of_locF_eq (p : PlF D) {P : Ideal (𝓞 D.host.E)} (hPp : P.IsPrime)
    (hP : P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal) {A B : Submodule (𝓞 D.host.E) V}
    (h : Formalism.HermitianLattices.Ext.L3.locF p.asIdeal A = Formalism.HermitianLattices.Ext.L3.locF p.asIdeal B) :
    PI.LatLocGlob.loc P A = PI.LatLocGlob.loc P B := by
  haveI := p.isPrime
  have sub : ∀ {A B : Submodule (𝓞 D.host.E) V}, Formalism.HermitianLattices.Ext.L3.locF p.asIdeal A = Formalism.HermitianLattices.Ext.L3.locF p.asIdeal B →
      PI.LatLocGlob.loc P A ⊆ PI.LatLocGlob.loc P B := by
    intro A B hAB x hx
    obtain ⟨s, hs, hsx⟩ := hx
    have h1 : s • x ∈ Formalism.HermitianLattices.Ext.L3.locF p.asIdeal B := by
      rw [← hAB]
      exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal A _).2
        ⟨1, fun h1 => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simpa using hsx⟩
    exact loc_locF p hPp hP B ⟨s, hs, h1⟩
  exact Set.Subset.antisymm (sub h) (sub h.symm)

theorem comap_ne_bot {P : Ideal (𝓞 D.host.E)} (hP : P.IsMaximal) :
    P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≠ ⊥ := by
  have hne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField D.host.E)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact Ideal.comap_ne_bot_of_integral_mem ha0 ha (Algebra.IsIntegral.isIntegral (R := 𝓞 D.host.F) a)

def plOf (P : Ideal (𝓞 D.host.E)) (hP : P.IsMaximal) : PlF D :=
  ⟨P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), Ideal.comap_isPrime _ _, comap_ne_bot hP⟩

theorem finite_over (p : PlF D) :
    {P : Ideal (𝓞 D.host.E) | P.IsMaximal ∧ P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal}.Finite := by
  have hmap : p.asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact p.ne_bot
  refine ((Ideal.finite_factors hmap).image HeightOneSpectrum.asIdeal).subset ?_
  rintro P ⟨hPm, hPp⟩
  have hne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hPm (RingOfIntegers.not_isField D.host.E)
  refine ⟨⟨P, hPm.isPrime, hne⟩, ?_, rfl⟩
  show P ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, hPp]

end Patch

theorem latPatch_holds : Formalism.L2.SG.Pf.FrameGlobalPatching.LatPatch := by
  intro D Zd Λ₀ hΛ₀ Mf hMf hfin
  choose Λ' hΛ' hMΛ' using hMf
  have hfullΛ (L : Submodule (𝓞 D.host.E) (VS D).V) (hL : Submodule.IsFullLattice D.host.E L) :
      PI.LatLocGlob.IsFullLat D.host.E L := ⟨hL.toIsLattice.fg, hL.span_eq_top⟩
  let M : Ideal (𝓞 D.host.E) → Set (VS D).V := fun P =>
    if hP : P.IsMaximal then PI.LatLocGlob.loc P (Λ' (plOf P hP)) else ∅
  have hMP : ∀ P (hP : P.IsMaximal), M P = PI.LatLocGlob.loc P (Λ' (plOf P hP)) := fun P hP => by
    simp only [M, dif_pos hP]
  have hexc : {P : Ideal (𝓞 D.host.E) | P.IsMaximal ∧ M P ≠ PI.LatLocGlob.loc P Λ₀}.Finite := by
    refine (hfin.biUnion fun p _ => finite_over p).subset ?_
    rintro P ⟨hPm, hne⟩
    refine Set.mem_biUnion (x := plOf P hPm) ?_ ⟨hPm, rfl⟩
    intro heq
    apply hne
    rw [hMP P hPm]
    have h1 : lattice₂ D Zd.M (plOf P hPm) (Λ' (plOf P hPm)) = lattice₂ D Zd.M (plOf P hPm) Λ₀ := by
      rw [← hMΛ']; by_contra h; exact h (by simpa using heq) |>.elim
    exact loc_eq_of_locF_eq (plOf P hPm) hPm.isPrime rfl ((localLattice_eq_iff Zd _ (hΛ' _) hΛ₀).1 h1)
  obtain ⟨L, ⟨hLfull, hLloc⟩, huniq⟩ := latLocGlob (𝓞 D.host.E) D.host.E (VS D).V Λ₀ (hfullΛ Λ₀ hΛ₀) M
    (fun P hP => ⟨Λ' (plOf P hP), hfullΛ _ (hΛ' _), hMP P hP⟩) hexc
  have hL : Submodule.IsFullLattice D.host.E L := by
    letI := Submodule.IsLattice.of_fg D.host.E hLfull.1
    exact ⟨hLfull.2⟩
  have hlocP : ∀ (p : PlF D) (P : Ideal (𝓞 D.host.E)), P.IsMaximal →
      P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal →
      PI.LatLocGlob.loc P L = PI.LatLocGlob.loc P (Λ' p) := by
    intro p P hPm hPp
    rw [hLloc P hPm, hMP P hPm]
    have : plOf P hPm = p := HeightOneSpectrum.ext hPp
    rw [this]
  have hlocF : ∀ p : PlF D, Formalism.HermitianLattices.Ext.L3.locF p.asIdeal L = Formalism.HermitianLattices.Ext.L3.locF p.asIdeal (Λ' p) := by
    intro p
    ext x
    constructor
    · intro hx
      refine locF_of_loc p _ fun P hPm hPp => ?_
      rw [← hlocP p P hPm hPp]
      exact loc_of_locF p hPp L hx
    · intro hx
      refine locF_of_loc p _ fun P hPm hPp => ?_
      rw [hlocP p P hPm hPp]
      exact loc_of_locF p hPp _ hx
  refine ⟨L, ⟨hL, fun p => ?_⟩, ?_⟩
  · rw [hMΛ' p]
    exact (localLattice_eq_iff Zd p hL (hΛ' p)).2 (hlocF p)
  · rintro Λ ⟨hΛ, hΛp⟩
    have h1 : ∀ p : PlF D, Formalism.HermitianLattices.Ext.L3.locF p.asIdeal Λ = Formalism.HermitianLattices.Ext.L3.locF p.asIdeal L := fun p =>
      ((localLattice_eq_iff Zd p hΛ (hΛ' p)).1 ((hΛp p).trans (hMΛ' p))).trans (hlocF p).symm
    have sub : ∀ {A B : Submodule (𝓞 D.host.E) (VS D).V}, Submodule.IsLattice D.host.E B →
        (∀ p : PlF D, Formalism.HermitianLattices.Ext.L3.locF p.asIdeal A = Formalism.HermitianLattices.Ext.L3.locF p.asIdeal B) → A ≤ B := by
      intro A B hB hAB x hx
      refine PI.UnitaryGroupMassFormula.UJClassMass.interLocF (F := D.host.F) B hB x fun v => ?_
      haveI := v.isPrime
      have h2 : x ∈ Formalism.HermitianLattices.Ext.L3.locF v.asIdeal B := by
        rw [← hAB v]
        exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF v.asIdeal A x).2
          ⟨1, fun h1 => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simpa using hx⟩
      exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF v.asIdeal B x).1 h2
    exact le_antisymm (sub hL.toIsLattice h1) (sub hΛ.toIsLattice fun p => (h1 p).symm)

end Formalism.L2.SG.Pf.LocalDenominators
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SmulCancelQ
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

theorem dec_of {U W : Submodule E V} (h : IsCompl U W) (x : V) : ∃ a ∈ U, ∃ b ∈ W, a + b = x := by
  have hx : x ∈ U ⊔ W := by
    rw [h.sup_eq_top]
    exact Submodule.mem_top
  exact Submodule.mem_sup.mp hx

theorem dec_unique {U W : Submodule E V} (h : IsCompl U W) {a a' b b' : V} (ha : a ∈ U) (ha' : a' ∈ U)
    (hb : b ∈ W) (hb' : b' ∈ W) (e : a + b = a' + b') : a = a' ∧ b = b' := by
  have h1 : a - a' ∈ U := U.sub_mem ha ha'
  have heq : a - a' = b' - b := by
    rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
  have h2 : a - a' ∈ W := by
    rw [heq]
    exact W.sub_mem hb' hb
  have h0 : a - a' = 0 := by
    have hbot := h.inf_eq_bot
    rw [Submodule.eq_bot_iff] at hbot
    exact hbot _ ⟨h1, h2⟩
  have haa : a = a' := sub_eq_zero.mp h0
  refine ⟨haa, ?_⟩
  rw [haa] at e
  exact add_left_cancel e

theorem dec_diff {U W : Submodule E V} (h : IsCompl U W) (c : E) {a a' a'' b b' b'' x x' y : V}
    (ha : a ∈ U) (ha' : a' ∈ U) (ha'' : a'' ∈ U) (hb : b ∈ W) (hb' : b' ∈ W) (hb'' : b'' ∈ W)
    (hx : a + b = x) (hx' : a' + b' = x') (hy : a'' + b'' = y) (hd : x - x' = c • y) :
    a - a' = c • a'' ∧ b - b' = c • b'' := by
  have hsum : (a - a') + (b - b') = c • a'' + c • b'' := by
    rw [← smul_add, hy, ← hd, ← hx, ← hx']
    abel
  exact dec_unique h (U.sub_mem ha ha') (U.smul_mem c ha'') (W.sub_mem hb hb') (W.smul_mem c hb'') hsum

theorem part_MMsharp (t : Term V M r) (Λ : Submodule M.L.O V) (hsd : H.IsSelfDual Λ) (hMM : MMo H t ≤ Λ)
    {a b : V} (ha : a ∈ Submodule.span E (Set.range (Sum.elim t.f t.f'))) (hb : b ∈ H.W0 t.f t.f')
    (hab : a + b ∈ Λ) : a ∈ MMsharp H t := by

  have hmm_le : ∀ i, H.MMfam t i ∈ H.Xp t.f ⊔ H.Xp t.f' := by
    intro i
    unfold Formalism.MainNotions.S.Loc.HermSp.MMfam
    rcases hs : M.split with _ | g
    · dsimp only
      rcases i with i | i
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
      · exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)
    · dsimp only
      rcases i with i | i
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
      · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩))
          (Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)))
  have hspan : Submodule.span E (Set.range (Sum.elim t.f t.f')) ≤ Submodule.span E (Set.range (H.MMfam t)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    unfold Formalism.MainNotions.S.Loc.HermSp.MMfam
    rcases hs : M.split with _ | g
    · dsimp only
      exact Submodule.subset_span ⟨i, rfl⟩
    · dsimp only
      rcases i with i | i
      · exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
      · have hq : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
        have e : t.f' i = t.f i + algebraMap F E (g.q : F) • (algebraMap F E ((g.q : F)⁻¹) • (t.f' i - t.f i)) := by
          rw [smul_smul, ← map_mul, mul_inv_cancel₀ hq, map_one, one_smul]
          abel
        show t.f' i ∈ _
        rw [e]
        exact Submodule.add_mem _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩))
  refine ⟨hspan ha, fun m hm => ?_⟩
  have hmΛ : m ∈ Λ := hMM hm
  have hab' := (hsd.2.2 (a + b)).mp hab m hmΛ
  have hmX : m ∈ H.Xp t.f ⊔ H.Xp t.f' := by
    have hle : MMo H t ≤ (H.Xp t.f ⊔ H.Xp t.f').restrictScalars M.L.O := by
      unfold Formalism.L2.SG.LsDatumA.MMo
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hmm_le i
    exact hle hm
  have hbm : H.h b m = 0 := (show ∀ x ∈ H.Xp t.f ⊔ H.Xp t.f', H.h b x = 0 from hb) m hmX
  rw [H.h_add_left, hbm, add_zero] at hab'
  exact hab'

theorem perp_left {g : Fin (r + 1) → V} {a b : V} (hb : b ∈ H.perp (H.X g)) (hab : a + b ∈ H.perp (H.X g)) :
    a ∈ H.perp (H.X g) := by
  have h1 := (H.perp (H.X g)).sub_mem hab hb
  simpa using h1

theorem smul_cancel_q (g : SplitG M.L) {v w : V}
    (h : algebraMap F E (g.q : F) • v = algebraMap F E (g.q : F) • w) : v = w := by
  have hq : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
  have hu : IsUnit (algebraMap F E (g.q : F)) := (IsUnit.mk0 _ hq).map _
  exact (hu.smul_left_cancel).mp h

end RG2

end Formalism.L2.SG.LsDatumA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfQ
section
noncomputable section

open scoped Classical

open ValuativeRel NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.Pf.StabIntSh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gS_ne : ((gS D : ℕ) : D.host.E) ≠ 0 := by
  unfold gS; push_cast
  exact mul_ne_zero (by exact_mod_cast (D.host.g_prime 0).ne_zero) (by exact_mod_cast (D.host.g_prime 1).ne_zero)

theorem qdPow_mem_iff (k : ℕ) (w : D.host.E) : w ∈ qdPow D k ↔ w / ((gS D : ℕ) : D.host.E) ∈ ddPow D k := by
  unfold qdPow qq
  rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.mem_singleton_mul]
  have h0 := gS_ne (D := D)
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [map_natCast, mul_div_cancel_left₀ _ h0]; exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    rw [map_natCast, mul_div_cancel₀ _ h0]

theorem mem_span_mul_iff {K : Type*} [CommRing K] (O : Subring K) (t : K) (ht : IsUnit t) (S : Set K) (y : K) :
    y ∈ Submodule.span O ((fun s => t * s) '' S) ↔ Ring.inverse t * y ∈ Submodule.span O S := by
  have hinv : Ring.inverse t * t = 1 := Ring.inverse_mul_cancel t ht
  have fwd : ∀ (t' : K) (T : Set K) (x : K), x ∈ Submodule.span O T →
      t' * x ∈ Submodule.span O ((fun s => t' * s) '' T) := by
    intro t' T x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
    | smul o x _ hx =>
      rw [Subring.smul_def, smul_eq_mul, mul_left_comm, ← smul_eq_mul, ← Subring.smul_def]
      exact Submodule.smul_mem _ o hx
  constructor
  · intro hy
    have := fwd (Ring.inverse t) _ y hy
    rwa [Set.image_image, show (fun s => Ring.inverse t * (t * s)) = id by
      funext s; rw [← mul_assoc, hinv, one_mul]; rfl, Set.image_id] at this
  · intro hy
    have := fwd t S _ hy
    rwa [← mul_assoc, Ring.mul_inverse_cancel t ht, one_mul] at this

variable (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ q, Agree δ M q) (p : PlF D)

theorem ιgS_mul_inv : (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * (D.s.atP p).ιE (((gS D : ℕ) : D.host.E)⁻¹) = 1 := by
  rw [← map_mul, mul_inv_cancel₀ gS_ne, map_one]

def uGS : (D.s.atP p).Epˣ :=
  ⟨(D.s.atP p).ιE ((gS D : ℕ) : D.host.E), (D.s.atP p).ιE (((gS D : ℕ) : D.host.E)⁻¹), ιgS_mul_inv p,
    by rw [mul_comm]; exact ιgS_mul_inv p⟩

theorem locMem_qd_iff (k : ℕ) (z : D.host.E) :
    LocMem D p (qdPow D k) z ↔ LocMem D p (ddPow D k) (z / ((gS D : ℕ) : D.host.E)) := by
  unfold LocMem
  set ι := (D.s.atP p).ιE
  have hu : IsUnit (ι ((gS D : ℕ) : D.host.E)) := (uGS p).isUnit
  have hset : ι '' (qdPow D k : Set D.host.E) =
      (fun s => ι ((gS D : ℕ) : D.host.E) * s) '' (ι '' (ddPow D k : Set D.host.E)) := by
    rw [Set.image_image]
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w / ((gS D : ℕ) : D.host.E), (qdPow_mem_iff k w).1 hw, ?_⟩
      show ι ((gS D : ℕ) : D.host.E) * ι (w / ((gS D : ℕ) : D.host.E)) = ι w
      rw [← map_mul, mul_div_cancel₀ _ gS_ne]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨((gS D : ℕ) : D.host.E) * y, (qdPow_mem_iff k _).2 (by rwa [mul_div_cancel_left₀ _ gS_ne]), ?_⟩
      show ι (((gS D : ℕ) : D.host.E) * y) = ι ((gS D : ℕ) : D.host.E) * ι y
      rw [map_mul]
  rw [hset, mem_span_mul_iff _ _ hu]
  have hi : Ring.inverse (ι ((gS D : ℕ) : D.host.E)) = ι (((gS D : ℕ) : D.host.E)⁻¹) := by
    rw [show ι ((gS D : ℕ) : D.host.E) = ((uGS p : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) from rfl, Ring.inverse_unit]
    rfl
  rw [hi, ← map_mul, div_eq_mul_inv, mul_comm z]


include hA in
theorem qLocG_of_data (g : Loc.SplitG (M p).L) (hs : (M p).split = some g) (k : ℕ) (hk : k ≤ D.R.rS)
    (z : D.host.E) :
    LocMem D p (qdPow D k) z ↔ ∃ o ∈ (D.s.atP p).O,
      cc δ p ^ k * (D.s.atP p).ιE z = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * o := by
  rw [locMem_qd_iff, locMem_iff δ M hA p hk]
  set ι := (D.s.atP p).ιE

  obtain ⟨sg, hsg, hq⟩ : ∃ sg, (D.s.atP p).split = some sg ∧ g.q = sg.q := by
    have h6 := (hA p).2.2.2.2.2
    cases hD : (D.s.atP p).split with
    | none => rw [hs, hD] at h6; exact h6.elim
    | some sg => rw [hs, hD] at h6; exact ⟨sg, rfl, h6.2⟩
  have hgp := Formalism.MainNotions.BridgeLemma.gpart_some p sg hsg

  have hgS : ι ((gS D : ℕ) : D.host.E) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * ι ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) := by
    rw [hq, sg.q_eq, ← Formalism.MainNotions.BridgeLemma.gpart_mul_oth p, hgp]
    simp only [Nat.cast_mul, map_mul, map_natCast]
  have huP : ι (uP p : D.host.E) * ι ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) = 1 := by
    rw [← map_mul, Formalism.MainNotions.BridgeLemma.unitAt_eq p]
    have h0 : ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) ≠ 0 := by
      exact_mod_cast Formalism.MainNotions.BridgeLemma.oth_ne_zero p
    push_cast
    rw [inv_mul_cancel₀ h0, map_one]
  have huO : ι (uP p : D.host.E) ∈ (D.s.atP p).O := LocFacts.unitPart_mem₂ p
  have hoO : ι ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) ∈ (D.s.atP p).O := by
    rw [map_natCast]; exact natCast_mem _ _
  have hz : ι z = ι (z / ((gS D : ℕ) : D.host.E)) * ι ((gS D : ℕ) : D.host.E) := by
    rw [← map_mul, div_mul_cancel₀ _ gS_ne]
  constructor
  · intro h
    refine ⟨ι ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) * (cc δ p ^ k * ι (z / ((gS D : ℕ) : D.host.E))),
      mul_mem hoO h, ?_⟩
    rw [hz, hgS]; ring
  · rintro ⟨o, ho, he⟩
    have : cc δ p ^ k * ι (z / ((gS D : ℕ) : D.host.E)) = o * ι (uP p : D.host.E) := by
      have h1 : cc δ p ^ k * ι (z / ((gS D : ℕ) : D.host.E)) * ι ((gS D : ℕ) : D.host.E) =
          o * ι (uP p : D.host.E) * ι ((gS D : ℕ) : D.host.E) := by
        rw [mul_assoc, ← hz, he, hgS]
        linear_combination (-(algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * o)) * huP
      have hu : IsUnit (ι ((gS D : ℕ) : D.host.E)) := (uGS p).isUnit
      exact hu.mul_right_cancel h1
    rw [this]; exact mul_mem ho huO

theorem qLocG : QLocG D := fun δ M hA p g hs k hk z => qLocG_of_data δ M hA p g hs k hk z

theorem locShapeG : LocShapeG D := locShapeG_of qLocG

end Formalism.L2.SG.Pf.StabIntSh
end
end

