module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0009
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.Bundle0004
public import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.Bundle0001
public import Formalism.TruncatedSeriesCounting.EtaDeterminantPolynomialIdentities
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.Bundle0001
public import Formalism.DistinguishedUnitIdeals.Bundle0001
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.CutPlace
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.LemmaC
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.Rounding
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.AprimeCuts
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.DescentEstimateDownUp
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.LinExtEqZeroOfMemExt
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.LevelsModConstIffOfDownDown

@[expose] public section

noncomputable section

open Classical

namespace Formalism.MainNotions.LocalTheoryWindows

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V'] {ρ' : Representation LL G V'}
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'} (F : LatHom L L')

abbrev clsZ (L' : Lattice (O := O) ρ') : ↥(latticeCocycles L') →ₗ[O] LatticeCohomology L' := Submodule.mkQ _

theorem mem_H1fT_iff (x : LatticeCohomology L') :
    x ∈ latticeFiniteCohomology PD L' ↔ ∃ c : ↥(latticeCocycles L'), (c : G → V') ∈ latticeFiniteCocycles PD L' ∧ clsZ L' c = x := by
  unfold latticeFiniteCohomology
  rw [Submodule.mem_map]
  rfl

theorem clsZ_eq_zero (c : ↥(latticeCocycles L')) : clsZ L' c = 0 ↔ (c : G → V') ∈ latticeCoboundaries L' := by
  unfold clsZ
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

theorem H1map_clsZ (c : ↥(latticeCocycles L)) :
    F.H1map (clsZ L c) = clsZ L' ⟨F.post c, F.post_Z1T c c.2⟩ := rfl

theorem mem_ImF_of_cls (p : ↥(latticeCocycles L')) (h : clsZ L' p ∈ (latticeFiniteCohomology PD L).map F.H1map) :
    (p : G → V') ∈ F.ImF PD := by
  obtain ⟨x, hx, hxp⟩ := h
  obtain ⟨c, hc, rfl⟩ := (mem_H1fT_iff PD x).1 hx
  rw [H1map_clsZ] at hxp
  have h0 : clsZ L' (p - ⟨F.post c, F.post_Z1T c c.2⟩) = 0 := by rw [map_sub, hxp, sub_self]
  have h1 := (clsZ_eq_zero _).1 h0
  have h2 : (p : G → V') = F.post c + ((p - ⟨F.post c, F.post_Z1T c c.2⟩ : ↥(latticeCocycles L')) : G → V') := by
    simp
  rw [h2]
  exact Submodule.add_mem_sup (Submodule.mem_map_of_mem hc) h1

theorem cls_mem_of_ImF (p : ↥(latticeCocycles L')) (h : (p : G → V') ∈ F.ImF PD) :
    clsZ L' p ∈ (latticeFiniteCohomology PD L).map F.H1map := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h
  obtain ⟨c, hc, rfl⟩ := ha
  have hcZ : c ∈ latticeCocycles L := hc.1
  refine ⟨clsZ L ⟨c, hcZ⟩, (mem_H1fT_iff PD _).2 ⟨⟨c, hcZ⟩, hc, rfl⟩, ?_⟩
  rw [H1map_clsZ]
  have h0 : clsZ L' (p - ⟨F.post c, F.post_Z1T c hcZ⟩) = 0 := by
    rw [clsZ_eq_zero]
    have : ((p - ⟨F.post c, F.post_Z1T c hcZ⟩ : ↥(latticeCocycles L')) : G → V') = b := by
      simp [← hab]
    rw [this]; exact hb
  rw [map_sub, sub_eq_zero] at h0
  exact h0.symm

def liftZ (x : LatticeCohomology L') : ↥(latticeCocycles L') :=
  if h : x ∈ latticeFiniteCohomology PD L' then ((mem_H1fT_iff PD x).1 h).choose else 0

theorem liftZ_mem {x : LatticeCohomology L'} (h : x ∈ latticeFiniteCohomology PD L') : ((liftZ PD x : ↥(latticeCocycles L')) : G → V') ∈ latticeFiniteCocycles PD L' := by
  unfold liftZ; rw [dite_eq_left h]; exact ((mem_H1fT_iff PD x).1 h).choose_spec.1

theorem liftZ_cls {x : LatticeCohomology L'} (h : x ∈ latticeFiniteCohomology PD L') : clsZ L' (liftZ PD x) = x := by
  unfold liftZ; rw [dite_eq_left h]; exact ((mem_H1fT_iff PD x).1 h).choose_spec.2

def liftS (A : Finset (LatticeCohomology L')) : Finset (G → V') := A.image fun x => ((liftZ PD x : ↥(latticeCocycles L')) : G → V')

theorem exists_lift_span (A : Finset (LatticeCohomology L')) (hA : (↑A : Set (LatticeCohomology L')) ⊆ latticeFiniteCohomology PD L') (a : LatticeCohomology L')
    (ha : a ∈ Submodule.span O (↑A : Set (LatticeCohomology L'))) :
    ∃ y : ↥(latticeCocycles L'), (y : G → V') ∈ Submodule.span O (↑(liftS PD A) : Set (G → V')) ∧ clsZ L' y = a := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    refine ⟨liftZ PD x, Submodule.subset_span ?_, liftZ_cls PD (hA hx)⟩
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ hx)
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    exact ⟨u + w, Submodule.add_mem _ hu hw, map_add _ _ _⟩
  | smul c x _ hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨c • u, Submodule.smul_mem _ c hu, map_smul _ _ _⟩

theorem mem_span_sup_ImF (A : Finset (LatticeCohomology L')) (hA : (↑A : Set (LatticeCohomology L')) ⊆ latticeFiniteCohomology PD L')
    (p : ↥(latticeCocycles L'))
    (hp : clsZ L' p ∈ Submodule.span O (↑A : Set (LatticeCohomology L')) ⊔ (latticeFiniteCohomology PD L).map F.H1map) :
    (p : G → V') ∈ Submodule.span O (↑(liftS PD A) : Set (G → V')) ⊔ F.ImF PD := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hp
  obtain ⟨y, hy, rfl⟩ := exists_lift_span PD A hA a ha
  have h1 : clsZ L' (p - y) ∈ (latticeFiniteCohomology PD L).map F.H1map := by
    rw [map_sub, ← hab, add_sub_cancel_left]; exact hb
  have h2 := mem_ImF_of_cls PD F _ h1
  have h3 : (p : G → V') = (y : G → V') + ((p - y : ↥(latticeCocycles L')) : G → V') := by simp
  rw [h3]
  exact Submodule.add_mem_sup hy h2

theorem col_le_of_span (hI : F.ImF PD ≤ latticeFiniteCocycles PD L') (gens cls : Finset (LatticeCohomology L')) (g e e' : ℕ)
    (hgens : Submodule.span O (↑gens : Set (LatticeCohomology L')) = latticeFiniteCohomology PD L') (hg : gens.card ≤ g)
    (hcls : (↑cls : Set (LatticeCohomology L')) ⊆ latticeFiniteCohomology PD L')
    (h1 : ∀ x ∈ latticeFiniteCohomology PD L', (((PD.p : ℕ) : O) ^ e) • x ∈
      Submodule.span O (↑cls : Set (LatticeCohomology L')) ⊔ (latticeFiniteCohomology PD L).map F.H1map)
    (h2 : ∀ x ∈ cls, (((PD.p : ℕ) : O) ^ e') • x ∈ (latticeFiniteCohomology PD L).map F.H1map) :
    F.col PD ≤ ((g * e + cls.card * e' : ℕ) : ℕ∞) * lenOl PD (O := O) := by
  have hgs : (↑gens : Set (LatticeCohomology L')) ⊆ latticeFiniteCohomology PD L' := by
    rw [← hgens]; exact Submodule.subset_span
  have hsub : ∀ (A : Finset (LatticeCohomology L')), (↑A : Set (LatticeCohomology L')) ⊆ latticeFiniteCohomology PD L' →
      (↑(liftS PD A) : Set (G → V')) ⊆ latticeFiniteCocycles PD L' := by
    intro A hA p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hp)
    exact liftZ_mem PD (hA hx)
  have hnat : ∀ (k : ℕ) (p : G → V'), (PD.p ^ k : ℕ) • p = (((PD.p : ℕ) : O) ^ k) • p := by
    intro k p
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  refine Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds.length_quotient_le_of_two_step O (G → V') PD.p g cls.card e e' (latticeFiniteCocycles PD L') (F.ImF PD)
    (liftS PD gens) (liftS PD cls) hI (le_trans Finset.card_image_le hg) Finset.card_image_le
    (hsub cls hcls) ?_ ?_ ?_
  · apply le_antisymm
    · exact sup_le (Submodule.span_le.2 (hsub gens hgs)) hI
    · intro p hp
      have hpZ : p ∈ latticeCocycles L' := hp.1
      refine mem_span_sup_ImF PD F gens hgs ⟨p, hpZ⟩ (Submodule.mem_sup_left ?_)
      rw [hgens]
      exact (mem_H1fT_iff PD _).2 ⟨⟨p, hpZ⟩, hp, rfl⟩
  · intro p hp
    have hpZ : p ∈ latticeCocycles L' := hp.1
    rw [hnat]
    refine mem_span_sup_ImF PD F cls hcls ((((PD.p : ℕ) : O) ^ e) • (⟨p, hpZ⟩ : ↥(latticeCocycles L'))) ?_
    rw [map_smul]
    exact h1 _ ((mem_H1fT_iff PD _).2 ⟨⟨p, hpZ⟩, hp, rfl⟩)
  · intro p hp
    rw [hnat]
    have hle : Submodule.span O (↑(liftS PD cls) : Set (G → V')) ≤
        (F.ImF PD).comap ((((PD.p : ℕ) : O) ^ e') • (LinearMap.id : (G → V') →ₗ[O] (G → V'))) := by
      rw [Submodule.span_le]
      intro q hq
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hq)
      have := mem_ImF_of_cls PD F ((((PD.p : ℕ) : O) ^ e') • liftZ PD x) (by
        rw [map_smul, liftZ_cls PD (hcls hx)]; exact h2 x hx)
      exact this
    exact hle hp

theorem cls_of_LiftF {e' : ℕ} (hL : F.LiftF PD e') (x : LatticeCohomology L') (hx : x ∈ latticeFiniteCohomology PD L') :
    (((PD.p : ℕ) : O) ^ e') • x ∈ (latticeFiniteCohomology PD L).map F.H1map := by
  obtain ⟨c, hc, rfl⟩ := (mem_H1fT_iff PD x).1 hx
  rw [← map_smul]
  exact cls_mem_of_ImF PD F _ (hL c hc)

end Gen

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem ImF_le (PD : PeriodData G Qp K₀ K B BdR) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) : F.ImF PD ≤ latticeFiniteCocycles PD T₂.L := by
  have : IsTopologicalAddGroup T₁.V := IsModuleTopology.topologicalAddGroup LL T₁.V
  have : IsTopologicalAddGroup T₂.V := IsModuleTopology.topologicalAddGroup LL T₂.V
  exact (finiteCocycles_properties.2.2.2 G Qp K₀ K B BdR PD LL O T₁.V T₂.V T₁.ρ T₂.ρ T₁.L T₂.L F T₂.cont).1

theorem colLeR_of_span (PD : PeriodData G Qp K₀ K B BdR) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (gens cls : Finset (LatticeCohomology T₂.L)) (g e e' k : ℕ)
    (hk : lenOl PD (O := O) = (k : ℕ∞))
    (hgens : Submodule.span O (↑gens : Set (LatticeCohomology T₂.L)) = latticeFiniteCohomology PD T₂.L) (hg : gens.card ≤ g)
    (hcls : (↑cls : Set (LatticeCohomology T₂.L)) ⊆ latticeFiniteCohomology PD T₂.L)
    (h1 : ∀ x ∈ latticeFiniteCohomology PD T₂.L, (((PD.p : ℕ) : O) ^ e) • x ∈
      Submodule.span O (↑cls : Set (LatticeCohomology T₂.L)) ⊔ (latticeFiniteCohomology PD T₁.L).map F.H1map)
    (h2 : ∀ x ∈ cls, (((PD.p : ℕ) : O) ^ e') • x ∈ (latticeFiniteCohomology PD T₁.L).map F.H1map) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.ColLeR PD F ((g : ℝ) * e + cls.card * e') := by
  have h := col_le_of_span PD F (ImF_le PD F) gens cls g e e' hgens hg hcls h1 h2
  rw [hk] at h
  have h' : F.col PD ≤ (((g * e + cls.card * e') * k : ℕ) : ℕ∞) := by
    rw [Nat.cast_mul]; exact h
  obtain ⟨mm, hmm⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top _) h')
  refine ⟨mm, k, hmm.symm, hk, ?_⟩
  rw [← hmm] at h'
  have h3 : mm ≤ (g * e + cls.card * e') * k := by exact_mod_cast h'
  have h4 : (mm : ℝ) ≤ (((g * e + cls.card * e') * k : ℕ) : ℝ) := by exact_mod_cast h3
  push_cast at h4
  exact h4

theorem colLeR_of_liftF (PD : PeriodData G Qp K₀ K B BdR) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (gens : Finset (LatticeCohomology T₂.L)) (g e k : ℕ)
    (hk : lenOl PD (O := O) = (k : ℕ∞))
    (hgens : Submodule.span O (↑gens : Set (LatticeCohomology T₂.L)) = latticeFiniteCohomology PD T₂.L) (hg : gens.card ≤ g)
    (hL : F.LiftF PD e) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.ColLeR PD F ((g : ℝ) * e) := by
  have h := colLeR_of_span PD F gens ∅ g e 0 k hk hgens hg (by simp)
    (fun x hx => Submodule.mem_sup_right (cls_of_LiftF PD F hL x hx)) (by simp)
  simpa using h

end Core

section Fin

variable {l : ℕ} [Fact l.Prime]

theorem OL_finite (LL : FinExt l) : Module.Finite ℤ_[l] ↥(OL LL) := by
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  exact IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)

theorem OL_quot_finite (LL : FinExt l) :
    Finite (↥(OL LL) ⧸ Ideal.span {((l : ℕ) : ↥(OL LL))}) := by
  have := OL_finite LL
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℤ_[l] ↥(OL LL)
  let g : (Fin n → Fin l) → (↥(OL LL) ⧸ Ideal.span {((l : ℕ) : ↥(OL LL))}) :=
    fun r => Ideal.Quotient.mk _ (f fun i => ((r i : ℕ) : ℤ_[l]))
  apply Finite.of_surjective g
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a, rfl⟩ := hf y
  have hrep : ∀ i, ∃ b : ℤ_[l], a i = ((a i).zmodRepr : ℤ_[l]) + (l : ℤ_[l]) * b := by
    intro i
    have h := PadicInt.sub_zmodRepr_mem (a i)
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
    obtain ⟨b, hb⟩ := h
    exact ⟨b, by rw [← hb]; ring⟩
  choose b hb using hrep
  refine ⟨fun i => ⟨(a i).zmodRepr, PadicInt.zmodRepr_lt_p _⟩, ?_⟩
  have ha : a = (fun i => (((a i).zmodRepr : ℕ) : ℤ_[l])) + (l : ℕ) • b := by
    funext i
    rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul]
    exact hb i
  have hfa : f a = f (fun i => (((a i).zmodRepr : ℕ) : ℤ_[l])) + ((l : ℕ) : ↥(OL LL)) * f b := by
    conv_lhs => rw [ha]
    rw [map_add (f := _), map_nsmul, nsmul_eq_mul]
  show Ideal.Quotient.mk _ (f fun i => (((a i).zmodRepr : ℕ) : ℤ_[l])) = Ideal.Quotient.mk _ (f a)
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  refine ⟨- f b, ?_⟩
  rw [hfa]
  ring

theorem len_finite_of_finite (R : Type) [CommRing R] (I : Ideal R) [Finite (R ⧸ I)] :
    ∃ k : ℕ, Module.length R (R ⧸ I) = (k : ℕ∞) := by
  have h1 : IsFiniteLength R (R ⧸ I) :=
    isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (Module.length_ne_top_iff.2 h1)
  exact ⟨k, hk.symm⟩

theorem lenOl_finite (P : LocPrime l) (K LL : FinExt l) :
    ∃ k : ℕ, lenOl (P.PD K) (O := ↥(OL LL)) = (k : ℕ∞) := by
  unfold lenOl
  rw [P.PD_p K]
  have := OL_quot_finite LL
  exact len_finite_of_finite _ _

end Fin

section Words

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

end Words

end Formalism.MainNotions.LocalTheoryWindows
