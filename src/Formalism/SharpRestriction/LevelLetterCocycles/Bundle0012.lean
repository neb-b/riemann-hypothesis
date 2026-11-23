module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.AdmBoundsBOfAdm
section
noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def HypB (PD : PeriodData G Qp K₀ K B BdR) [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n)
    (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b w S η m : ℕ) (up : ZMod n → Bool)
    (size Mi hi : ZMod n → ℕ) : Prop :=
  11 ≤ PD.p ∧ TruncatedSeriesCountingBounds.HidaSetting PD W T₁ T₂ F b w S η m up size Mi hi ∧ 20 * w ≤ b ∧ 20 * η ≤ b ∧
    20 * S ≤ b ∧ ∃ i, ¬ TruncatedSeriesCountingBounds.Thick b η size i

def Alt (b η : ℕ) (up : ZMod n → Bool) (size : ZMod n → ℕ) : Prop :=
  ∀ i, up (i + 1) ≠ up i ∧
    ¬ (TruncatedSeriesCountingBounds.Thick b η size i ∧ TruncatedSeriesCountingBounds.Thick b η size (i + 1) ∧ TruncatedSeriesCountingBounds.Thick b η size (i + 2))

def One (b η R : ℕ) (up : ZMod n → Bool) (size : ZMod n → ℕ) : Prop :=
  (∀ i, up i = up 0) ∧ ∀ i, ¬ ∀ t : ℕ, t < R → TruncatedSeriesCountingBounds.Thick b η size (i + t)

def Sg (l b w S η : ℕ) (size : ZMod n → ℕ) : ℝ :=
  (TruncatedSeriesCountingBounds.hB b w S η size : ℝ) / (l : ℝ) ^ 2 + ((w : ℝ) + S + η) / l +
    Real.logb l (2 * (TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) + 1

def bandI (l b w S η : ℕ) (size : ZMod n → ℕ) (Cb : ℝ) : ℝ :=
  if TruncatedSeriesCountingBounds.Band l b S η size (Real.logb l (2 * (TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) Cb then 1 else 0

def arcOf [NeZero n] (b w S η : ℕ) (up : ZMod n → Bool) (size : ZMod n → ℕ) : ArcLiftingSetup.ArcP n where
  G₀ := w + S
  S := S
  η := η
  h := TruncatedSeriesCountingBounds.hB b w S η size
  j := 1
  ty := fun i => if up i then .up (size i) else .down (size i)
  cuts := Finset.univ.filter fun c => ¬ TruncatedSeriesCountingBounds.Thick b η size (c + 1)
  len := fun c => sInf {d : ℕ | 1 ≤ d ∧
    ¬ TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)}

def kapC (l : ℕ) (A : ArcLiftingSetup.ArcP n) (c : ZMod n) : ℕ :=
  A.len c + ∑ i ∈ (A.JS c).erase 0, (A.len c + 1 + padicValInt l i)

def ExpIn (PD : PeriodData G Qp K₀ K B BdR) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (Z : Finset (G → T₂.V)) (e : ℕ) : Prop :=
  ∀ c ∈ latticeFiniteCocycles PD T₂.L, ((PD.p : O) ^ e) • c ∈ F.ImF PD ⊔ Submodule.span O (Z : Set (G → T₂.V))

def ExtYCore (PD : PeriodData G Qp K₀ K B BdR) (W : LocWach PD LL O v n) : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ cc ∈ latticeFiniteCocycles PD T.L,
    ∃ (Y : LocLat G Qp LL O) (ι : LatHom T.L Y.L) (π : LatHom Y.L W.one.L),
      IsCrys PD Y.ρ ∧ Formalism.MainNotions.LiftingTheory.IsExtOf W ι π cc

end Core

structure AdmBoundsB (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CR CA CB CK : ℝ) : Prop where
  p2 : Formalism.MainNotions.DeltaInvariantLattices.P2 D HW F
  p3 : Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm
  p4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm
  p5 : Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F
  p9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F
  a2 : ArcLiftingSetup.adm2 D HW F CR CA CB CK
  a5 : ArcLiftingSetup.adm5 D HW F
  sP : ArcLiftingSetup.SaturationFrobeniusPullback D HW F
  kLev : ArcLiftingSetup.KillerLevL D.loc D.locA HW F
  kMod : ArcLiftingSetup.KillerModL D.loc D.locA HW F
  a9 : ArcLiftingSetup.adm9 D
  a10 : ArcLiftingSetup.adm10 D
  a11 : ArcLiftingSetup.adm11 D HW F
  a12 : ArcLiftingSetup.adm12 D HW F Cm
  a13 : ArcLiftingSetup.adm13 D HW F Cm
  a14 : ArcLiftingSetup.adm14 D HW F Cm
  a15 : ArcLiftingSetup.adm15 D

theorem admBoundsB_of_adm {D : D7} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW} {Cm : CmpOf D.loc D.locA HW F}
    {CR CA CB CK Ckap : ℝ} (h : ArcLiftingSetup.admitted D HW F Cm CR CA CB CK Ckap) : AdmBoundsB D HW F Cm CR CA CB CK :=
  ⟨fun l _ K s LL g => (h.1.1 l K s LL g).2.1, fun l _ K s LL g => (h.1.1 l K s LL g).2.2.1,
    fun l _ K s LL g => (h.1.1 l K s LL g).2.2.2.1, fun l _ K s LL g => (h.1.1 l K s LL g).2.2.2.2.1,
    fun l _ K s LL g => (h.1.1 l K s LL g).2.2.2.2.2.2.2.2.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1.2.2.1, h.2.2.2.2.1.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1⟩

end Formalism.MainNotions.N.Ln17
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.AlgebraMapUnitZpow
section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.KV

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem algebraMap_unit_zpow (u : Oˣ) (z : ℤ) :
    algebraMap O LL ((u ^ z : Oˣ) : O) = (algebraMap O LL (u : O)) ^ z := by
  change ((Units.map (algebraMap O LL).toMonoidHom (u ^ z) : LLˣ) : LL) = _
  rw [map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

theorem v_prod {ι : Type*} (s : Finset ι) (f : ι → LL) :
    v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]

theorem padicValInt_mul_pow {p : ℕ} (hp : p.Prime) {i : ℤ} (hi : i ≠ 0) (ell : ℕ) :
    padicValInt p (i * (p : ℤ) ^ ell) = padicValInt p i + ell := by
  have := Fact.mk hp
  simp only [padicValInt, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  rw [Nat.multiplicity_mul (Int.natAbs_ne_zero.2 hi) (pow_ne_zero _ hp.ne_zero),
    Nat.multiplicity_prime_pow]

theorem eval_PPO (W : LocWach PD LL O v n) (ell : ℕ) (JS : Finset ℤ) :
    algebraMap O LL ((PPO W ell JS).eval 1) =
      (∏ i ∈ JS.erase 0, (1 - (algebraMap O LL (W.χΓ W.gam : O)) ^ (i * (PD.p : ℤ) ^ ell))) *
        (PD.p : LL) ^ ell := by
  simp only [PPO, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_finsetSum, one_pow, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one, map_mul, map_prod, map_sub, map_one, map_natCast,
    algebraMap_unit_zpow]
  push_cast
  ring

theorem val_PP_one (W : LocWach PD LL O v n) (hs : W.s = 1) (hp : PD.p ≠ 2) (ell : ℕ)
    (JS : Finset ℤ) :
    v (algebraMap O LL ((PPO W ell JS).eval 1)) =
      ((ell + ∑ i ∈ JS.erase 0, (ell + 1 + padicValInt PD.p i) : ℕ) : WithTop ℚ) := by
  have hy : 1 ≤ v (algebraMap O LL (W.χΓ W.gam : O) - 1) := by
    rw [W.gam_gen, hs, Nat.cast_one]
  have hfac : ∀ i ∈ JS.erase 0,
      v (1 - (algebraMap O LL (W.χΓ W.gam : O)) ^ (i * (PD.p : ℤ) ^ ell)) =
        ((ell + 1 + padicValInt PD.p i : ℕ) : WithTop ℚ) := by
    intro i hi
    have hi0 : i ≠ 0 := (Finset.mem_erase.1 hi).1
    have hm : i * (PD.p : ℤ) ^ ell ≠ 0 := mul_ne_zero hi0 (pow_ne_zero _ (by exact_mod_cast PD.hp.ne_zero))
    rw [AddValuation.map_sub_swap, LTE.val_zpow_sub_one v PD.hp hp W.v_l hy hm, W.gam_gen, hs,
      padicValInt_mul_pow PD.hp hi0]
    push_cast
    abel
  rw [eval_PPO, AddValuation.map_mul, v_prod, Finset.sum_congr rfl hfac, AddValuation.map_pow, W.v_l,
    nsmul_one, Nat.cast_add, Nat.cast_sum, add_comm]

end Formalism.MainNotions.UnusedSlot80.KV
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ArcParametersShiftInvariant
section
noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

section Comb

variable {n : ℕ} (a : ZMod n)

def sh {α : Type*} (f : ZMod n → α) : ZMod n → α := fun i => f (i - a)

def shC (cuts : Finset (ZMod n)) : Finset (ZMod n) := cuts.image (· + a)

theorem mem_shC {cuts : Finset (ZMod n)} {c : ZMod n} : c ∈ shC a cuts ↔ c - a ∈ cuts := by
  simp only [shC, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨c - a, h, sub_add_cancel c a⟩

theorem ellMax_sh (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ) :
    ellMax (shC a cuts) (sh a arcLen) = ellMax cuts arcLen := by
  unfold ellMax shC
  rw [Finset.sup_image]
  congr 1
  funext x
  simp [sh]

theorem cutsOK_sh {j : ℕ} {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (h : CutsOK n j ty cuts arcLen) : CutsOK n j (sh a ty) (shC a cuts) (sh a arcLen) := by
  obtain ⟨hne, hj, h3, h4, h5⟩ := h
  refine ⟨hne.image _, hj, fun c hc ↦ ?_, fun c hc ↦ h4 _ ((mem_shC a).1 hc), fun c hc k hk1 hkj ↦ ?_⟩
  · obtain ⟨e1, e2, e3, e4⟩ := h3 _ ((mem_shC a).1 hc)
    refine ⟨e1, e2, (mem_shC a).2 ?_, fun d hd1 hd2 hmem ↦ e4 d hd1 hd2 ?_⟩
    · rw [sub_right_comm]
      exact e3
    · have hm := (mem_shC a).1 hmem
      rwa [sub_right_comm] at hm
  · show ty (c + (k : ZMod n) - a) = LT.thin
    rw [show c + (k : ZMod n) - a = c - a + k by ring]
    exact h5 _ ((mem_shC a).1 hc) k hk1 hkj

theorem ro_sh (ty : ZMod n → LT) (arcLen : ZMod n → ℕ) (c : ZMod n) :
    ro (sh a ty) (sh a arcLen) c = ro ty arcLen (c - a) := by
  rw [Formalism.MainNotions.LocalTheoryWindows.ro, Formalism.MainNotions.LocalTheoryWindows.ro, Formalism.MainNotions.LocalTheoryWindows.thickLv, Formalism.MainNotions.LocalTheoryWindows.thickLv]
  congr 1
  apply Finset.filter_congr
  intro s _
  simp only [sh]
  rw [show c - (s : ZMod n) - a = c - a - s by ring]

theorem thickLe2_sh {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (h : ThickLe2 ty cuts arcLen) : ThickLe2 (sh a ty) (shC a cuts) (sh a arcLen) := by
  intro c hc
  rw [ro_sh]
  exact h _ ((mem_shC a).1 hc)

theorem wordOK_sh {l a₀ : ℕ} {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (h : WordOK l a₀ ty cuts arcLen) : WordOK l a₀ (sh a ty) (shC a cuts) (sh a arcLen) := by
  intro c hc s₀ s₁ hs hs1 b₀ b₁
  have h' := h _ ((mem_shC a).1 hc) s₀ s₁ hs hs1 b₀ b₁
  simp only [sh]
  rw [sub_right_comm c (s₁ : ZMod n) a, sub_right_comm c (s₀ : ZMod n) a]
  exact h'

theorem sizesOK_sh {g S h : ℕ} {ty : ZMod n → LT} (H : SizesOK g S h ty) :
    SizesOK g S h (sh a ty) := fun i ↦ H (i - a)

variable [NeZero n]

theorem Hmax_sh (H : ZMod n → ℕ) : Hmax n (sh a H) = Hmax n H := by
  unfold Hmax
  apply le_antisymm
  · exact Finset.sup_le fun i _ ↦ Finset.le_sup (f := H) (Finset.mem_univ (i - a))
  · refine Finset.sup_le fun i _ ↦ ?_
    have hle := Finset.le_sup (f := sh a H) (Finset.mem_univ (i + a))
    simpa [sh] using hle

theorem sBd_sh (l : ℕ) (H : ZMod n → ℕ) (i : ZMod n) : sBd l n (sh a H) i = sBd l n H (i - a) := by
  unfold sBd
  rw [Hmax_sh]
  congr 1
  funext k
  simp only [sh]
  rw [show i + ((k + 1 : ℕ) : ZMod n) - a = i - a + ((k + 1 : ℕ) : ZMod n) by ring]

theorem rF_sh (l : ℕ) (H : ZMod n → ℕ) (i : ZMod n) : rF l n (sh a H) i = rF l n H (i - a) := by
  unfold rF
  rw [sBd_sh, Hmax_sh]

theorem rrPar_sh (l : ℕ) (H₁ H₂ : ZMod n → ℕ) (cuts : Finset (ZMod n)) :
    rrPar l n (sh a H₁) (sh a H₂) (shC a cuts) = rrPar l n H₁ H₂ cuts := by
  unfold rrPar shC
  rw [Finset.sup_image]
  congr 1
  funext c
  simp [rF_sh]

theorem arc_parameters_shift_invariant (l j g h : ℕ) (H₁ H₂ : ZMod n → ℕ) (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ) :
    initialExponentBound l n j g h (sh a H₁) (sh a H₂) (shC a cuts) (sh a arcLen) =
      initialExponentBound l n j g h H₁ H₂ cuts arcLen := by
  unfold initialExponentBound
  rw [rrPar_sh, ellMax_sh]

theorem ePar_sh (l j g h : ℕ) (H₁ H₂ : ZMod n → ℕ) (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ) :
    ePar l n j g h (sh a H₁) (sh a H₂) (shC a cuts) (sh a arcLen) =
      ePar l n j g h H₁ H₂ cuts arcLen := by
  unfold ePar
  rw [rrPar_sh, arc_parameters_shift_invariant, ellMax_sh]

end Comb

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

theorem jumpsAtE_sh (T : LocLat G Qp LL O) (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (a i : ZMod n) (S : Set ℤ)
    (h : JumpsAtE PD T (fun k => emb (k + a)) (i - a) S) : JumpsAtE PD T emb i S := by
  intro τ hτ
  exact h τ (by simp only [sub_add_cancel]; exact hτ)

theorem exists_rot {emb emb' : ZMod n → (K₀ →ₐ[Qp] LL)} (hb : Function.Surjective emb')
    (h : ∀ i, (emb (i + 1)).comp PD.σ = emb i) (h' : ∀ i, (emb' (i + 1)).comp PD.σ = emb' i) :
    ∃ a : ZMod n, emb = fun i => emb' (i + a) := by
  obtain ⟨a, ha⟩ := hb (emb 0)
  refine ⟨a, ?_⟩
  have key : ∀ k : ℕ, emb (-(k : ZMod n)) = emb' (-(k : ZMod n) + a) := by
    intro k
    induction k with
    | zero => simp [ha]
    | succ k ih =>
      have e1 := h (-((k + 1 : ℕ) : ZMod n))
      have e2 := h' (-((k + 1 : ℕ) : ZMod n) + a)
      rw [show -((k + 1 : ℕ) : ZMod n) + 1 = -(k : ZMod n) by push_cast; ring, ih] at e1
      rw [show -((k + 1 : ℕ) : ZMod n) + a + 1 = -(k : ZMod n) + a by push_cast; ring] at e2
      rw [← e1, e2]
  funext i
  have hi := key ((-i).val)
  rwa [ZMod.natCast_zmod_val, neg_neg] at hi

variable [Fintype (K →ₐ[Qp] LL)]

theorem thmELiftAt_rot (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (a : ZMod n)
    (H : ThmELiftAt PD (O := O) n emb v) : ThmELiftAt PD (O := O) n (fun i => emb (i + a)) v := by
  intro hLet hp T₁ T₂ F hGood hC1 hC2 hOnto j Gp S η h ty cuts arcLen Mb₁ hb₁ Mb₂ hb₂ hKind hJ hg
    hSizes hCuts hThick hJ1 hJ2 hWord
  have hLet' : Letters PD LL v emb := by
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hLet
    refine ⟨e1, e2, e3, ?_, fun i ↦ ?_, e6⟩
    · have he : emb = (fun i ↦ emb (i + a)) ∘ (fun i ↦ i - a) := funext fun i ↦ by simp
      rw [he]
      exact e4.comp (Equiv.subRight a).bijective
    · have e := e5 (i - a)
      simp only [sub_add_cancel, show i - a + 1 + a = i + 1 by ring] at e
      exact e
  have hW : WordOK PD.p (initialExponentBound PD.p n j (gPar Gp S η) h (sh a Mb₁ + sh a hb₁) (sh a Mb₂ + sh a hb₂)
      (shC a cuts) (sh a arcLen)) (sh a ty) (shC a cuts) (sh a arcLen) := by
    rw [show sh a Mb₁ + sh a hb₁ = sh a (Mb₁ + hb₁) from rfl,
      show sh a Mb₂ + sh a hb₂ = sh a (Mb₂ + hb₂) from rfl, arc_parameters_shift_invariant]
    exact wordOK_sh a hWord
  have hL := H hLet' hp T₁ T₂ F hGood hC1 hC2 hOnto j Gp S η h (sh a ty) (shC a cuts) (sh a arcLen)
    (sh a Mb₁) (sh a hb₁) (sh a Mb₂) (sh a hb₂) (fun i ↦ jumpsAtE_sh T₁ emb a i _ (hKind (i - a))) hJ hg
    (sizesOK_sh a hSizes) (cutsOK_sh a hCuts) (thickLe2_sh a hThick)
    (fun i ↦ jumpsAtE_sh T₁ emb a i _ (hJ1 (i - a))) (fun i ↦ jumpsAtE_sh T₂ emb a i _ (hJ2 (i - a))) hW
  rwa [show sh a Mb₁ + sh a hb₁ = sh a (Mb₁ + hb₁) from rfl,
    show sh a Mb₂ + sh a hb₂ = sh a (Mb₂ + hb₂) from rfl, ePar_sh] at hL

end Formalism.MainNotions.WachCoordinates.Br
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.CongruenceSingleEndomorphism
section
open Module

noncomputable section

namespace Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Module IsDiscreteValuationRing

section Hecke

open Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br Formalism.NG Formalism.NG.QuotientPowerLengths

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type} [Fintype X]
  {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M]
  (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M)

theorem heckeEig_indep (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) :
    iSupIndep (heckeEig T act) := by
  let F : T → Module.End (FractionRing O) (TensorProduct O (FractionRing O) M) :=
    fun f => actK T act f
  have hc : ∀ f g, Commute (F f) (F g) := fun f g => by
    show actK T act f * actK T act g = actK T act g * actK T act f
    rw [← map_mul, mul_comm, map_mul]
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo F
    (fun f g φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc g f) φ)
  let χ : X → (T → FractionRing O) := fun x f => algebraMap O (FractionRing O) ((f : X → O) x)
  have hχ : Function.Injective χ := by
    intro x y hxy
    by_contra hne
    obtain ⟨f, hf, hfx⟩ := hsep x y hne
    exact hfx (IsFractionRing.injective O (FractionRing O) (congrFun hxy ⟨f, hf⟩))
  refine (h.comp hχ).mono fun x => iInf_mono fun f => ?_
  exact ((F f).genEigenspace _).monotone le_top

end Hecke

section Record

open Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br

variable {D : D7}

theorem eig_isCompl (i : D.nd.Loc) (S : Finset (D.nd.X i)) :
    IsCompl (D.nd.eigSum i ↑S) (D.nd.eigSum i (↑S)ᶜ) := by
  refine ⟨(heckeEig_indep (D.nd.T i) (D.nd.act i) (D.nd.T_sep i)).disjoint_biSup_biSup
    disjoint_compl_right, codisjoint_iff.2 ?_⟩
  rw [eq_top_iff, ← EigSpan_holds D.nd i]
  refine iSup_le fun x => ?_
  by_cases hx : x ∈ (S : Set (D.nd.X i))
  · exact le_sup_of_le_left (le_biSup (heckeEig (D.nd.T i) (D.nd.act i)) hx)
  · exact le_sup_of_le_right
      (le_biSup (heckeEig (D.nd.T i) (D.nd.act i)) (show x ∈ (S : Set (D.nd.X i))ᶜ from hx))

def prGood (i : D.nd.Loc) :
    Module.End (FractionRing (D.nd.O i))
      (TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i)) :=
  (D.nd.eigSum i ↑(D.nd.Zgood i)).projection (D.nd.eigSum i (↑(D.nd.Zgood i))ᶜ)
    (eig_isCompl i (D.nd.Zgood i))

end Record

section Reduce

open Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br Formalism.NG Formalism.NG.QuotientPowerLengths

variable {D : D7}

def EtaBound (CT : ℕ) (i : D.nd.Loc) (k : Fin 2)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (eta : ℕ) : Prop :=
  ∃ c : D.nd.X i → ℚ,
    D.nd.etaLoc i ≤
      ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℚ) * (c π + padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard) ∧
    ∀ π ∈ D.nd.Zgood i, LocalCongruenceBound CT eta i ρ π (c π)

def CongruenceSingleEndomorphism (CT : ℕ) (i : D.nd.Loc) (k : Fin 2)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (eta : ℕ) : Prop :=
  ∃ (α : Module.End (D.nd.O i) (D.nd.Mt i)) (a : D.nd.X i → D.nd.O i) (c : D.nd.X i → ℚ),
    (∀ π ∈ D.nd.Zgood i, a π ≠ 0 ∧
      (∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π,
        α.baseChange (FractionRing (D.nd.O i)) u = a π • u) ∧
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {a π}) ≤
        c π + padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard ∧
      LocalCongruenceBound CT eta i ρ π (c π)) ∧
    ∀ x, x ∉ D.nd.Zgood i → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
      α.baseChange (FractionRing (D.nd.O i)) u = 0

def CongruenceFamilyEndomorphisms (CT : ℕ) (i : D.nd.Loc) (k : Fin 2)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (eta : ℕ) : Prop :=
  ∃ (E : Set (Module.End (D.nd.O i) (D.nd.Mt i))) (a : D.nd.X i → D.nd.O i) (c : D.nd.X i → ℚ),
    (∀ α ∈ E, (∀ f : D.nd.T i, α * D.nd.act i f = D.nd.act i f * α) ∧
      ∀ x, x ∉ D.nd.Zgood i → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
        α.baseChange (FractionRing (D.nd.O i)) u = 0) ∧
    ∀ π ∈ D.nd.Zgood i, a π ≠ 0 ∧
      (∃ α ∈ E, ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π,
        α.baseChange (FractionRing (D.nd.O i)) u = a π • u) ∧
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {a π}) ≤
        c π + padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard ∧
      LocalCongruenceBound CT eta i ρ π (c π)

open Classical in
def cutLocus (i : D.nd.Loc) (Xs : Set (D.nd.X i)) : Finset (D.nd.X i) :=
  Finset.univ.filter fun x => x ∈ D.nd.Z i ∨ x ∉ Xs

def vccCut (i : D.nd.Loc) (Xs : Set (D.nd.X i)) (π : D.nd.X i) : ℚ :=
  lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ ccAt (D.nd.T i) (cutLocus i Xs) π)

def CutAt (i : D.nd.Loc) (k : Fin 2) (π : D.nd.X i) (Xs : Set (D.nd.X i))
    (β : Module.End (D.nd.O i) (D.nd.Mt i)) (b : D.nd.O i) : Prop :=
  π ∈ Xs ∧ π ∈ D.nd.Z i ∧ (∀ x ∈ Xs, x ∈ D.nd.Z i → x ∈ D.nd.Zgood i) ∧
    (∀ f : D.nd.T i, β * D.nd.act i f = D.nd.act i f * β) ∧ b ≠ 0 ∧
    (∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π, β.baseChange (FractionRing (D.nd.O i)) u = b • u) ∧
    (∀ x, x ∉ Xs → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
      β.baseChange (FractionRing (D.nd.O i)) u = 0) ∧
    lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {b}) ≤
      padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard

def CongruenceLocalDecomposition (CT : ℕ) (i : D.nd.Loc) (k : Fin 2)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (eta : ℕ) : Prop :=
  ∃ (Xs : D.nd.X i → Set (D.nd.X i)) (β : D.nd.X i → Module.End (D.nd.O i) (D.nd.Mt i))
    (b : D.nd.X i → D.nd.O i),
    ∀ π ∈ D.nd.Zgood i, CutAt i k π (Xs π) (β π) (b π) ∧ LocalCongruenceBound CT eta i ρ π (vccCut i (Xs π) π)

end Reduce

end Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

end
end

