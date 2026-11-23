module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0011
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0012
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RingDataOfCrystalline

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.IsAdicCompleteOfIdealPowLe
section
noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem isAdicComplete_of_ideal_pow_le {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I J : Ideal R) [hJ : IsAdicComplete J M] (e : ℕ) (he : 1 ≤ e) (hJI : J ≤ I) (hIJ : I ^ e ≤ J) :
    IsAdicComplete I M := by
  have mono : ∀ {A B : Ideal R}, A ≤ B → ∀ n : ℕ, A ^ n ≤ B ^ n := by
    intro A B h n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ]
      exact Ideal.mul_mono ih h
  have hIJn : ∀ n : ℕ, I ^ (e * n) ≤ J ^ n := fun n => by
    rw [pow_mul]
    exact mono hIJ n
  have hJIn : ∀ n : ℕ, J ^ n ≤ I ^ n := fun n => mono hJI n
  have hle : ∀ n : ℕ, n ≤ e * n := fun n => by nlinarith
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    exact hJ.haus' x fun n => (hx (e * n)).mono (Submodule.smul_mono_left (hIJn n))
  · intro f hf
    obtain ⟨L, hL⟩ := hJ.prec' (fun k => f (e * k)) (fun {m n} hmn =>
      (hf (Nat.mul_le_mul le_rfl hmn)).mono (Submodule.smul_mono_left (hIJn m)))
    refine ⟨L, fun n => ?_⟩
    exact (hf (hle n)).trans ((hL n).mono (Submodule.smul_mono_left (hJIn n)))

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 in
theorem isAdicComplete_integers_local : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l),
    IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := by
  intro l _ LL
  have hc : IsAdicComplete (Ideal.span {((l : ℕ) : ↥(OL LL))}) ↥(OL LL) :=
    Formalism.MainNotions.LiftingTheory.phib_OL_complete LL

  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h
    have h' := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h
    simp only [map_natCast, ZeroMemClass.coe_zero] at h'
    have hp : (l : ℕ) ≠ 0 := (Fact.out : l.Prime).ne_zero
    exact hp (by exact_mod_cast h')
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(OL LL)
  obtain ⟨k, u, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have hmax : IsLocalRing.maximalIdeal ↥(OL LL) = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hspan : Ideal.span {((l : ℕ) : ↥(OL LL))} = IsLocalRing.maximalIdeal ↥(OL LL) ^ k := by
    rw [hmax, Ideal.span_singleton_pow, hk, Ideal.span_singleton_mul_left_unit u.isUnit]

  have hk1 : 1 ≤ k := by
    by_contra hlt
    have hk0 : k = 0 := by omega
    have htop : Ideal.span {((l : ℕ) : ↥(OL LL))} = ⊤ := by
      rw [hspan, hk0, pow_zero, Ideal.one_eq_top]
    have h10 : (1 : ↥(OL LL)) = 0 := by
      apply hc.haus' 1
      intro m
      rw [SModEq.sub_mem, htop, Ideal.top_pow, Submodule.top_smul]
      exact Submodule.mem_top
    exact one_ne_zero h10
  refine isAdicComplete_of_ideal_pow_le (IsLocalRing.maximalIdeal ↥(OL LL))
    (Ideal.span {((l : ℕ) : ↥(OL LL))}) k hk1 ?_ ?_
  · rw [hspan]
    calc IsLocalRing.maximalIdeal ↥(OL LL) ^ k ≤ IsLocalRing.maximalIdeal ↥(OL LL) ^ 1 :=
          Ideal.pow_le_pow_right hk1
      _ = IsLocalRing.maximalIdeal ↥(OL LL) := pow_one _
  · rw [hspan]

end Formalism.MainNotions.N.Ln17
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.IsRhoZeroOfPi0
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.FrobeniusPowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

namespace Formalism.MainNotions.N.Ln17.PCutBoundRho

open Formalism.MainNotions.N.Ln17.PCutBoundRep

theorem H1map_latSmul (T : LocLat G Qp LL O) (o : O) (x : LatticeCohomology T.L) :
    (latSmul T o).H1map x = o • x := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    rw [← Submodule.Quotient.mk_smul]
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk (o • z)
    congr 1
    apply Subtype.ext
    funext g
    show (latSmul T o).f ((z : G → T.V) g) = o • (z : G → T.V) g
    simp [latSmul, algebraMap_smul]

section Rho

variable {W : LocWach PD LL O v n} {A : ArcP n} {c : ZMod n} {T : LocLat G Qp LL O}
  (hRelay : RelayCore W) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p) (hA : A.OK) (hc : c ∈ A.cuts)
  (hW : Win W A T)
include hRelay hcase hl hA hc hW

theorem rho_ex {w : W.DD T} (hw : InI W T c w) : ∃ x, IsRho W A T c w x :=
  (((hRelay hcase hl A hA c hc).1 T hW).2.1 w hw).2.2.2.1

theorem rho_uniq {w : W.DD T} (hw : InI W T c w) {x x' : LatticeCohomology T.L} (h : IsRho W A T c w x)
    (h' : IsRho W A T c w x') : x = x' :=
  (((hRelay hcase hl A hA c hc).1 T hW).2.1 w hw).2.2.2.2.1 x x' h h'

theorem isRho_zero_of_pi0 {w : W.DD T} (hw : InI W T c w) (hπ : InFNc W T c W.π₀ w) : IsRho W A T c w 0 :=
  (((hRelay hcase hl A hA c hc).1 T hW).2.1 w hw).2.2.2.2.2.1 hπ

theorem rho_add {w w' : W.DD T} {x x' : LatticeCohomology T.L} (hw : InI W T c w) (hw' : InI W T c w')
    (h : IsRho W A T c w x) (h' : IsRho W A T c w' x') : IsRho W A T c (w + w') (x + x') :=
  ((hRelay hcase hl A hA c hc).1 T hW).2.2 w w' x x' hw hw' h h'

theorem rho_smul {w : W.DD T} {x : LatticeCohomology T.L} (hw : InI W T c w) (h : IsRho W A T c w x) (o : O) :
    IsRho W A T c (o • w) (o • x) := by
  have h2 := (hRelay hcase hl A hA c hc).2 T T (latSmul T o) hW hW w x hw h
  rwa [W.map_latSmul, H1map_latSmul] at h2

theorem rho_sum {ι : Type} (s : Finset ι) (w : ι → W.DD T) (x : ι → LatticeCohomology T.L)
    (hw : ∀ i ∈ s, InI W T c (w i)) (h : ∀ i ∈ s, IsRho W A T c (w i) (x i)) :
    IsRho W A T c (∑ i ∈ s, w i) (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact isRho_zero_of_pi0 hRelay hcase hl hA hc hW (TypesA.InI_zero W) ⟨0, zero_mem _, smul_zero _, (smul_zero _).symm⟩
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact rho_add hRelay hcase hl hA hc hW (hw j (Finset.mem_insert_self j s))
      (InI_sum W s w fun i hi => hw i (Finset.mem_insert_of_mem hi)) (h j (Finset.mem_insert_self j s))
      (ih (fun i hi => hw i (Finset.mem_insert_of_mem hi)) fun i hi => h i (Finset.mem_insert_of_mem hi))

end Rho

section abelian₂

variable {W : LocWach PD LL O v n}

theorem γ_Lam (hR : GS.RD W) (A : ArcP n) (a : ZMod n) (e : ℕ) :
    ∃ R ∈ W.AΔ, ∃ R' ∈ W.AΔ, R * R' = 1 ∧ W.γA W.gam (abelian₂ W A a e) = R * abelian₂ W A a e := by
  choose r hr r' hr' hrr hγ using GS.psγ hR
  refine ⟨∏ s ∈ Finset.range e, r s ^ A.Hs a e s, prod_mem fun s _ => pow_mem (GS.mem_invariants_of_mem_S1 W (hr s)) _,
    ∏ s ∈ Finset.range e, r' s ^ A.Hs a e s, prod_mem fun s _ => pow_mem (GS.mem_invariants_of_mem_S1 W (hr' s)) _, ?_, ?_⟩
  · rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun s _ => by rw [← mul_pow, hrr, one_pow]
  · unfold abelian₂
    exact GS.γ_prod r hγ e _

theorem φpow_π₀_prod (hR : GS.RD W) (t : ℕ) :
    ∃ U ∈ W.AΔ, (W.φA ^ t) W.π₀ = W.π₀ * (∏ k ∈ Finset.range t, ps W k ^ (PD.p - 1)) * U := by
  obtain ⟨-, ⟨w, hw⟩, -⟩ := id hR
  have hwΔ : (w : LetA O n) ∈ W.AΔ := by
    refine GS.quot_mem W (W.AΔ.mul_mem (GS.π₀_mem W) (pow_mem (GS.qA_mem W) (PD.p - 1))) ?_ ?_
    · rw [map_mul, map_pow]
      exact (GS.isUnit_π₀ hR).mul ((GS.isUnit_qA hR).pow _)
    · have : W.π₀ * qA W ^ (PD.p - 1) * (w : LetA O n) = W.φA W.π₀ := by rw [hw]; ring
      rw [this]
      simpa using TypesA.φA_pow_mem W (TypesA.pi0_mem_ADelta W) 1
  induction t with
  | zero => exact ⟨1, W.AΔ.one_mem, by simp⟩
  | succ t ih =>
    obtain ⟨U, hU, hUe⟩ := ih
    refine ⟨(W.φA ^ t) (w : LetA O n) * U, W.AΔ.mul_mem (TypesA.φA_pow_mem W hwΔ t) hU, ?_⟩
    rw [pow_succ, AlgHom.mul_apply, hw, map_mul, map_mul, map_pow, hUe, Finset.prod_range_succ]
    simp only [ps]
    ring

theorem φpow_π₀_JJ (hR : GS.RD W) (j M G₀ : ℕ) (h2 : 2 * G₀ ≤ (PD.p - 1) * M) :
    ∃ t ∈ W.AΔ, ((W.φA ^ j) W.π₀) ^ M = Formalism.MainNotions.LiftingTheory.JJ W j (2 * G₀) M * t := by
  obtain ⟨U, hU, hUe⟩ := φpow_π₀_prod hR j
  refine ⟨(∏ k ∈ Finset.range j, ps W k ^ ((PD.p - 1) * M - 2 * G₀)) * U ^ M,
    W.AΔ.mul_mem (prod_mem fun k _ => pow_mem (TypesA.ps_mem W k) _) (pow_mem hU M), ?_⟩
  have e1 : (∏ k ∈ Finset.range j, ps W k ^ (PD.p - 1)) ^ M =
      (∏ k ∈ Finset.range j, ps W k ^ (2 * G₀)) * ∏ k ∈ Finset.range j, ps W k ^ ((PD.p - 1) * M - 2 * G₀) := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' h2]
  have hpk : ∀ k, Formalism.MainNotions.LiftingTheory.pk W k = ps W k := fun _ => rfl
  rw [hUe, mul_pow, mul_pow, e1]
  unfold Formalism.MainNotions.LiftingTheory.JJ
  simp only [hpk]
  ring

end abelian₂

section LV

variable (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL)

def LV (g : Fin d → W.EE) (e : ℕ) : Prop :=
  ∃ (w₁ : W.DD T₁) (z : W.DD T₂), InI W T₁ c w₁ ∧ (∃ Λ' ∈ Ps W, InFNc W T₁ c 1 (Λ' • w₁)) ∧
    InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) 1 (abelian₂ W A c (A.len c) • W.map F w₁) ∧
    InFNc W T₂ c W.π₀ z ∧
    RepVV W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) (A.M PD.p) (abelian₂ W A c (A.len c)) b sol
      (W.map F w₁ - z) (fun k => lE W e * g k)

variable {W A F c b sol}

theorem LV_of_lifts {k₀ : Fin d} {f : W.EE} {e : ℕ} (h : LiftsAt W A F c b sol k₀ f e) :
    LV W A F c b sol (fun k => if k = k₀ then f else 0) e := by
  obtain ⟨w₁, z, hw, hΛ, hP, hz, hR⟩ := h
  exact ⟨w₁, z, hw, hΛ, hP, hz, TypesA.RepVV_congr W hR rfl fun k => by rw [mul_ite, mul_zero]⟩

theorem LV_add {g g' : Fin d → W.EE} {e : ℕ} (h : LV W A F c b sol g e) (h' : LV W A F c b sol g' e) :
    LV W A F c b sol (fun k => g k + g' k) e := by
  obtain ⟨w₁, z, hw, ⟨Λ₁, hΛ₁, hΛw₁⟩, hP, hz, hR⟩ := h
  obtain ⟨w₁', z', hw', ⟨Λ₂, hΛ₂, hΛw₂⟩, hP', hz', hR'⟩ := h'
  refine ⟨w₁ + w₁', z + z', TypesA.InI_add W hw hw', ⟨Λ₁ * Λ₂, mul_mem hΛ₁ hΛ₂, ?_⟩, ?_,
    TypesA.InFNc_add W hz hz', ?_⟩
  · have hsplit : (Λ₁ * Λ₂) • (w₁ + w₁') = Λ₂ • (Λ₁ • w₁) + Λ₁ • (Λ₂ • w₁') := by
      rw [smul_add, mul_smul, mul_smul, smul_comm Λ₁ Λ₂ w₁]
    rw [hsplit]
    exact TypesA.InFNc_add W (TypesA.InFNc_smul W (TypesA.Ps_mem W hΛ₂) hΛw₁)
      (TypesA.InFNc_smul W (TypesA.Ps_mem W hΛ₁) hΛw₂)
  · rw [map_add (f := _), smul_add]
    exact TypesA.inMultiple_add W hP hP'
  · exact TypesA.RepVV_congr W (TypesA.RepVV_add W hR hR') (by rw [map_add (f := _)]; abel)
      fun k => (mul_add _ _ _).symm

theorem LV_zero {e : ℕ}
    (h0 : RepVV W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) (A.M PD.p) (abelian₂ W A c (A.len c)) b sol 0
      (fun _ => 0)) : LV W A F c b sol (fun _ => 0) e := by
  refine ⟨0, 0, TypesA.InI_zero W, ⟨1, one_mem _, ?_⟩, ?_, ⟨0, zero_mem _, smul_zero _, (smul_zero _).symm⟩,
    TypesA.RepVV_congr W h0 (by simp) fun k => (mul_zero _).symm⟩
  · rw [smul_zero]; exact ⟨0, zero_mem _, smul_zero _, (smul_zero _).symm⟩
  · rw [map_zero, smul_zero]; exact ⟨0, zero_mem _, (smul_zero _).symm⟩

theorem LV_sum {e : ℕ}
    (h0 : RepVV W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) (A.M PD.p) (abelian₂ W A c (A.len c)) b sol 0
      (fun _ => 0)) {ι : Type} (s : Finset ι) (g : ι → Fin d → W.EE) (h : ∀ i ∈ s, LV W A F c b sol (g i) e) :
    LV W A F c b sol (fun k => ∑ i ∈ s, g i k) e := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LV_zero h0 (e := e)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact LV_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end LV

end Formalism.MainNotions.N.Ln17.PCutBoundRho
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.PpLeHLD
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.DYB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

variable (W : LocWach PD LL O v n)

theorem φD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

theorem γ_smulA (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.γ T (a • x) = W.γA W.gam a • W.γ T x := by
  show W.γD T W.gam (a • x) = W.γA W.gam a • W.γD T W.gam x
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]
  rfl

theorem γA_lA_pow (k : ℕ) : W.γA W.gam (lA W ^ k) = lA W ^ k := by
  unfold lA
  rw [map_pow, map_natCast]

def HLD (T : LocLat G Qp LL O) (c : ZMod n) : AddSubgroup (W.DD T) where
  carrier := {x | (letE (O := O) c : LetA O n) • x = x ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x}
  zero_mem' := ⟨smul_zero _, fun δ _ => map_zero _⟩
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨by rw [smul_add, hx1, hy1], fun δ hδ => by rw [map_add (f := _), hx2 δ hδ, hy2 δ hδ]⟩
  neg_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨by rw [smul_neg, hx1], fun δ hδ => by rw [map_neg, hx2 δ hδ]⟩

theorem Pp_le_HLD (T : LocLat G Qp LL O) (c : ZMod n) : Pp W T c 1 ≤ HLD W T (c + 1) := by
  have hφE : W.φA (letE (O := O) c) = letE (c + 1) := by
    funext k
    unfold letE LocWach.φA letφ
    change W.φ₀ ((Pi.single c 1 : LetA O n) (k - 1)) = (Pi.single (c + 1) 1 : LetA O n) k
    by_cases hk : k = c + 1
    · subst hk
      simp
    · have hk' : k - 1 ≠ c := by
        intro h'
        apply hk
        rw [← h', sub_add_cancel]
      rw [Pi.single_eq_of_ne hk', Pi.single_eq_of_ne hk, map_zero]
  have hid : ∀ d : ZMod n, (letE (O := O) d : LetA O n) * letE d = letE d := by
    intro d
    funext k
    unfold letE
    by_cases hk : k = d
    · subst hk
      simp
    · simp [Pi.single_eq_of_ne hk]
  have hsl : ∀ δ (a : LetA O n) (z : W.DD T), W.γD T δ (a • z) = W.γA δ a • W.γD T δ z := by
    intro δ a z
    rw [← algebraMap_smul W.EE a z, W.γD_smul, W.γE_ext, algebraMap_smul]
    rfl
  unfold Pp
  rw [AddSubgroup.closure_le]
  rintro z ⟨a, ha, x, ⟨hxN, hxl⟩, rfl⟩
  obtain ⟨_, hxD⟩ : x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x := hxN
  obtain ⟨y, _, rfl⟩ := hxl
  simp only [pow_one, LinearMap.smul_apply, LinearMap.id_apply] at hxD ⊢
  change _ ∧ _
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [φD_smulA W T, hφE]
    simp only [smul_smul]
    congr 1
    linear_combination a * hid (c + 1)
  · rw [hsl, ← W.φγ_comm, hxD δ hδ, ha δ hδ]

theorem Pp_smul (T : LocLat G Qp LL O) (c : ZMod n) {a : LetA O n} (ha : a ∈ W.AΔ) {y : W.DD T}
    (hy : y ∈ Pp W T c 1) : a • y ∈ Pp W T c 1 := by
  unfold Pp at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hz
    apply AddSubgroup.subset_closure
    exact ⟨a * b, W.AΔ.mul_mem ha hb, x, hx, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [smul_add]; exact add_mem hu hw
  | neg u _ hu => rw [smul_neg]; exact neg_mem hu

theorem InNΔi_γ (T : LocLat G Qp LL O) (c : ZMod n) {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c x) : Formalism.MainNotions.LiftingTheory.InNΔi W T c (W.γ T x) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨hN, hD⟩ : x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x := h1
  have hsl : ∀ δ (a : LetA O n) (z : W.DD T), W.γD T δ (a • z) = W.γA δ a • W.γD T δ z := by
    intro δ a z
    rw [← algebraMap_smul W.EE a z, W.γD_smul, W.γE_ext, algebraMap_smul]
    rfl
  have hγE : W.γA W.gam (letE (O := O) c) = letE c := by
    funext k
    unfold letE LocWach.γA letγ
    change W.γ₀ W.gam ((Pi.single c 1 : LetA O n) k) = (Pi.single c 1 : LetA O n) k
    by_cases hk : k = c
    · subst hk
      simp
    · rw [Pi.single_eq_of_ne hk, map_zero]
  refine ⟨?_, ?_⟩
  · show W.γD T W.gam x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (W.γD T W.gam x) = W.γD T W.gam x
    refine ⟨W.N_Γ T W.gam x hN, fun δ hδ => ?_⟩
    rw [← W.γD_mul, mul_comm, W.γD_mul, hD δ hδ]
  · obtain ⟨y, hy, rfl⟩ := h2
    refine ⟨W.γD T W.gam y, W.N_Γ T W.gam y hy, ?_⟩
    show (letE c • LinearMap.id) (W.γD T W.gam y) = W.γD T W.gam ((letE c • LinearMap.id) y)
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [hsl, hγE]

theorem Pp_γ (T : LocLat G Qp LL O) (c : ZMod n) {y : W.DD T} (hy : y ∈ Pp W T c 1) :
    W.γ T y ∈ Pp W T c 1 := by
  have hsl : ∀ δ (a : LetA O n) (z : W.DD T), W.γD T δ (a • z) = W.γA δ a • W.γD T δ z := by
    intro δ a z
    rw [← algebraMap_smul W.EE a z, W.γD_smul, W.γE_ext, algebraMap_smul]
    rfl
  have hcomm : ∀ (g h : W.Gam) (a : LetA O n), W.γA g (W.γA h a) = W.γA h (W.γA g a) := by
    intro g h a
    funext k
    unfold LocWach.γA letγ
    change W.γ₀ g (W.γ₀ h (a k)) = W.γ₀ h (W.γ₀ g (a k))
    rw [← AlgHom.mul_apply, ← map_mul, mul_comm, map_mul, AlgHom.mul_apply]
  unfold Pp at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    apply AddSubgroup.subset_closure
    refine ⟨W.γA W.gam a, ?_, W.γ T x, InNΔi_γ W T c hx, ?_⟩
    · show ∀ δ ∈ W.DelF, W.γA δ (W.γA W.gam a) = W.γA W.gam a
      intro δ hδ
      rw [hcomm, ha δ hδ]
    · show W.γD T W.gam (a • (W.φD T ^ 1) x) = W.γA W.gam a • (W.φD T ^ 1) (W.γD T W.gam x)
      rw [pow_one, hsl, W.φγ_comm]
  | zero => rw [map_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [map_add (f := _)]; exact add_mem hu hw
  | neg u _ hu => rw [map_neg]; exact neg_mem hu

theorem Pp_qpow (T : LocLat G Qp LL O) (c : ZMod n) (k : ℕ)
    (hq : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T c x → qA W ^ k • W.φD T x ∈ W.N T) {y : W.DD T}
    (hy : y ∈ Pp W T c 1) : qA W ^ k • y ∈ W.NΔ T := by
  have hsl : ∀ δ (a : LetA O n) (z : W.DD T), W.γD T δ (a • z) = W.γA δ a • W.γD T δ z := by
    intro δ a z
    rw [← algebraMap_smul W.EE a z, W.γD_smul, W.γE_ext, algebraMap_smul]
    rfl
  have htor : ∀ g h : W.Gam, g ∈ W.DelF → h ∈ W.DelF → g * h ∈ W.DelF := by
    intro g h hg hh
    rw [W.DelF_def] at hg hh ⊢
    obtain ⟨a, ha, hga⟩ := hg
    obtain ⟨b, hb, hhb⟩ := hh
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [mul_pow, pow_mul, hga, one_pow, mul_comm a b, pow_mul, hhb, one_pow, one_mul]
  have hinv : ∀ g : W.Gam, g ∈ W.DelF → g⁻¹ ∈ W.DelF := by
    intro g hg
    rw [W.DelF_def] at hg ⊢
    obtain ⟨a, ha, hga⟩ := hg
    exact ⟨a, ha, by rw [inv_pow, hga, inv_one]⟩
  have hπ : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀ := by
    intro δ hδ
    funext k
    unfold LocWach.γA letγ LocWach.π₀
    change W.γ₀ δ W.π₀₁ = W.π₀₁
    unfold LocWach.π₀₁
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sub, map_one, map_natCast, map_sum]
    congr 1
    have hm : ∀ δ' : W.Gam, W.γ₀ δ (W.γ₀ δ' (1 + PowerSeries.X)) = W.γ₀ (δ * δ') (1 + PowerSeries.X) :=
      fun δ' => by rw [map_mul, AlgHom.mul_apply]
    simp only [hm]
    exact Finset.sum_nbij' (δ * ·) (δ⁻¹ * ·) (fun a ha => htor δ a hδ ha)
      (fun a ha => htor _ a (hinv δ hδ) ha) (fun a _ => inv_mul_cancel_left δ a)
      (fun a _ => mul_inv_cancel_left δ a) (fun a _ => rfl)
  have hqΔ : ∀ δ ∈ W.DelF, W.γA δ (qA W) = qA W := by
    intro δ hδ
    unfold qA lA
    rw [map_add (f := _), hπ δ hδ, map_natCast]
  unfold Pp at hy
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    obtain ⟨_, hxD⟩ : x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x := hx.1
    have hN : qA W ^ k • W.φD T x ∈ W.N T := hq x hx
    rw [pow_one, smul_smul, mul_comm (qA W ^ k) a, ← smul_smul]
    show a • qA W ^ k • W.φD T x ∈ W.N T ∧
      ∀ δ ∈ W.DelF, W.γD T δ (a • qA W ^ k • W.φD T x) = a • qA W ^ k • W.φD T x
    refine ⟨(W.N T).smul_mem a hN, fun δ hδ => ?_⟩
    rw [hsl, hsl, ← W.φγ_comm, hxD δ hδ, ha δ hδ, map_pow, hqΔ δ hδ]
  | zero => rw [smul_zero]; exact (W.NΔ T).zero_mem
  | add u w _ _ hu hw => rw [smul_add]; exact (W.NΔ T).add_mem hu hw
  | neg u _ hu => rw [smul_neg]; exact (W.NΔ T).neg_mem hu

end Formalism.MainNotions.N.FrobeniusPowerSeries.DYB

end
end

