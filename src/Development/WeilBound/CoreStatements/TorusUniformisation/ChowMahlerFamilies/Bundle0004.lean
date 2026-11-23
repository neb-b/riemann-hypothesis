module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XPowspan
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.A_powspan

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mul_mem_gen (R : Subalgebra o Ω) (S : Set Ω) {a e : Ω} (ha : a ∈ R) (he : e ∈ S) :
    a * e ∈ spanOver R S :=
  AddSubgroup.subset_closure ⟨a, ha, e, he, rfl⟩

theorem span_stable (R : Subalgebra o Ω) (S : Set Ω) {a : Ω} (ha : a ∈ R) {v : Ω}
    (hv : v ∈ spanOver R S) : a * v ∈ spanOver R S := by
  induction hv using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a', ha', e, he, rfl⟩ := hx
    rw [smul_eq_mul, ← mul_assoc]
    exact mul_mem_gen R S (R.mul_mem ha ha') he
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem span_le (R : Subalgebra o Ω) (S : Set Ω) (T : AddSubgroup Ω)
    (hT : ∀ a ∈ R, ∀ v ∈ T, a * v ∈ T) (hS : ∀ e ∈ S, e ∈ T) : spanOver R S ≤ T := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨a, ha, e, he, rfl⟩
  exact hT a ha e (hS e he)

theorem span_loc (R : Subalgebra o Ω) (S : Set Ω) {f : Ω} (hf : f ∈ R) (b : Ω)
    (hS : ∀ e ∈ S, ∃ n : ℕ, f ^ n * (e / b) ∈ R) {v : Ω} (hv : v ∈ spanOver R S) :
    ∃ n : ℕ, f ^ n * (v / b) ∈ R := by
  induction hv using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, e, he, rfl⟩ := hx
    obtain ⟨n, hn⟩ := hS e he
    refine ⟨n, ?_⟩
    have : f ^ n * (a • e / b) = a * (f ^ n * (e / b)) := by rw [smul_eq_mul]; ring
    rw [this]; exact R.mul_mem ha hn
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : f ^ (n + m) * ((x + y) / b) = f ^ m * (f ^ n * (x / b)) + f ^ n * (f ^ m * (y / b)) := by
      ring
    rw [this]
    exact R.add_mem (R.mul_mem (R.pow_mem hf m) hn) (R.mul_mem (R.pow_mem hf n) hm)
  | neg x _ hx =>
    obtain ⟨n, hn⟩ := hx
    refine ⟨n, ?_⟩
    have : f ^ n * (-x / b) = -(f ^ n * (x / b)) := by ring
    rw [this]; exact R.neg_mem hn

theorem mem_of_loc (R : Subalgebra o Ω) (T : AddSubgroup Ω) (hT : ∀ a ∈ R, ∀ v ∈ T, a * v ∈ T)
    {k : ℕ} (f c : Fin k → Ω) (hf : ∀ l, f l ∈ R) (hc : ∀ l, c l ∈ R) (hs : ∑ l, c l * f l = 1)
    {w : Ω} (hw : ∀ l, ∃ n : ℕ, f l ^ n * w ∈ T) : w ∈ T := by
  let I : Ideal R :=
    { carrier := {r | (r : Ω) * w ∈ T}
      add_mem' := fun {x y} hx hy => by
        change ((x + y : R) : Ω) * w ∈ T
        rw [Subalgebra.coe_add, add_mul]; exact add_mem hx hy
      zero_mem' := by
        change ((0 : R) : Ω) * w ∈ T
        simp
      smul_mem' := fun r x hx => by
        change ((r * x : R) : Ω) * w ∈ T
        rw [Subalgebra.coe_mul, mul_assoc]; exact hT r r.2 _ hx }
  have h1 : (1 : R) ∈ I.radical := by
    have : (1 : R) = ∑ l, (⟨c l, hc l⟩ : R) * ⟨f l, hf l⟩ := by
      apply Subtype.ext
      simp [hs]
    rw [this]
    refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ ?_
    obtain ⟨n, hn⟩ := hw l
    exact ⟨n, by
      change (((⟨f l, hf l⟩ : R) ^ n : R) : Ω) * w ∈ T
      simpa using hn⟩
  obtain ⟨n, hn⟩ := h1
  rw [one_pow] at hn
  have : ((1 : R) : Ω) * w ∈ T := hn
  simpa using this

theorem unpack (R : Subalgebra o Ω) (X : AddSubgroup Ω) (f : Ω)
    (h : ∃ b : Fin 1 → Ω, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ e, (∃ n : ℕ, f ^ n • e ∈ X) ↔
        ∃ a : Fin 1 → Ω, (∀ q, ∃ n : ℕ, f ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q) :
    ∃ b : Ω, b ≠ 0 ∧ (∃ m : ℕ, f ^ m * b ∈ X) ∧ ∀ x ∈ X, ∃ n : ℕ, f ^ n * (x / b) ∈ R := by
  obtain ⟨b, hb, -, h⟩ := h
  have hb0 : b 0 ≠ 0 := hb.ne_zero 0
  refine ⟨b 0, hb0, ?_, fun x hx => ?_⟩
  · exact (h (b 0)).2 ⟨fun _ => 1, fun _ => ⟨0, by simpa using R.one_mem⟩, by simp⟩
  · obtain ⟨a, ha, hx'⟩ := (h x).1 ⟨0, by simpa using hx⟩
    obtain ⟨n, hn⟩ := ha 0
    refine ⟨n, ?_⟩
    have : x / b 0 = a 0 := by
      rw [hx']; simp [hb0]
    rwa [this]

theorem locFree_pow (R : Subalgebra o Ω) (p : ℕ) (X : AddSubgroup Ω) (hX : LocFree R 1 X) :
    LocFree R 1 (powSpan R p X) := by
  obtain ⟨-, k, f, c, hf, hc, hs, hl⟩ := hX
  refine ⟨fun a ha e he => span_stable R _ ha he, k, f, c, hf, hc, hs, fun l => ?_⟩
  obtain ⟨b, hb, ⟨m, hm⟩, hx⟩ := unpack R X (f l) (hl l)
  have hbp : b ^ p ≠ 0 := pow_ne_zero p hb
  refine ⟨fun _ => b ^ p, ?_, ?_, fun e => ⟨?_, ?_⟩⟩
  · exact linearIndependent_unique_iff.2 hbp
  · rw [eq_top_iff]
    intro v _
    have : v = (v / b ^ p) • b ^ p := by simp [hbp]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  · rintro ⟨n, hn⟩
    obtain ⟨n', hn'⟩ := span_loc R _ (hf l) (b ^ p) (by
      rintro _ ⟨x, hx', rfl⟩
      obtain ⟨j, hj⟩ := hx x hx'
      refine ⟨j * p, ?_⟩
      have := R.pow_mem hj p
      rwa [mul_pow, ← pow_mul, div_pow] at this) hn
    refine ⟨fun _ => e / b ^ p, fun _ => ⟨n' + n, ?_⟩, by simp [hbp]⟩
    have : f l ^ (n' + n) * (e / b ^ p) = f l ^ n' * (f l ^ n • e / b ^ p) := by
      rw [smul_eq_mul]; ring
    rwa [this]
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨n, hn⟩ := ha 0
    refine ⟨n + m * p, ?_⟩
    have : f l ^ (n + m * p) • (∑ q : Fin 1, a q • b ^ p) = (f l ^ n * a 0) * (f l ^ m * b) ^ p := by
      simp only [Fin.sum_univ_one, smul_eq_mul]; ring
    rw [this]
    exact mul_mem_gen R _ hn ⟨_, hm, rfl⟩

end PositivityTheory.Xgn.A_powspan

open PositivityTheory.Xgn.A_powspan in
theorem PositivityTheory.Xgn.t_powspan : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ (p : ℕ) (X : AddSubgroup Ω), LocFree R 1 X → LocFree R 1 (powSpan R p X) ∧ powSpan RC p (spanOver RC (algebraMap Ω C '' X)) = spanOver RC (algebraMap Ω C '' powSpan R p X) := by
  intro o Ω C _ _ _ _ _ _ _ R RC hR p X hX
  refine ⟨locFree_pow R p X hX, le_antisymm ?_ ?_⟩
  · obtain ⟨-, k, f, c, hf, hc, hs, hl⟩ := hX
    refine span_le RC _ _ (fun a ha v hv => span_stable RC _ ha hv) ?_
    rintro _ ⟨z, hz, rfl⟩
    refine mem_of_loc RC _ (fun a ha v hv => span_stable RC _ ha hv)
      (fun l => algebraMap Ω C (f l)) (fun l => algebraMap Ω C (c l)) (fun l => hR _ (hf l))
      (fun l => hR _ (hc l)) ?_ fun l => ?_
    · have := congrArg (algebraMap Ω C) hs
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum] using this
    · obtain ⟨b, hb, ⟨m, hm⟩, hx⟩ := unpack R X (f l) (hl l)
      have hb' : algebraMap Ω C b ≠ 0 := by simpa using hb
      obtain ⟨n, hn⟩ := span_loc RC _ (hR _ (hf l)) (algebraMap Ω C b) (by
        rintro _ ⟨x, hx', rfl⟩
        obtain ⟨j, hj⟩ := hx x hx'
        exact ⟨j, by simpa using hR _ hj⟩) hz
      refine ⟨(n + m) * p, ?_⟩
      have : algebraMap Ω C (f l) ^ ((n + m) * p) * z ^ p =
          (algebraMap Ω C (f l) ^ n * (z / algebraMap Ω C b)) ^ p *
            algebraMap Ω C (1 * (f l ^ m * b) ^ p) := by
        rw [one_mul, map_pow, map_mul, map_pow, ← mul_pow, pow_mul, ← mul_pow]
        congr 1
        field_simp
        ring
      beta_reduce
      rw [this]
      exact mul_mem_gen RC _ (RC.pow_mem hn p)
        ⟨_, mul_mem_gen R _ R.one_mem ⟨_, hm, rfl⟩, rfl⟩
  · refine span_le RC _ _ (fun a ha v hv => span_stable RC _ ha hv) ?_
    rintro _ ⟨y, hy, rfl⟩
    have : powSpan R p X ≤ (powSpan RC p (spanOver RC (algebraMap Ω C '' X))).comap
        (algebraMap Ω C).toAddMonoidHom := by
      refine span_le R _ _ (fun a ha v hv => ?_) ?_
      · change algebraMap Ω C (a * v) ∈ powSpan RC p _
        rw [map_mul]
        exact span_stable RC _ (hR a ha) hv
      · rintro _ ⟨x, hx, rfl⟩
        change algebraMap Ω C (x ^ p) ∈ powSpan RC p _
        have h1 : algebraMap Ω C (x ^ p) = 1 * (1 * algebraMap Ω C x) ^ p := by simp
        rw [h1]
        exact mul_mem_gen RC _ RC.one_mem ⟨_, mul_mem_gen RC _ RC.one_mem ⟨x, hx, rfl⟩, rfl⟩
    exact this hy
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSummandOfQuot
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.A_summand_of_quot

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
  {E : Type} [AddCommGroup E] [Module Ω E]

def toSub (L : AddSubgroup E) (h : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) : Submodule R E where
  carrier := L
  add_mem' := fun ha hb => L.add_mem ha hb
  zero_mem' := L.zero_mem
  smul_mem' := fun a e he => h a a.2 e he

theorem exists_dual {r : ℕ} {L : AddSubgroup E} (h : LocFree R r L) :
    Module.finrank Ω E = r ∧ ∃ (k : ℕ) (φ : Fin k × Fin r → Module.Dual Ω E) (v : Fin k × Fin r → E),
      (∀ i, v i ∈ L) ∧ (∀ i, ∀ e ∈ L, φ i e ∈ R) ∧ ∀ e, ∑ i, φ i e • v i = e := by
  have h' : LocFree R r (toSub R L h.1).toAddSubgroup := h
  refine ⟨(LocFreeProj.main R r (toSub R L h.1) h').2.2.1, ?_⟩
  obtain ⟨k, f, c, B, hsum, hgen, hcoord⟩ := LocFreeProj.exists_charts h'
  choose n0 hn0 using hgen
  have hs : ∀ j q, ((f j : Ω) ^ (Finset.univ.sup fun i : Fin k × Fin r => n0 i.1 i.2)) • B j q ∈ toSub R L h.1 :=
    fun j q => LocFreeProj.pow_smul_mem (f j)
      (Finset.le_sup (f := fun i : Fin k × Fin r => n0 i.1 i.2) (Finset.mem_univ (j, q))) (hn0 j q)
  generalize hN0 : (Finset.univ.sup fun i : Fin k × Fin r => n0 i.1 i.2) = N0 at hs
  have hP0 : ∀ (l : Fin k) (p : Fin r) (jq : Fin k × Fin r),
      ∃ n, (f l : Ω) ^ n * (B l).repr ((f jq.1 : Ω) ^ N0 • B jq.1 jq.2) p ∈ R :=
    fun l p jq => hcoord l p _ (hs jq.1 jq.2)
  choose nP hnP using hP0
  have hbound : ∀ e ∈ toSub R L h.1, ∀ l p,
      (f l : Ω) ^ (Finset.univ.sup fun i : Fin k × Fin r × (Fin k × Fin r) => nP i.1 i.2.1 i.2.2) * (B l).repr e p ∈ R := by
    intro e he l p
    choose m hm using fun (jq : Fin k × Fin r) => hcoord jq.1 jq.2 e he
    obtain ⟨d, hd⟩ := LocFreeProj.exists_pow_cover f c hsum (Finset.univ.sup m + N0)
    have hexp := LocFreeProj.expand f d B (Finset.univ.sup m) N0 hd e
    have key : (B l).coord p e = ∑ i : Fin k × Fin r,
        ((d i.1 : Ω) * ((f i.1 : Ω) ^ (Finset.univ.sup m) * (B i.1).repr e i.2)) *
          (B l).coord p ((f i.1 : Ω) ^ N0 • B i.1 i.2) := by
      conv_lhs => rw [← hexp]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul]
    rw [← Module.Basis.coord_apply, key, Finset.mul_sum]
    refine R.sum_mem fun i _ => ?_
    rw [mul_left_comm]
    refine R.mul_mem (R.mul_mem (d i.1).2
      (LocFreeProj.pow_mul_mem (f i.1) (Finset.le_sup (Finset.mem_univ i)) (hm i))) ?_
    rw [Module.Basis.coord_apply]
    exact LocFreeProj.pow_mul_mem (f l)
      (Finset.le_sup (f := fun i : Fin k × Fin r × (Fin k × Fin r) => nP i.1 i.2.1 i.2.2)
        (Finset.mem_univ (l, p, i))) (hnP l p i)
  generalize (Finset.univ.sup fun i : Fin k × Fin r × (Fin k × Fin r) => nP i.1 i.2.1 i.2.2) = P at hbound
  obtain ⟨d', hd'⟩ := LocFreeProj.exists_pow_cover f c hsum (P + N0)
  refine ⟨k, fun i => ((d' i.1 : Ω) * (f i.1 : Ω) ^ P) • (B i.1).coord i.2,
    fun i => (f i.1 : Ω) ^ N0 • B i.1 i.2, fun i => hs i.1 i.2, ?_, ?_⟩
  · intro i e he
    simp only [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
    rw [mul_assoc]
    exact R.mul_mem (d' i.1).2 (hbound e he i.1 i.2)
  · intro e
    have hx := LocFreeProj.expand f d' B P N0 hd' e
    convert hx using 2 with i
    simp only [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul, mul_assoc]

theorem locFree_of_dual {ι : Type} [Fintype ι] {r : ℕ} {L : AddSubgroup E}
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) (hr : Module.finrank Ω E = r)
    (φ : ι → Module.Dual Ω E) (v : ι → E) (hvL : ∀ i, v i ∈ L) (hφ : ∀ i, ∀ e ∈ L, φ i e ∈ R)
    (hv : ∀ e, ∑ i, φ i e • v i = e) : LocFree R r L := by
  have h1 := LocFreeProj.finite_projective (L := toSub R L hL) φ (fun i => ⟨v i, hvL i⟩) hφ hv
  have h2 := LocFreeProj.isBaseChange (L := toSub R L hL) φ (fun i => ⟨v i, hvL i⟩) hφ hv
  exact LocFreeProj.locFree_of_projective R r (toSub R L hL) h1.1 h1.2 hr h2

end PositivityTheory.Xgn.A_summand_of_quot

open PositivityTheory.Xgn.A_summand_of_quot in
theorem PositivityTheory.Xgn.summand_iff_locFree_quot : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {V : Type} [AddCommGroup V] [Module Ω V] (U : Submodule Ω V) (N m : ℕ) (L : AddSubgroup V), LocFree R N L → (LocFree R m (L.map U.mkQ.toAddMonoidHom) → Summand L U) ∧ (Summand L U → LocFree R (Module.finrank Ω U) (L.comap U.subtype.toAddMonoidHom) ∧ LocFree R (N - Module.finrank Ω U) (L.map U.mkQ.toAddMonoidHom)) := by
  intro o Ω _ _ _ R V _ _ U N m L hN
  have hst : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L := hN.1
  constructor
  · intro hm
    obtain ⟨-, k, φ, v, hv, hφ, hsum⟩ := PositivityTheory.Xgn.A_summand_of_quot.exists_dual R hm
    have hlift : ∀ i, ∃ e ∈ L, U.mkQ e = v i := fun i => by
      obtain ⟨e, he, hev⟩ := AddSubgroup.mem_map.1 (hv i)
      exact ⟨e, he, hev⟩
    choose w hw hwv using hlift
    have hkey : ∀ x : V ⧸ U, U.mkQ (∑ i, φ i x • w i) = x := by
      intro x
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_smul, hwv]
      exact hsum x
    refine ⟨LinearMap.id - (∑ i, LinearMap.smulRight (φ i) (w i)) ∘ₗ U.mkQ, ?_, ?_, ?_⟩
    · intro x
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, LinearMap.sum_apply,
        LinearMap.smulRight_apply, map_sub, hkey, sub_self]
    · intro u hu
      have h0 : U.mkQ u = 0 := (Submodule.Quotient.mk_eq_zero U).2 hu
      simp [h0]
    · intro e he
      have hme : U.mkQ e ∈ AddSubgroup.map U.mkQ.toAddMonoidHom L := AddSubgroup.mem_map_of_mem _ he
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, LinearMap.sum_apply,
        LinearMap.smulRight_apply]
      exact sub_mem he (AddSubgroup.sum_mem _ fun i _ => hst _ (hφ i _ hme) _ (hw i))
  · rintro ⟨ρ, hρU, hρid, hρL⟩
    obtain ⟨hrank, k, φ, v, hv, hφ, hsum⟩ := PositivityTheory.Xgn.A_summand_of_quot.exists_dual R hN
    have hfin : Module.Finite Ω V := by
      refine Module.Finite.of_surjective (∑ i, LinearMap.smulRight (LinearMap.proj i : (Fin k × Fin N → Ω) →ₗ[Ω] Ω) (v i)) ?_
      intro e
      refine ⟨fun i => φ i e, ?_⟩
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
      exact hsum e
    constructor
    · refine PositivityTheory.Xgn.A_summand_of_quot.locFree_of_dual R (fun a ha e he => hst a ha _ he) rfl
        (fun i => (φ i).comp U.subtype) (fun i => ⟨ρ (v i), hρU _⟩) (fun i => hρL _ (hv i))
        (fun i e he => hφ i _ he) ?_
      intro e
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.comp_apply, Submodule.subtype_apply]
      calc ∑ i, φ i e • ρ (v i) = ρ (∑ i, φ i e • v i) := by simp [map_sum, map_smul]
        _ = e := by rw [hsum]; exact hρid _ e.2
    · have hker : ∀ i, U ≤ LinearMap.ker ((φ i).comp (LinearMap.id - ρ)) := by
        intro i u hu
        simp [LinearMap.mem_ker, hρid u hu]
      refine PositivityTheory.Xgn.A_summand_of_quot.locFree_of_dual R ?_ ?_
        (fun i => U.liftQ ((φ i).comp (LinearMap.id - ρ)) (hker i)) (fun i => U.mkQ (v i))
        (fun i => AddSubgroup.mem_map_of_mem _ (hv i)) ?_ ?_
      · intro a ha x hx
        obtain ⟨e, he, rfl⟩ := AddSubgroup.mem_map.1 hx
        refine AddSubgroup.mem_map.2 ⟨a • e, hst a ha e he, ?_⟩
        simp
      · rw [← hrank, ← Submodule.finrank_quotient_add_finrank U]
        omega
      · intro i x hx
        obtain ⟨e, he, rfl⟩ := AddSubgroup.mem_map.1 hx
        simp only [LinearMap.toAddMonoidHom_coe, Submodule.mkQ_apply, Submodule.liftQ_apply,
          LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
        exact hφ i _ (sub_mem he (hρL e he))
      · intro x
        obtain ⟨e, rfl⟩ := U.mkQ_surjective x
        simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.comp_apply, LinearMap.sub_apply,
          LinearMap.id_apply]
        have h1 : ∑ i, φ i (e - ρ e) • (Submodule.Quotient.mk (v i) : V ⧸ U) =
            U.mkQ (∑ i, φ i (e - ρ e) • v i) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp [map_sum, map_smul]
        rw [h1, hsum, map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply,
          (Submodule.Quotient.mk_eq_zero U).2 (hρU e), sub_zero]
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XTestptExists
section
open GlobalTheory.CompanionTheory.Ar.Num

theorem PositivityTheory.Xgn.t_testpt_exists : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (A : Subalgebra o Ω) (p : ℕ), p.Prime → (p : Ω) ≠ 0 → IsDiscreteValuationRing A → IsFractionRing A Ω → ¬ IsUnit (p : A) → ∃ (C : Type) (_ : Field C) (_ : Algebra o C) (_ : Algebra Ω C) (_ : IsScalarTower o Ω C) (RC : Subalgebra o C), IsTestPt p A RC ∧ ∀ a : Ω, algebraMap Ω C a ∈ RC → a ∈ A := by
  intro o Ω _ _ _ A p _ hp0 _ _ hu
  have hpA : algebraMap A Ω (p : A) = (p : Ω) := map_natCast _ p
  have ha0 : (p : A) ≠ 0 := fun h => hp0 (by rw [← hpA, h, map_zero])
  obtain ⟨C, _, _, _, _, _, hC, hr⟩ :=
    GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing A Ω ha0
      ((IsLocalRing.mem_maximalIdeal _).2 hu) (r := 1 / 2) (by norm_num) (by norm_num)
  have hmem : ∀ a : Ω, ‖algebraMap Ω C a‖ ≤ 1 ↔ a ∈ A := fun a => by
    rw [hC]
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨a, h⟩, rfl⟩⟩
  have hp1 : ‖(p : C)‖ < 1 := by
    rw [hpA, map_natCast] at hr
    rw [hr]; norm_num
  letI : Algebra o C := ((algebraMap Ω C).comp (algebraMap o Ω)).toAlgebra
  haveI : IsScalarTower o Ω C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let RC : Subalgebra o C :=
    { (GlobalTheory.normIntegers C).toSubring.toSubsemiring with
      algebraMap_mem' := fun r =>
        GlobalTheory.mem_normIntegers_iff.2 ((hmem _).2 (A.algebraMap_mem r)) }
  have hRC : ∀ c : C, c ∈ RC ↔ ‖c‖ ≤ 1 := fun c => GlobalTheory.mem_normIntegers_iff
  have hv : ∀ c : C, c ∈ RC ↔ NormedField.valuation c ≤ 1 := fun c => Iff.rfl
  have hO : (NormedField.valuation (K := C)).Integers RC :=
    ⟨Subtype.val_injective, fun x => (hv _).1 x.2, fun r hr => ⟨⟨r, (hv r).2 hr⟩, rfl⟩⟩
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, RC,
    ⟨inferInstance, ⟨NormedField.valuation, hv, ?_⟩, ?_, fun a ha => (hRC _).2 ((hmem a).2 ha)⟩,
    fun a ha => (hmem a).1 ((hRC _).1 ha)⟩
  · rw [NormedField.valuation_apply, ← NNReal.coe_lt_coe]
    exact hp1
  · exact GlobalTheory.NormIntegers.isAdicComplete_span_singleton hO (by simpa only [map_natCast] using hp1)
end

