module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.Bundle0001
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0037

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.Column
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem inc_cast {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) {u u' : WeightFamilies.Wt D j}
    (h : u = u') (F : B.Cusp j u) : X.inc u' (h ▸ F) = X.inc u F := by
  subst h; rfl

theorem one_le_of_nonneg_of_ne {a : WithTop ℤ} (h0 : 0 ≤ a) (h1 : a ≠ 0) : 1 ≤ a := by
  induction a using WithTop.recTopCoe with
  | top => exact le_top
  | coe n =>
    have h2 : (0 : ℤ) ≤ n := by exact_mod_cast h0
    have h3 : n ≠ 0 := fun h => h1 (by rw [h]; rfl)
    exact_mod_cast (show (1 : ℤ) ≤ n by omega)

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem wfr_eq (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (jj : Fin G.N) :
    fr0 X la G.w 1 ⟨emb X la G.N (X.inc _ ((add_zero_weight_one_eq wL).symm ▸ G.w jj : B.Cusp j (addL (wt0 D j) wL 1))),
      emb_mem_Vw X la G.N _ _⟩ = wfr G la jj := by
  unfold wfr
  congr 1
  exact Subtype.ext (congrArg (emb X la G.N) (inc_cast X (add_zero_weight_one_eq wL).symm (G.w jj)))

theorem ord_wfr_nonneg (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B)
    (hT : Q.InTie S) (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) (ζ : PtsG G la) (jj : Fin G.N) :
    0 ≤ ord (unifO X la G.N) ζ (toOsK X la G.w (wfr G la jj)) := by
  obtain ⟨hd1, hd2, -, -, -, hk, -⟩ := hT ζ
  have e := hk 1 ((add_zero_weight_one_eq wL).symm ▸ G.w jj : B.Cusp j (addL (wt0 D j) wL 1))
  rw [wfr_eq, inc_cast] at e
  have hv : X.depth S.sW wL la (Q.y ζ) ≤ X.vAt la (Q.y ζ) (X.inc wL (G.w jj)) := iInf₂_le _ (hw jj)
  have hd : X.depth S.sW wL la (Q.y ζ) = (((X.depth S.sW wL la (Q.y ζ)).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal hd1 hd2).symm
  have hv' : (((X.depth S.sW wL la (Q.y ζ)).toReal : ℝ) : EReal) ≤ X.vAt la (Q.y ζ) (X.inc wL (G.w jj)) := by
    rw [← hd]; exact hv
  have hb := ereal_bound (ep := ep (unifO X la G.N) ζ) (T := 1) hd hv'
  have key : (((0 : ℤ) : ℝ) : EReal) ≤ toE (ord (unifO X la G.N) ζ (toOsK X la G.w (wfr G la jj))) := by
    rw [e]
    refine le_trans (le_of_eq ?_) hb
    simp
  simpa using le_of_coe_le_toE key

theorem one_eq_sum_wfr (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) :
    (1 : ↥(Frac0 X la G.w)) = ∑ k, (@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ (Tv X la G.N (0, k))) • wfr G la k := by
  have h1 : frac X la G.w 1 (sec X la G.w 0) = 1 := by rw [frac_apply, pow_one, section_mul_inverse_eq_one]
  have h2 : frac X la G.w 1 (sec X la G.w 0) = ∑ k, (@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ (Tv X la G.N (0, k))) •
      frac X la G.w 1 (emb X la G.N (X.inc wL (G.w k))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sec, map_sum]
    simp only [map_smul]
  apply Subtype.ext
  rw [OneMemClass.coe_one, ← h1, h2, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl

theorem one_eq_sum_toOsK (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) :
    (1 : OsK X la G.w) = ∑ k, algebraMap (Op X la G.N) (OsK X la G.w) (Tv X la G.N (0, k)) *
      toOsK X la G.w (wfr G la k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_one (toOsK X la G.w), one_eq_sum_wfr G la, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Algebra.smul_def, (IsScalarTower.algebraMap_apply (Op X la G.N) (Kp X la G.N) (OsK X la G.w) _).symm]

theorem one_le_ord_sum (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (ζ : PtsG G la) [IsDVRAt ζ]
    (h : IsUnif (OsK X la G.w) (unifO X la G.N)) (s : Finset (Fin G.N)) (f : Fin G.N → OsK X la G.w)
    (hf : ∀ k, 1 ≤ ord (unifO X la G.N) ζ (f k)) : 1 ≤ ord (unifO X la G.N) ζ (∑ k ∈ s, f k) := by
  classical
  refine Finset.induction_on s (by rw [Finset.sum_empty, ord_zero ζ h]; exact le_top) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha]
  exact (le_min (hf a) ih).trans (ord_add ζ h _ _)

theorem column_holds : Column := by
  intro D B P j X ka wL wF G la Q S CRm T c hOk hw ζ
  have hC := hOk.2.1
  have hT := hOk.2.2.1
  have h := isUnif_of_curve Q hC
  have := isDVRAt_of_curve Q hC ζ
  refine ⟨fun jj => ord_wfr_nonneg G la Q S hT hw ζ jj, ?_⟩
  by_contra hne
  push Not at hne
  have hall : ∀ k, 1 ≤ ord (unifO X la G.N) ζ (algebraMap (Op X la G.N) (OsK X la G.w) (Tv X la G.N (0, k)) *
      toOsK X la G.w (wfr G la k)) := by
    intro k
    rw [ord_mul ζ h]
    have h0 : 0 ≤ ord (unifO X la G.N) ζ (algebraMap (Op X la G.N) (OsK X la G.w) (Tv X la G.N (0, k))) :=
      ord_nonneg ζ h (Subalgebra.algebraMap_mem _ _)
    have h1 := one_le_of_nonneg_of_ne (ord_wfr_nonneg G la Q S hT hw ζ k) (hne k)
    simpa using add_le_add h0 h1
  have h2 := one_le_ord_sum G la ζ h Finset.univ _ hall
  rw [← one_eq_sum_toOsK, ord_one ζ h] at h2
  exact absurd (WithTop.coe_le_coe.1 (show ((1 : ℤ) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ) from h2)) (by norm_num)

end PoleLengthBounds
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.EqZeroOfOrdTop
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

section Ord

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A : Type*} [CommRing A] [Algebra O A] {ϖ : O}

theorem ord_prod_eq_zero (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) {ι : Type*} (s : Finset ι) (f : ι → A)
    (hf : ∀ i ∈ s, ord ϖ ζ (f i) = 0) : ord ϖ ζ (∏ i ∈ s, f i) = 0 := by
  refine Finset.prod_induction f (fun x => ord ϖ ζ x = 0) (fun a b ha hb => ?_) (ord_one ζ h) hf
  rw [ord_mul ζ h, ha, hb, add_zero]

theorem eq_zero_of_ord_top [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) {x : A} (hx : ∀ ζ : Pts O A, ord ϖ ζ x = ⊤) : x = 0 := by
  obtain ⟨n, hn⟩ := h.denom x
  have h0 : (⟨ϖ ^ n • x, hn⟩ : ↥(As O A)) = 0 := by
    refine eq_zero_of_localization _ fun J hJ => ?_
    have h1 := hx ⟨J, hJ⟩
    rw [ord_eq _ h hn, ordAt, WithTop.add_eq_top] at h1
    rcases h1 with h1 | h1
    · rw [ENat.map_eq_top_iff] at h1
      exact (vL_eq_top_iff (ζ := (⟨J, hJ⟩ : Pts O A)) _).1 h1
    · exact absurd h1 (WithTop.coe_ne_top)
  have h2 : ϖ ^ n • x = 0 := congrArg Subtype.val h0
  rw [Algebra.smul_def, map_pow] at h2
  exact ((h.isUnit.pow n).mul_right_eq_zero).1 h2

end Ord

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem ord_uC_eq_zero {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) (hC : Q.InCurve)
    (ζ : PtsG G la) (jj : Fin G.N) (α : Fin (WeightFamilies.dimY D j) → ℕ)
    (h0 : ord (unifO X la G.N) ζ (toOsK X la G.w (wfr G la jj)) = 0) :
    ord (unifO X la G.N) ζ (uC G la jj α) = 0 := by
  have := isDVRAt_of_curve Q hC ζ
  have hU := isUnif_of_curve Q hC
  unfold uC
  refine ord_prod_eq_zero ζ hU _ _ fun i _ => ?_
  rw [ord_pow ζ hU, h0, smul_zero]

theorem uBall_of_column (hCol : Column) : UBall := by
  unfold UBall
  intro D B P j X ka wL wF G la Q S CRm T c hOk hw α b hb
  have hC : Q.InCurve := hOk.2.1
  have hU := isUnif_of_curve Q hC
  have : ∀ ζ : PtsG G la, IsDVRAt ζ := fun ζ => isDVRAt_of_curve Q hC ζ
  unfold LocalPointData.A0 at hb ⊢
  rw [mem_ballO_iff Q.c hU hC.2.2]
  intro ζ
  obtain ⟨jj, hjj⟩ := (hCol G la Q S CRm T c hOk hw ζ).2
  have h1 := (mem_ballO_iff Q.c hU hC.2.2 _).1 (hb jj) ζ
  rw [ordV_smul Q.c ζ hU hC.2.2, ord_uC_eq_zero Q hC ζ jj α hjj, zero_add] at h1
  exact h1

end PoleLengthBounds
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.HasseOpSmul
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem sum_snd_le {D : D7} {j N : ℕ} {β : Idx D j N →₀ ℕ} {q : (Idx D j N →₀ ℕ) × (Idx D j N →₀ ℕ)}
    (hq : q ∈ Finset.HasAntidiagonal.antidiagonal β) :
    (q.2.sum fun _ n => n) ≤ (β.sum fun _ n => n) := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
  rw [← hq, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  exact Nat.le_add_left _ _

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {wL wF : WeightFamilies.Wt D j}
  {la : HeightOneSpectrum (𝓞 B.KO)} {N : ℕ} {w : Fin N → B.Cusp j wL}

theorem hasse_Op_smul (o : Op X la N) (x : ↥(HK X la w wF)) (β : Idx D j N →₀ ℕ) :
    hasse X la w β (((@algebraMap (Op X la N) (Kp X la N) _ _ _ o • x : ↥(HK X la w wF))) : Lw X la w) =
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal β,
        @algebraMap (Op X la N) (Kp X la N) _ _ _ (hasseOp X la N q.1 o) • hasse X la w q.2 (x : Lw X la w) := by
  have e1 : ((@algebraMap (Op X la N) (Kp X la N) _ _ _ o • x : ↥(HK X la w wF)) : Lw X la w) =
      algebraMap (Rp X la N) (Lw X la w) (algebraMap (Op X la N) (Rp X la N) o) * (x : Lw X la w) := by
    rw [Submodule.coe_smul_of_tower, Algebra.smul_def,
      IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w),
      ← IsScalarTower.algebraMap_apply (Op X la N) (Kp X la N) (Rp X la N)]
  rw [e1]
  refine (hasse_mul X la w β _ _).trans (Finset.sum_congr rfl fun q _ => ?_)
  rw [Algebra.smul_def]
  congr 1
  rw [IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lc X la w),
    ← IsScalarTower.algebraMap_apply (Op X la N) (Kp X la N) (Rp X la N)]
  exact hasse_algebraMap_Op X la w q.1 o

theorem aaRep_holds : AARep := by
  unfold AARep
  intro D B P j X ka wL wF G la Q S CRm T c hOk hw x hx
  have hC : Q.InCurve := hOk.2.1
  have hU := isUnif_of_curve Q hC
  have : ∀ ζ : PtsG G la, IsDVRAt ζ := fun ζ => isDVRAt_of_curve Q hC ζ
  suffices key : ∃ x' : ↥(HK X la G.w wF),
      (∃ hx' : ∀ β : Idx D j G.N →₀ ℕ, (β.sum fun _ n => n) ≤ a0 D j T - 1 →
          hasse X la G.w β (x' : Lw X la G.w) ∈ HK X la G.w wF,
        ∀ β hβ, toA0K X la G.w wF ⟨_, hx' β hβ⟩ ∈ Q.A0) ∧
      toWK X la G.w wF (a0 D j T) x' = x by
    obtain ⟨x', ⟨_, h2⟩, h3⟩ := key
    exact ⟨x', h3, fun β hβ _ => h2 β hβ⟩
  unfold LocalPointData.AA LocalPointData.AAp at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x0, ⟨hx0, hb0⟩, rfl⟩ := hy
    refine ⟨x0, ⟨hx0, fun β hβ => ?_⟩, rfl⟩
    unfold LocalPointData.A0
    rw [mem_ballO_iff Q.c hU hC.2.2]
    intro ζ
    have h := hb0 β hβ ζ
    simpa [LocalPointData.ordA] using h
  | zero =>
    have hz : ∀ β : Idx D j G.N →₀ ℕ,
        hasse X la G.w β ((0 : ↥(HK X la G.w wF)) : Lw X la G.w) = 0 := fun β => by
      exact map_zero (hasse X la G.w β)
    refine ⟨0, ⟨fun β _ => by rw [hz]; exact (HK X la G.w wF).zero_mem, fun β hβ => ?_⟩, map_zero _⟩
    convert Q.A0.zero_mem using 1
    rw [← map_zero (toA0K X la G.w wF)]
    exact congrArg _ (Subtype.ext (hz β))
  | add a b _ _ ha hb =>
    obtain ⟨xa, ⟨ha1, ha2⟩, rfl⟩ := ha
    obtain ⟨xb, ⟨hb1, hb2⟩, rfl⟩ := hb
    have hs : ∀ β : Idx D j G.N →₀ ℕ, hasse X la G.w β ((xa + xb : ↥(HK X la G.w wF)) : Lw X la G.w) =
        hasse X la G.w β (xa : Lw X la G.w) + hasse X la G.w β (xb : Lw X la G.w) := fun β => by
      exact map_add (hasse X la G.w β) _ _
    refine ⟨xa + xb, ⟨fun β hβ => by rw [hs]; exact add_mem (ha1 β hβ) (hb1 β hβ), fun β hβ => ?_⟩, map_add _ _ _⟩
    convert Q.A0.add_mem (ha2 β hβ) (hb2 β hβ) using 1
    rw [← map_add (f := _)]
    exact congrArg _ (Subtype.ext (hs β))
  | smul o y _ ih =>
    classical
    obtain ⟨x0, ⟨h1, h2⟩, rfl⟩ := ih
    let g : (Idx D j G.N →₀ ℕ) × (Idx D j G.N →₀ ℕ) → ↥(HK X la G.w wF) := fun q =>
      if h : hasse X la G.w q.2 (x0 : Lw X la G.w) ∈ HK X la G.w wF then ⟨_, h⟩ else 0
    have hg' : ∀ q : (Idx D j G.N →₀ ℕ) × (Idx D j G.N →₀ ℕ), ∀ hq : (q.2.sum fun _ n => n) ≤ a0 D j T - 1,
        g q = ⟨_, h1 q.2 hq⟩ := fun q hq => dif_pos (h1 q.2 hq)
    let F : (Idx D j G.N →₀ ℕ) → ↥(HK X la G.w wF) := fun β =>
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal β, @algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ (hasseOp X la G.N q.1 o) • g q
    have he : ∀ β : Idx D j G.N →₀ ℕ, (β.sum fun _ n => n) ≤ a0 D j T - 1 →
        hasse X la G.w β ((@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ o • x0 : ↥(HK X la G.w wF)) : Lw X la G.w) =
          ((F β : ↥(HK X la G.w wF)) : Lw X la G.w) := by
      intro β hβ
      rw [hasse_Op_smul, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [Submodule.coe_smul_of_tower, hg' q ((sum_snd_le hq).trans hβ)]
      rfl
    refine ⟨@algebraMap (Op X la G.N) (Kp X la G.N) _ _ _ o • x0, ⟨fun β hβ => ?_, fun β hβ => ?_⟩, ?_⟩
    · rw [he β hβ]
      exact Submodule.coe_mem _
    · have hm : toA0K X la G.w wF (F β) ∈ Q.A0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Q.A0.sum_mem fun q hq => ?_
        rw [LinearMap.map_smul_of_tower, algebraMap_smul, hg' q ((sum_snd_le hq).trans hβ)]
        exact Q.A0.smul_mem _ (h2 q.2 ((sum_snd_le hq).trans hβ))
      convert hm using 1
      exact congrArg _ (Subtype.ext (he β hβ))
    · rw [LinearMap.map_smul_of_tower]
      rfl

end PoleLengthBounds
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.HasseVan
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem sumN_eq {σ : Type*} (β : σ →₀ ℕ) : (β.sum fun _ n => n) = Finsupp.degree β := rfl

theorem mem_Jid_smul_top_of_JHfr {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (u : WeightFamilies.Wt D j)
    {b : ℕ} (hb : 1 ≤ b) (y : ↥(HK X la w u)) (hy : (y : Lw X la w) ∈ JHfr X la w u b) :
    y ∈ Jid X la w • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)) := by
  have h1 : y ∈ Jid X la w ^ b • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)) :=
    (mem_Jid_pow_smul_top X la w).2 ((mem_JHfr X la w).1 hy)
  exact Submodule.smul_mono_left (Ideal.pow_le_self (by omega)) h1

theorem hasseVan_holds : HasseVan := by
  intro D B P j X ka wL wF G la a x hx β hβ h
  rw [reduction_eq_zero_iff_mem_ideal_smul]
  have hx' : (x : Lw X la G.w) ∈ JHfr X la G.w wF a :=
    (mem_JHfr X la G.w).2 ((mem_Jid_pow_smul_top X la G.w).1 hx)
  have h2 := hasse_jid_power X la G.w wF β a _ hx'
  exact mem_Jid_smul_top_of_JHfr X la G.w wF (b := a - β.sum fun _ n => n) (by omega) ⟨_, h⟩ h2

end PoleLengthBounds
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorRep
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

section Gen

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {d : ℕ} (g : Fin d → R)

def monSpan (k : ℕ) : Submodule R M where
  carrier := {x | ∃ cf : (Fin d → ℕ) → M, x = ∑ α ∈ Finset.Nat.antidiagonalTuple d k, (∏ i, g i ^ α i) • cf α}
  add_mem' := by
    rintro x y ⟨c1, rfl⟩ ⟨c2, rfl⟩
    exact ⟨c1 + c2, by simp [smul_add, Finset.sum_add_distrib]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro r x ⟨c1, rfl⟩
    exact ⟨r • c1, by simp [Finset.smul_sum, smul_comm r]⟩

theorem single_mem_monSpan {k : ℕ} {α : Fin d → ℕ} (hα : α ∈ Finset.Nat.antidiagonalTuple d k) (m : M) :
    (∏ i, g i ^ α i) • m ∈ monSpan (M := M) g k := by
  refine ⟨fun β => if β = α then m else 0, ?_⟩
  rw [Finset.sum_eq_single α]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd hα h

theorem prod_pow_add_single (α : Fin d → ℕ) (i : Fin d) :
    (∏ l, g l ^ (α + Pi.single i 1 : Fin d → ℕ) l) = g i * ∏ l, g l ^ α l := by
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  rw [mul_comm]
  congr 1
  rw [Finset.prod_eq_single i]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem pow_smul_top_le_monSpan (k : ℕ) :
    (Ideal.span (Set.range g)) ^ k • (⊤ : Submodule R M) ≤ monSpan (M := M) g k := by
  induction k with
  | zero =>
    intro x _
    refine ⟨fun _ => x, ?_⟩
    simp [Finset.Nat.antidiagonalTuple_zero_right]
  | succ k ih =>
    rw [pow_succ', Submodule.mul_smul, Submodule.smul_le]
    intro r hr n hn
    obtain ⟨cf, rfl⟩ := ih hn
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hr
    rw [Finset.sum_smul]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun β hβ => ?_
    have hβ' : β + Pi.single i 1 ∈ Finset.Nat.antidiagonalTuple d (k + 1) := by
      rw [Finset.Nat.mem_antidiagonalTuple] at hβ ⊢
      simp [Finset.sum_add_distrib, hβ]
    have e : (a i • g i) • ((∏ l, g l ^ β l) • cf β) =
        (∏ l, g l ^ (β + Pi.single i 1 : Fin d → ℕ) l) • (a i • cf β) := by
      rw [smul_smul, smul_smul, prod_pow_add_single g β i, smul_eq_mul]
      congr 1
      ring
    rw [e]
    exact single_mem_monSpan g hβ' _

end Gen

theorem taylorRep_holds : TaylorRep := by
  intro D B P j X ka wL wF G la k x hx
  obtain ⟨cf, hcf⟩ := pow_smul_top_le_monSpan (M := ↥(HK X la G.w wF))
    (fun i : Fin (WeightFamilies.dimY D j) => sfr X la G.w i.succ) k hx
  refine ⟨cf, ?_⟩
  have : x - ∑ α ∈ mon D j k, ym G la α • cf α = 0 := by
    rw [sub_eq_zero]; exact hcf
  rw [this]
  exact Submodule.zero_mem _

end PoleLengthBounds
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorSpanGenerators
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j}

theorem prod_sec_pow_mul_mem {la : HeightOneSpectrum (𝓞 B.KO)} {N : ℕ} {wL : WeightFamilies.Wt D j}
    (w : Fin N → B.Cusp j wL) (u : WeightFamilies.Wt D j) (α : Fin (WeightFamilies.dimY D j) → ℕ) (s : Finset (Fin (WeightFamilies.dimY D j)))
    {n : ℕ} {v : Rp X la N} (hv : v ∈ Vw X la N (addL u wL n)) :
    (∏ i ∈ s, sec X la w i.succ ^ α i) * v ∈ Vw X la N (addL u wL (n + ∑ i ∈ s, α i)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using hv
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_assoc]
    have := sec_pow_mul_mem X la w a.succ u _ (α a) ih
    rwa [show n + ∑ i ∈ s, α i + α a = n + (α a + ∑ i ∈ s, α i) by ring] at this

theorem taylorSpanGenerators : TaylorSpanGenerators := by
  intro D B P j X ka wL wF G la T k hk α hα i
  have hs : ∑ i, α i = k := Finset.Nat.mem_antidiagonalTuple.1 hα
  have hkT : ∑ i, α i ≤ T := by
    have : a0 D j T ≤ T := Nat.sub_le _ _
    omega
  have h0 : emb X la G.N (X.inc wF (G.th' i)) ∈ Vw X la G.N (addL wF wL 0) := by
    rw [addL_zero]; exact emb_mem_Vw X la G.N wF _
  have h1 := sec_pow_mul_mem X la G.w 0 wF 0 (T - ∑ i, α i) h0
  have h2 := prod_sec_pow_mul_mem G.w wF α Finset.univ h1
  rw [show 0 + (T - ∑ i, α i) + ∑ i, α i = T by omega] at h2
  have hf : secPow X la G.w α * sec X la G.w 0 ^ (T - ∑ i, α i) * emb X la G.N (X.inc wF (G.th' i)) ∈
      Vw X la G.N (addL wF wL T) := by
    rw [mul_assoc]; exact h2
  refine ⟨toHK X la G.w wF T ⟨_, hf⟩,
    toHK0 X la G.w wF ⟨emb X la G.N (X.inc wF (G.th' i)), emb_mem_Vw X la G.N wF (G.th' i)⟩, ?_, ?_, rfl⟩
  · exact Submodule.subset_span ⟨⟨_, hf⟩, ⟨α, i, by omega, rfl⟩, rfl⟩
  · apply Subtype.ext
    have e1 : ((ym G la α : ↥(Frac0 X la G.w)) : Lw X la G.w) = frac X la G.w (∑ i, α i) (secPow X la G.w α) :=
      coe_prod_sfr X la G.w α
    rw [Submodule.coe_smul, Subalgebra.smul_def, smul_eq_mul, e1, coe_toHK, coe_toHK0, ← frac_zero, frac_mul,
      add_zero]
    have e2 := frac_pow_mul X la G.w (∑ i, α i) (T - ∑ i, α i)
      (secPow X la G.w α * emb X la G.N (X.inc wF (G.th' i)))
    rw [show ∑ i, α i + (T - ∑ i, α i) = T by omega] at e2
    rw [← e2]
    congr 1
    show _ = _
    ring

end PoleLengthBounds
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorSpanLeBound
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem taylorSpanLeBound : TaylorSpanLeBound := by
  intro D B P j X ka wL wF G la Q S CRm T c hOk hw hth
  let G' : GlobalFamilyData X (addL wF wL T) wL wF :=
    { N := G.N, w := G.w, del := G.del, th' := G.th', rz := G.rz, alz := G.alz, th0 := G.th0,
      zc := fun _ => 0, rq := 0, th := Fin.elim0, iet := G.iet, et := G.et, mx := G.mx }
  let Q' : LocalPointData G' la := ⟨Q.y, Q.g0, Q.c⟩
  exact reduced_generators_le (G := G') Q' S hOk.2.1 hOk.2.2.1 hw hth

end PoleLengthBounds
end
end

