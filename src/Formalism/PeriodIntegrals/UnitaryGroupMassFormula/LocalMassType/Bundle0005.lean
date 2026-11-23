module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.IsTopRingTens
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.IdxGrp
section
noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory NumberField
  IsDedekindDomain
open scoped TensorProduct Classical

def frU {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {n r : ℕ} (P : Frame E n r) (u : UIdx r → Fv F v ⊗[F] E) :
    TupV (E := E) v n (r + 1) :=
  fun b => ∑ a, uMat v u a b • ratTup (Fv F v) (F0 P) a

def Cong {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Set (Fin n → E)) {r : ℕ} (g : ℕ) (P : Frame E n r) (x : HA (Fv F v) σ J)
    (u : UIdx r → Fv F v ⊗[F] E) : Prop :=
  ∀ b, ∃ w ∈ latLoc (E := E) v Λ,
    locF v (x • ratTup (Fv F v) (F0 P)) b - locF v (frU v P u) b = sc (E := E) v (g : Fv F v) • w

section Grp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}
  {Λ : Set (Fin n → E)}

theorem smul_tup (k : HA (Fv F v) σ J) {a : ℕ} (X : Fin a → Fin n → Fv F v ⊗[F] E) (b : Fin a) :
    (k • X) b = lin (Fv F v) σ J k (X b) := rfl

theorem kv_lat {k : HA (Fv F v) σ J} (hk : k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    {w : Fin n → Fv F v ⊗[F] E} (hw : w ∈ latLoc (E := E) v Λ) :
    lin (Fv F v) σ J k w ∈ latLoc (E := E) v Λ := (hk w).1 hw

theorem kv_mul {a b : HA (Fv F v) σ J} (ha : a ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    (hb : b ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) : a * b ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v :=
  Subgroup.mul_mem (Kloc (E := E) v Λ) ha hb

theorem kv_inv {a : HA (Fv F v) σ J} (ha : a ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) :
    a⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v :=
  Subgroup.inv_mem (Kloc (E := E) v Λ) ha

theorem kv_one : (1 : HA (Fv F v) σ J) ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v :=
  Subgroup.one_mem (Kloc (E := E) v Λ)

theorem locF_act (k : HA (Fv F v) σ J) {r : ℕ} (Y : TupV (E := E) v n (r + 1)) (b : Fin (r + 1)) :
    locF v (k • Y) b = lin (Fv F v) σ J k (locF v Y b) := by
  show sc (E := E) v (alp v r b) • (k • Y) b = _
  rw [smul_tup, locF, map_smul]

theorem locF_comb {r : ℕ} (M : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E))
    (X : TupV (E := E) v n (r + 1)) (b : Fin (r + 1)) :
    locF v (fun b => ∑ a, M a b • X a) b =
      ∑ a, (sc (E := E) v ((alp v r a)⁻¹ * alp v r b) * M a b) • locF v X a := by
  simp only [locF, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have h : (alp v r a)⁻¹ * alp v r b * alp v r a = alp v r b := by
    rw [mul_comm (alp v r a)⁻¹, mul_assoc, inv_mul_cancel₀ (alp_ne' v r a), mul_one]
  rw [mul_right_comm, sc_mul', h]

theorem prim_div {r : ℕ} {Y : TupV (E := E) v n (r + 1)} (hP : IsPrim v Λ Y)
    (c : Fin (r + 1) → Fv F v ⊗[F] E) {t : Fv F v} (ht : t ≠ 0) {y : Fin n → Fv F v ⊗[F] E}
    (hy : y ∈ latLoc (E := E) v Λ) (h : ∑ a, c a • Y a = sc (E := E) v t • y) (a : Fin (r + 1)) :
    sc (E := E) v t⁻¹ * c a ∈ OEv (E := E) v := by
  apply hP.2 (fun a => sc (E := E) v t⁻¹ * c a) _ a
  have : ∑ a, (sc (E := E) v t⁻¹ * c a) • Y a = sc (E := E) v t⁻¹ • ∑ a, c a • Y a := by
    rw [Finset.smul_sum]; simp only [smul_smul]
  rw [this, h, sc_smul_sc, inv_mul_cancel₀ ht, sc_one', one_smul]
  exact hy

theorem hR_smul (x w : Fin n → Fv F v ⊗[F] E) (c : Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • w) = c * hR (Fv F v) σ J x w := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem sd_smul (hSD : IsSDLoc σ J v Λ) {c : Fv F v ⊗[F] E} (hc : c ∈ OEv (E := E) v)
    {w : Fin n → Fv F v ⊗[F] E} (hw : w ∈ latLoc (E := E) v Λ) : c • w ∈ latLoc (E := E) v Λ :=
  (hSD (c • w)).2 fun x hx => by rw [hR_smul]; exact oev_mul v hc ((hSD w).1 hw x hx)

theorem lat_comb (hSD : IsSDLoc σ J v Λ) {r : ℕ} {Y : Fin (r + 1) → Fin n → Fv F v ⊗[F] E}
    (hY : ∀ a, Y a ∈ latLoc (E := E) v Λ) {c : Fin (r + 1) → Fv F v ⊗[F] E}
    (hc : ∀ a, c a ∈ OEv (E := E) v) : ∑ a, c a • Y a ∈ latLoc (E := E) v Λ :=
  Submodule.sum_mem _ fun a _ => sd_smul hSD (hc a) (hY a)

theorem uMat_sub {r : ℕ} (u u' : UIdx r → Fv F v ⊗[F] E) (a b : Fin (r + 1)) :
    uMat v u' a b - uMat v u a b =
      if h : a < b then u' ⟨(a, b), h⟩ - u ⟨(a, b), h⟩ else 0 := by
  by_cases h1 : a = b
  · subst h1; simp [uMat]
  · by_cases h2 : a < b <;> simp [uMat, h1, h2]

theorem locF_frU_sub {r : ℕ} (P : Frame E n r) (u u' : UIdx r → Fv F v ⊗[F] E) (b : Fin (r + 1)) :
    locF v (frU v P u') b - locF v (frU v P u) b =
      ∑ a, (sc (E := E) v ((alp v r a)⁻¹ * alp v r b) * (uMat v u' a b - uMat v u a b)) •
        locF v (ratTup (Fv F v) (F0 P)) a := by
  unfold frU
  rw [locF_comb, locF_comb, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← sub_smul, mul_sub]

theorem cong_lat_iff (hSD : IsSDLoc σ J v Λ) {r : ℕ} {P : Frame E n r}
    (hP : IsPrim v Λ (locF v (ratTup (Fv F v) (F0 P)))) {g : ℕ} (hg : (g : Fv F v) ≠ 0)
    (u u' : UIdx r → Fv F v ⊗[F] E) :
    (∀ b, ∃ z ∈ latLoc (E := E) v Λ,
      locF v (frU v P u') b - locF v (frU v P u) b = sc (E := E) v (g : Fv F v) • z) ↔
      -u + u' ∈ UOg (E := E) v g r := by
  constructor
  · rintro h ⟨⟨a, b⟩, hab⟩
    obtain ⟨z, hz, hzeq⟩ := h b
    rw [locF_frU_sub] at hzeq
    have := prim_div hP _ hg hz hzeq a
    rw [uMat_sub, dite_eq_left hab] at this
    dsimp only
    convert this using 1
    rw [Pi.add_apply, Pi.neg_apply, neg_add_eq_sub, ← mul_assoc, sc_mul']
    congr 1; congr 1; ring
  · intro h b
    refine ⟨∑ a, (sc (E := E) v (g : Fv F v)⁻¹ * (sc (E := E) v ((alp v r a)⁻¹ * alp v r b) *
      (uMat v u' a b - uMat v u a b))) • locF v (ratTup (Fv F v) (F0 P)) a,
      lat_comb hSD hP.1 ?_, ?_⟩
    · intro a
      rw [uMat_sub]
      split_ifs with hab
      · have := h ⟨(a, b), hab⟩
        simp only [Pi.add_apply, Pi.neg_apply, neg_add_eq_sub] at this
        convert this using 1
        rw [← mul_assoc, sc_mul']
        congr 1; congr 1; ring
      · rw [mul_zero, mul_zero]; exact oev_zero v
    · rw [locF_frU_sub, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_smul, ← mul_assoc, sc_mul', mul_inv_cancel₀ hg, sc_one', one_mul]

theorem cong_iff (hSD : IsSDLoc σ J v Λ) {r : ℕ} {P : Frame E n r}
    (hP : IsPrim v Λ (locF v (ratTup (Fv F v) (F0 P)))) {g : ℕ} (hg : (g : Fv F v) ≠ 0)
    {x y : HA (Fv F v) σ J} (hx : x ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    (hy : y ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) {u u' : UIdx r → Fv F v ⊗[F] E}
    (hcx : Cong σ J v Λ g P x u) (hcy : Cong σ J v Λ g P y u') :
    x⁻¹ * y ∈ K1 σ J v Λ g P ↔ -u + u' ∈ UOg (E := E) v g r := by
  rw [← cong_lat_iff hSD hP hg u u']
  have key : ∀ b, locF v ((x⁻¹ * y) • ratTup (Fv F v) (F0 P)) b - locF v (ratTup (Fv F v) (F0 P)) b =
      lin (Fv F v) σ J x⁻¹ (locF v (y • ratTup (Fv F v) (F0 P)) b -
        locF v (x • ratTup (Fv F v) (F0 P)) b) := by
    intro b
    rw [map_sub, locF_act, locF_act, locF_act, lin_mul, lin_inv_lin]
  constructor
  · rintro ⟨-, hk⟩ b
    obtain ⟨z, hz, hzeq⟩ := hk b
    obtain ⟨wx, hwx, hwxe⟩ := hcx b
    obtain ⟨wy, hwy, hwye⟩ := hcy b
    refine ⟨lin (Fv F v) σ J x z - wy + wx,
      Submodule.add_mem _ (Submodule.sub_mem _ (kv_lat hx hz) hwy) hwx, ?_⟩
    have e1 : locF v (y • ratTup (Fv F v) (F0 P)) b - locF v (x • ratTup (Fv F v) (F0 P)) b =
        sc (E := E) v (g : Fv F v) • lin (Fv F v) σ J x z := by
      rw [key] at hzeq
      have := congrArg (lin (Fv F v) σ J x) hzeq
      rwa [← lin_mul, mul_inv_cancel, lin_one, map_smul] at this
    rw [smul_add, smul_sub, ← e1, ← hwye, ← hwxe]
    abel
  · intro h
    refine ⟨kv_mul (kv_inv hx) hy, fun b => ?_⟩
    obtain ⟨z, hz, hzeq⟩ := h b
    obtain ⟨wx, hwx, hwxe⟩ := hcx b
    obtain ⟨wy, hwy, hwye⟩ := hcy b
    refine ⟨lin (Fv F v) σ J x⁻¹ (z + wy - wx),
      kv_lat (kv_inv hx) (Submodule.sub_mem _ (Submodule.add_mem _ hz hwy) hwx), ?_⟩
    rw [key, ← map_smul]
    congr 1
    rw [smul_sub, smul_add, ← hzeq, ← hwye, ← hwxe]
    abel

end Grp

end PI.LocMassTypW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.OmMeas
section
noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory NumberField
  IsDedekindDomain
open scoped TensorProduct

def OmHyp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ) (P P' : Frame E n r) (Λ : Set (Fin n → E))
    (T T' : F) (κ : HA (Fv F v) σ J) (μG : Measure (HA (Fv F v) σ J))
    (μS0 : Measure (S0 (Fv F v) σ J P)) (μS0' : Measure (S0 (Fv F v) σ J P')) : Prop :=
  StdHyp σ J ψ ∧ P.IsStd σ J T ∧ P'.IsStd σ J T' ∧ IsSDLoc σ J v Λ ∧ UnramAt (E := E) v ∧
    g.Prime ∧ (g : 𝓞 F) ∈ v.asIdeal ∧ Ideal.absNorm v.asIdeal = g ∧ etaV (E := E) v = 1 ∧
    κ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v ∧
    (∀ a, ∃ y ∈ latLoc (E := E) v Λ,
      locF v (κ • ratTup (Fv F v) (F0 P')) a - locF v (ratTup (Fv F v) (F0 P)) a =
        sc (E := E) v (g : Fv F v) • y) ∧
    μG.IsHaarMeasure ∧
    μS0.IsHaarMeasure ∧ IsCompatLoc σ J v (F0 P) μG μS0 (omAt σ J ψ v (TFl σ J v P)) ∧
    μS0'.IsHaarMeasure ∧ IsCompatLoc σ J v (F0 P') μG μS0' (omAt σ J ψ v (TFl σ J v P')) ∧
    IsPrim v Λ (locF v (ratTup (Fv F v) (F0 P))) ∧ IsPrim v Λ (locF v (ratTup (Fv F v) (F0 P'))) ∧
    LocMassOrdW.IsLatLoc v Λ ∧ (μS0 (stabilizerCompact σ J v Λ P)).toReal ≠ 0 ∧ (μS0' (stabilizerCompact σ J v Λ P')).toReal ≠ 0

def OmMeas : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ) (P P' : Frame E n r) (Λ : Set (Fin n → E))
    (T T' : F) (κ : HA (Fv F v) σ J) (μG : Measure (HA (Fv F v) σ J))
    (μS0 : Measure (S0 (Fv F v) σ J P)) (μS0' : Measure (S0 (Fv F v) σ J P')),
    OmHyp σ J ψ v g P P' Λ T T' κ μG μS0 μS0' →
    MeasurableSet (OmTyp v Λ g r) ∧ MeasurableSet (Formalism.L2.SG.TypedSets.Kv σ J Λ v) ∧
      MeasurableSet (K1 σ J v Λ g P) ∧
      MeasurableSet ((fun c : HA (Fv F v) σ J => c • ratTup (F := F) (Fv F v) (F0 P)) ''
        Formalism.L2.SG.TypedSets.Kv σ J Λ v) ∧
      ∀ k : HA (Fv F v) σ J, MeasurableSet ((fun c : HA (Fv F v) σ J => c • ratTup (F := F) (Fv F v) (F0 P')) ''
        {c | k⁻¹ * c * κ⁻¹ ∈ K1 σ J v Λ g P})

theorem weil_gen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) {a : ℕ}
    (X0 : Fin a → Fin n → E) (μG : Measure (HA (Fv F v) σ J))
    (μ' : Measure (stabT (Fv F v) σ J X0)) (ν : Measure (TupV (E := E) v n a))
    (hc : IsCompatLoc σ J v X0 μG μ' ν) (C : Set (HA (Fv F v) σ J)) (hCm : MeasurableSet C)
    (D : Set (stabT (Fv F v) σ J X0)) (hDm : MeasurableSet D)
    (hCD : ∀ c ∈ C, ∀ h : stabT (Fv F v) σ J X0, c * (h : HA (Fv F v) σ J) ∈ C ↔ h ∈ D)
    (hAm : MeasurableSet ((fun c : HA (Fv F v) σ J => c • ratTup (F := F) (Fv F v) X0) '' C)) :
    ν ((fun c : HA (Fv F v) σ J => c • ratTup (F := F) (Fv F v) X0) '' C) * μ' D = μG C := by
  classical
  set X0r := ratTup (F := F) (Fv F v) X0 with hX0r
  set A := (fun c : HA (Fv F v) σ J => c • X0r) '' C with hAdef
  let s : TupV (E := E) v n a → HA (Fv F v) σ J := fun Y =>
    if hY : Y ∈ A then hY.choose else if h' : ∃ g : HA (Fv F v) σ J, g • X0r = Y then h'.choose else 1
  have hs : ∀ Y, (∃ g : HA (Fv F v) σ J, g • X0r = Y) → s Y • X0r = Y := by
    intro Y hY
    by_cases hA : Y ∈ A
    · simp only [s, dif_pos hA]; exact hA.choose_spec.2
    · simp only [s, dif_neg hA, dif_pos hY]; exact hY.choose_spec
  have hf : Measurable (C.indicator (1 : HA (Fv F v) σ J → ENNReal)) := measurable_one.indicator hCm
  have key := hc.2 _ hf s hs
  have hL : ∫⁻ g, C.indicator (1 : HA (Fv F v) σ J → ENNReal) g ∂μG = μG C := lintegral_indicator_one hCm
  have hpt : ∀ Y, (∃ g : HA (Fv F v) σ J, g • X0r = Y) →
      ∫⁻ h', C.indicator (1 : HA (Fv F v) σ J → ENNReal) (s Y * (h' : HA (Fv F v) σ J)) ∂μ' =
        A.indicator (fun _ => μ' D) Y := by
    intro Y hY
    by_cases hA : Y ∈ A
    · rw [Set.indicator_of_mem hA]
      have hk : hA.choose ∈ C := hA.choose_spec.1
      have hsY : s Y = hA.choose := by simp only [s, dif_pos hA]
      rw [← lintegral_indicator_one hDm]
      congr 1
      funext h'
      rw [hsY]
      by_cases hh : h' ∈ D
      · rw [Set.indicator_of_mem hh, Set.indicator_of_mem ((hCD _ hk h').2 hh)]; rfl
      · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem (fun hm => hh ((hCD _ hk h').1 hm))]
    · rw [Set.indicator_of_notMem hA]
      have hz : ∀ h' : stabT (Fv F v) σ J X0,
          C.indicator (1 : HA (Fv F v) σ J → ENNReal) (s Y * (h' : HA (Fv F v) σ J)) = 0 := by
        intro h'
        rw [Set.indicator_of_notMem]
        intro hmem
        apply hA
        refine ⟨s Y * (h' : HA (Fv F v) σ J), hmem, ?_⟩
        have hst : (h' : HA (Fv F v) σ J) • X0r = X0r := h'.2
        show (s Y * (h' : HA (Fv F v) σ J)) • X0r = Y
        rw [mul_smul, hst, hs Y hY]
      simp [hz]
  have hae : ∀ᵐ Y ∂ν, ∃ g : HA (Fv F v) σ J, g • X0r = Y := ae_iff.mpr hc.1
  have hR' : ∫⁻ Y, ∫⁻ h', C.indicator (1 : HA (Fv F v) σ J → ENNReal) (s Y * (h' : HA (Fv F v) σ J)) ∂μ' ∂ν =
      ∫⁻ Y, A.indicator (fun _ => μ' D) Y ∂ν := by
    apply lintegral_congr_ae
    filter_upwards [hae] with Y hY
    exact hpt Y hY
  rw [hL, hR', lintegral_indicator_const hAm] at key
  rw [key, mul_comm]

theorem stepOm_ofK (hW : StepW) (hM : OmMeas) (hRK : RightK) (hO : LocMassOrdW.OmSF) :
    StepOm := by
  intro F E _ _ _ _ _ σ n J ψ v r g P P' Λ T T' κ μG μS0 μS0' hStd hP hP' hSD hUn hg hgv hN hEta hκ
    hκc hμG hμS0 hC hμS0' hC' hPr hPr' hL ha ha'
  have hH : OmHyp σ J ψ v g P P' Λ T T' κ μG μS0 μS0' :=
    ⟨hStd, hP, hP', hSD, hUn, hg, hgv, hN, hEta, hκ, hκc, hμG, hμS0, hC, hμS0', hC', hPr, hPr', hL, ha, ha'⟩
  obtain ⟨hOmm, hKm, hK1m, hAm, hBm⟩ := hM σ J ψ v g P P' Λ T T' κ μG μS0 μS0' hH
  have := hO σ J ψ v hStd (TFl σ J v P')
  set K := Formalism.L2.SG.TypedSets.Kv σ J Λ v with hKdef
  set K1s := K1 σ J v Λ g P with hK1def
  set X0r := ratTup (F := F) (Fv F v) (F0 P) with hX0r
  set X0r' := ratTup (F := F) (Fv F v) (F0 P') with hX0r'
  set ν := omAt σ J ψ v (TFl σ J v P) with hν
  set ν' := omAt σ J ψ v (TFl σ J v P') with hν'
  set a := μS0 (stabilizerCompact σ J v Λ P) with hadef
  set a' := μS0' (stabilizerCompact σ J v Λ P') with ha'def
  have hcg : CongL (Λ := Λ) g X0r (κ • X0r') := hκc
  have hS0Km : MeasurableSet (stabilizerCompact σ J v Λ P) := measurable_subtype_coe hKm
  have hS0Km' : MeasurableSet (stabilizerCompact σ J v Λ P') := measurable_subtype_coe hKm

  have hWK : ν ((fun c : HA (Fv F v) σ J => c • X0r) '' K) * a = μG K := by
    refine weil_gen σ J v (F0 P) μG μS0 ν hC K hKm (stabilizerCompact σ J v Λ P) hS0Km ?_ hAm
    intro c hc h
    show c * (h : HA (Fv F v) σ J) ∈ K ↔ (h : HA (Fv F v) σ J) ∈ K
    constructor
    · intro hm
      have := kv_mul' (kv_inv' hc) hm
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    · exact kv_mul' hc

  have hWC : ∀ k : HA (Fv F v) σ J,
      ν' ((fun c : HA (Fv F v) σ J => c • X0r') '' {c | k⁻¹ * c * κ⁻¹ ∈ K1s}) * a' = μG K1s := by
    intro k
    have hCm : MeasurableSet {c : HA (Fv F v) σ J | k⁻¹ * c * κ⁻¹ ∈ K1s} :=
      hK1m.preimage ((measurable_const_mul k⁻¹).mul_const κ⁻¹)
    refine (weil_gen σ J v (F0 P') μG μS0' ν' hC' _ hCm (stabilizerCompact σ J v Λ P') hS0Km' ?_ (hBm k)).trans ?_
    swap
    · show μG ((fun c => k⁻¹ * c) ⁻¹' ((fun c => c * κ⁻¹) ⁻¹' K1s)) = μG K1s
      rw [measure_preimage_mul]
      exact hRK σ J ψ v Λ μG hStd hSD hUn hEta hL hμG κ⁻¹ (kv_inv' hκ) K1s hK1m
    · intro c hc h
      show k⁻¹ * (c * (h : HA (Fv F v) σ J)) * κ⁻¹ ∈ K1s ↔ (h : HA (Fv F v) σ J) ∈ K
      rw [show k⁻¹ * (c * (h : HA (Fv F v) σ J)) * κ⁻¹ =
          (k⁻¹ * c * κ⁻¹) * (κ * (h : HA (Fv F v) σ J) * κ⁻¹) by group, congruence_mul_mem_iff hc]
      exact conj_mem_congruence_iff hκ hcg h.2
  have ha0' : a' ≠ 0 ∧ a' ≠ ⊤ := ⟨fun h => ha' (by rw [h]; rfl), fun h => ha' (by rw [h]; rfl)⟩
  have hWC' : ∀ k : HA (Fv F v) σ J,
      ν' ((fun c : HA (Fv F v) σ J => c • X0r') '' {c | k⁻¹ * c * κ⁻¹ ∈ K1s}) = μG K1s / a' := by
    intro k
    rw [ENNReal.eq_div_iff ha0'.1 ha0'.2, mul_comm]
    exact hWC k

  have hae' : ∀ᵐ Y ∂ν', ∃ g2 : HA (Fv F v) σ J, g2 • X0r' = Y := ae_iff.mpr hC'.1
  have hae : ∀ᵐ Y ∂ν, ∃ g1 : HA (Fv F v) σ J, g1 • X0r = Y := ae_iff.mpr hC.1
  have hslice : ∀ x, (∃ g1 : HA (Fv F v) σ J, g1 • X0r = x) →
      ν' (Prod.mk x ⁻¹' OmTyp v Λ g r) =
        ((fun c : HA (Fv F v) σ J => c • X0r) '' K).indicator (fun _ => μG K1s / a') x := by
    intro x ⟨g1, hg1⟩
    by_cases hx : x ∈ (fun c : HA (Fv F v) σ J => c • X0r) '' K
    · rw [Set.indicator_of_mem hx]
      obtain ⟨k, hk, hkx⟩ := hx
      rw [← hWC' k]
      apply measure_congr
      rw [Filter.eventuallyEq_set]
      filter_upwards [hae'] with x' hx'
      obtain ⟨g2, hg2⟩ := hx'
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨_, hp2, hcong⟩
        rw [← hg2] at hp2
        obtain ⟨k', hk', hk'x⟩ := hW σ J ψ v P' Λ T' hStd hP' hSD hUn hEta hPr' hL g2 hp2
        refine ⟨k', ⟨kv_mul' (kv_mul' (kv_inv' hk) hk') (kv_inv' hκ), ?_⟩, hk'x.trans hg2⟩
        have hc1 : CongL (Λ := Λ) g x x' := hcong
        have h1 := congL_smul (kv_inv' hk) hc1
        rw [← hkx, inv_smul_smul] at h1
        have h2 := congL_smul (kv_mul' (kv_mul' (kv_inv' hk) hk') (kv_inv' hκ)) hcg
        rw [show (k⁻¹ * k' * κ⁻¹) • κ • X0r' = k⁻¹ • x' by
          rw [← mul_smul, show k⁻¹ * k' * κ⁻¹ * κ = k⁻¹ * k' by group, mul_smul, hk'x, hg2]] at h2
        exact congL_trans h1 (congL_symm h2)
      · rintro ⟨c, homogComponent_comm_first_action, rfl⟩
        have hk1 := (mem_congruence_subgroup_iff).1 homogComponent_comm_first_action
        have hcK : c ∈ K := by
          have := kv_mul' (kv_mul' hk hk1.1) hκ
          rwa [show k * (k⁻¹ * c * κ⁻¹) * κ = c by group] at this
        refine ⟨?_, ?_, ?_⟩
        · rw [← hkx, locF_smul]; exact prim_smul hk hPr
        · rw [locF_smul]; exact prim_smul hcK hPr'
        · show CongL (Λ := Λ) g x (c • X0r')
          rw [← hkx, show c = k * ((k⁻¹ * c * κ⁻¹) * κ) by group, mul_smul]
          apply congL_smul hk
          rw [mul_smul]
          exact congL_trans hk1.2 (congL_smul hk1.1 hcg)
    · rw [Set.indicator_of_notMem hx]
      convert measure_empty (μ := ν')
      ext x'
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hp1, _, _⟩
      rw [← hg1] at hp1
      obtain ⟨k, hk, hkx⟩ := hW σ J ψ v P Λ T hStd hP hSD hUn hEta hPr hL g1 hp1
      exact hx ⟨k, hk, hkx.trans hg1⟩
  have hprod : (ν.prod ν') (OmTyp v Λ g r) =
      μG K1s / a' * ν ((fun c : HA (Fv F v) σ J => c • X0r) '' K) := by
    rw [Measure.prod_apply hOmm, ← lintegral_indicator_const hAm]
    apply lintegral_congr_ae
    filter_upwards [hae] with x hx
    exact hslice x hx
  unfold Mv
  rw [hprod, ← ENNReal.toReal_mul, ← ENNReal.toReal_mul, ← ENNReal.toReal_mul]
  congr 1
  calc μG K1s / a' * ν ((fun c : HA (Fv F v) σ J => c • X0r) '' K) * (a * a')
      = (ν ((fun c : HA (Fv F v) σ J => c • X0r) '' K) * a) * (μG K1s / a' * a') := by ring
    _ = μG K * μG K1s := by rw [hWK, ENNReal.div_mul_cancel ha0'.1 ha0'.2]

end PI.LocMassTypW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.SatSplit
section
noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory NumberField
  IsDedekindDomain Matrix
open scoped TensorProduct

def SplitR : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)),
    StdHyp σ J ψ → UnramAt (E := E) v → etaV (E := E) v = 1 →
    ∃ (e : Fv F v ⊗[F] E) (π₁ π₂ : Fv F v ⊗[F] E →+* Fv F v),
      e * e = e ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ e = 1 - e ∧
      (∀ x, x * e = sc (E := E) v (π₁ x) * e) ∧ (∀ x, x * (1 - e) = sc (E := E) v (π₂ x) * (1 - e)) ∧
      π₁ e = 1 ∧ π₂ e = 0 ∧ (∀ c : Fv F v, π₁ (sc (E := E) v c) = c ∧ π₂ (sc (E := E) v c) = c) ∧
      (∀ x, π₂ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ x) = π₁ x) ∧ (∀ x, π₁ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ x) = π₂ x) ∧
      (∀ x, x ∈ OEv (E := E) v ↔
        π₁ x ∈ v.adicCompletionIntegers F ∧ π₂ x ∈ v.adicCompletionIntegers F)

def LatStd : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)),
    StdHyp σ J ψ → IsSDLoc σ J v Λ → UnramAt (E := E) v → etaV (E := E) v = 1 →
    LocMassOrdW.IsLatLoc v Λ →
    ∃ Q : GL (Fin n) (Fv F v ⊗[F] E),
      (∀ y, y ∈ latLoc (E := E) v Λ ↔
        ∃ x : Fin n → Fv F v ⊗[F] E, (∀ i, x i ∈ OEv (E := E) v) ∧
          y = (Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x) ∧
      ∀ x y : Fin n → Fv F v ⊗[F] E,
        hR (Fv F v) σ J ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x)
          ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ y) = ∑ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (x i) * y i

def SatSplit : Prop :=
  ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n m : ℕ)
    (A : Matrix (Fin n) (Fin m) (v.adicCompletionIntegers F)),
    (∀ t : Fin m → v.adicCompletion F,
      (∀ i, (A.map (fun a => (a : v.adicCompletion F)) *ᵥ t) i ∈ v.adicCompletionIntegers F) →
      ∀ j, t j ∈ v.adicCompletionIntegers F) →
    ∃ L : Matrix (Fin m) (Fin n) (v.adicCompletionIntegers F), L * A = 1

end PI.LocMassTypW
end
end

