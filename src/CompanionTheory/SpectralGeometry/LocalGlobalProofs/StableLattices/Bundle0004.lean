module

public import Mathlib
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PairingOfSandwichStatement
section
open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.HermLat

section Lat

variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]

theorem smul_mem_of_isLat {Λ : AddSubgroup V} (hΛ : IsLat L Λ) {a : L} (ha : ‖a‖ ≤ 1) {x : V}
    (hx : x ∈ Λ) : a • x ∈ Λ := by
  obtain ⟨m, b, hb⟩ := hΛ
  rw [hb] at hx ⊢
  intro i
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) (hx i)

theorem exists_smul_mem_of_isLat {Λ : AddSubgroup V} (hΛ : IsLat L Λ) (v : V) :
    ∃ a : L, a ≠ 0 ∧ a • v ∈ Λ := by
  obtain ⟨m, b, hb⟩ := hΛ
  have hS0 : 0 ≤ ∑ i, ‖b.repr v i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨a, ha0, ha⟩ := NormedField.exists_norm_lt L
    (show (0 : ℝ) < 1 / (1 + ∑ i, ‖b.repr v i‖) by positivity)
  refine ⟨a, norm_pos_iff.mp ha0, (hb _).2 fun i => ?_⟩
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  have h1 : ‖b.repr v i‖ ≤ 1 + ∑ i, ‖b.repr v i‖ := by
    have := Finset.single_le_sum (f := fun i => ‖b.repr v i‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ i)
    linarith
  calc ‖a‖ * ‖b.repr v i‖ ≤ (1 / (1 + ∑ i, ‖b.repr v i‖)) * (1 + ∑ i, ‖b.repr v i‖) := by
        gcongr
    _ = 1 := by field_simp


variable (L) in
def adjoin [IsUltrametricDist L] (Λ : AddSubgroup V) (v : V) : AddSubgroup V where
  carrier := {z | ∃ l ∈ Λ, ∃ a : L, ‖a‖ ≤ 1 ∧ z = l + a • v}
  add_mem' := by
    rintro _ _ ⟨l, hl, a, ha, rfl⟩ ⟨l', hl', a', ha', rfl⟩
    refine ⟨l + l', Λ.add_mem hl hl', a + a',
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha ha'), ?_⟩
    rw [add_smul]
    abel
  zero_mem' := ⟨0, Λ.zero_mem, 0, by simp, by simp⟩
  neg_mem' := by
    rintro _ ⟨l, hl, a, ha, rfl⟩
    refine ⟨-l, Λ.neg_mem hl, -a, by simpa using ha, ?_⟩
    rw [neg_smul]
    abel

end Lat

section Herm

variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}

theorem herm_add_left (hh : IsHerm s h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hh.2.2.1 z (x + y), hh.1, map_add (f := _), ← hh.2.2.1, ← hh.2.2.1]

theorem herm_smul_left (hh : IsHerm s h) (a : L) (x y : V) : h (a • x) y = s a * h x y := by
  rw [hh.2.2.1 y (a • x), hh.2.1, map_mul, ← hh.2.2.1]

theorem herm_add_add (hh : IsHerm s h) (u v : V) :
    h (u + v) (u + v) = h u u + (h u v + s (h u v)) + h v v := by
  rw [herm_add_left hh, hh.1, hh.1, ← hh.2.2.1 u v]
  ring

end Herm

section Main

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {V : Type} [AddCommGroup V]
  [Module L V] {s : L →+* L} {δ : L} {h : V → V → L}

theorem norm_sub_le_of_le {a b : L} {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a - b‖ ≤ c := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by simpa using hb))

theorem pairing_le (hδ : IsDelta s δ) (hh : IsHerm s h) {Λ : AddSubgroup V}
    (hL : IsLat L Λ) (hint : ∀ x ∈ Λ, ‖h x x‖ ≤ 1) {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    ‖h x y‖ ≤ ‖δ‖ := by
  refine (hδ.2.1 _).1 fun t ht => ?_
  have hty : t • y ∈ Λ := smul_mem_of_isLat hL ht hy
  have e := herm_add_add hh x (t • y)
  have e' : h x y * t + s (h x y * t) =
      h (x + t • y) (x + t • y) - h x x - h (t • y) (t • y) := by
    rw [e, hh.2.1 t x y, mul_comm t]
    ring
  rw [e']
  exact norm_sub_le_of_le (norm_sub_le_of_le (hint _ (Λ.add_mem hx hty)) (hint _ hx)) (hint _ hty)

theorem adjoin_integral (hs : IsInv s) (hδ : IsDelta s δ) (hh : IsHerm s h) {Λ : AddSubgroup V}
    (hint : ∀ x ∈ Λ, ‖h x x‖ ≤ 1) {p : L} (hp0 : p ≠ 0) {x : V}
    (hq : ‖h x x‖ ≤ ‖p‖ ^ 2) (hsmall : ∀ y ∈ Λ, ‖h x y‖ ≤ ‖p‖ * ‖δ‖) :
    ∀ z ∈ adjoin (L := L) Λ (p⁻¹ • x), ‖h z z‖ ≤ 1 := by
  rintro _ ⟨l, hl, a, ha, rfl⟩
  have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  rw [herm_add_add hh]
  have hb : ‖h l (a • p⁻¹ • x)‖ ≤ ‖δ‖ := by
    rw [hh.2.1, hh.2.1, hh.2.2.1 x l, norm_mul, norm_mul, norm_inv, hs.2.1]
    have h1 := hsmall l hl
    calc ‖a‖ * (‖p‖⁻¹ * ‖h x l‖) ≤ 1 * (‖p‖⁻¹ * (‖p‖ * ‖δ‖)) := by gcongr
      _ = ‖δ‖ := by field_simp
  have htr : ‖h l (a • p⁻¹ • x) + s (h l (a • p⁻¹ • x))‖ ≤ 1 := by
    have := (hδ.2.1 _).2 hb 1 (by simp)
    simpa using this
  have hlast : ‖h (a • p⁻¹ • x) (a • p⁻¹ • x)‖ ≤ 1 := by
    rw [herm_smul_left hh, herm_smul_left hh, hh.2.1, hh.2.1, norm_mul, norm_mul, norm_mul,
      norm_mul, hs.2.1, hs.2.1, norm_inv]
    have hpp : ‖p‖⁻¹ * (‖p‖⁻¹ * ‖p‖ ^ 2) = 1 := by field_simp
    calc ‖a‖ * (‖p‖⁻¹ * (‖a‖ * (‖p‖⁻¹ * ‖h x x‖)))
        ≤ 1 * (‖p‖⁻¹ * (1 * (‖p‖⁻¹ * ‖p‖ ^ 2))) := by gcongr
      _ = 1 := by rw [one_mul, one_mul, hpp]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hint l hl) htr)) hlast)

theorem pairing_of_sandwich : StSandwich → StPairing := by
  intro hS L _ _ _ _ s hs δ hδ V _ _ _ h hh Λ hΛ
  obtain ⟨hL, hint, hmax⟩ := hΛ
  refine ⟨fun x hx y hy => pairing_le hδ hh hL hint hx hy, ?_⟩
  intro p hp hunif x hx hxp hq
  have hp0 : p ≠ 0 := by
    rintro rfl
    obtain ⟨a, ha0, ha⟩ := NormedField.exists_norm_lt L (show (0 : ℝ) < 1 by norm_num)
    have := hunif a ha
    rw [norm_zero] at this
    linarith
  have hδ0 : δ ≠ 0 := hδ.1
  have hδn : 0 < ‖δ‖ := norm_pos_iff.mpr hδ0
  by_cases hex : ∃ y ∈ Λ, ‖h x y‖ = ‖δ‖
  · obtain ⟨y, hy, hyn⟩ := hex
    have hne : h x y ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hyn
      exact hδ0 (norm_eq_zero.mp hyn.symm)
    refine ⟨(δ / h x y) • y, smul_mem_of_isLat hL ?_ hy, ?_⟩
    · rw [norm_div, hyn, div_self hδn.ne']
    · rw [hh.2.1]
      field_simp
  · exfalso
    have hsmall : ∀ y ∈ Λ, ‖h x y‖ ≤ ‖p‖ * ‖δ‖ := by
      intro y hy
      have hlt : ‖h x y‖ < ‖δ‖ :=
        lt_of_le_of_ne (pairing_le hδ hh hL hint hx hy) fun e => hex ⟨y, hy, e⟩
      have h2 : ‖h x y / δ‖ < 1 := by
        rw [norm_div, div_lt_one hδn]
        exact hlt
      have h3 := hunif _ h2
      rw [norm_div, div_le_iff₀ hδn] at h3
      exact h3
    have hle : Λ ≤ adjoin (L := L) Λ (p⁻¹ • x) := fun l hl => ⟨l, hl, 0, by simp, by simp⟩
    have hL' : IsLat L (adjoin (L := L) Λ (p⁻¹ • x)) := by
      refine hS L V Λ _ p hL hp0 ?_ ?_ ?_
      · rintro _ ⟨l, hl, a, ha, rfl⟩
        have e : p • (l + a • p⁻¹ • x) = p • l + a • x := by
          rw [smul_add, smul_comm p a, smul_smul p, mul_inv_cancel₀ hp0, one_smul]
        rw [e]
        exact Λ.add_mem (smul_mem_of_isLat hL hp.le hl) (smul_mem_of_isLat hL ha hx)
      · intro v
        obtain ⟨a, ha, hav⟩ := exists_smul_mem_of_isLat hL v
        exact ⟨a, ha, hle hav⟩
      · rintro b hb _ ⟨l, hl, a, ha, rfl⟩
        refine ⟨b • l, smul_mem_of_isLat hL hb hl, b * a, ?_, ?_⟩
        · rw [norm_mul]
          exact mul_le_one₀ hb (norm_nonneg _) ha
        · rw [smul_add, smul_smul]
    have heq := hmax _ hL' (adjoin_integral hs hδ hh hint hp0 hq hsmall) hle
    apply hxp
    rw [← heq]
    exact ⟨0, Λ.zero_mem, 1, by simp, by simp⟩

end Main

end GlobalTheory.CompanionTheory.HermLat

end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SandwichStatement
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Lattice

open CompanionTheory.Rg.FlB
open scoped NormedField Valued

theorem exists_common_denom {L ι : Type} [Field L] (O : Subring L)
    (hfrac : ∀ x : L, ∃ a : O, (a : L) ≠ 0 ∧ (a : L) * x ∈ O) (s : Finset ι) (g : ι → L) :
    ∃ d : O, (d : L) ≠ 0 ∧ ∀ i ∈ s, (d : L) * g i ∈ O := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert i s _ ih =>
    obtain ⟨d, hd, h⟩ := ih
    obtain ⟨a, ha, hi⟩ := hfrac (g i)
    refine ⟨a * d, by simp [ha, hd], fun j hj => ?_⟩
    rcases Finset.mem_insert.1 hj with rfl | hj
    · have : ((a * d : O) : L) * g j = (d : L) * ((a : L) * g j) := by push_cast; ring
      rw [this]
      exact O.mul_mem d.2 hi
    · have : ((a * d : O) : L) * g j = (a : L) * ((d : L) * g j) := by push_cast; ring
      rw [this]
      exact O.mul_mem a.2 (h j hj)

theorem exists_basis_of_pid {L V : Type} [Field L] [AddCommGroup V] [Module L V] (O : Subring L)
    [IsPrincipalIdealRing O]
    (hfrac : ∀ x : L, ∃ a : O, (a : L) ≠ 0 ∧ (a : L) * x ∈ O) {m : ℕ}
    (b : Module.Basis (Fin m) L V) (Λ : AddSubgroup V) (c : L) (hc : c ≠ 0)
    (h1 : ∀ x ∈ Λ, ∀ i, b.repr (c • x) i ∈ O) (hspan : ∀ x : V, ∃ a : L, a ≠ 0 ∧ a • x ∈ Λ)
    (hO : ∀ a ∈ O, ∀ x ∈ Λ, a • x ∈ Λ) :
    ∃ (n : ℕ) (B : Module.Basis (Fin n) L V), ∀ x, x ∈ Λ ↔ ∀ i, B.repr x i ∈ O := by
  classical

  let ψ : (Fin m → O) →ₗ[O] V :=
    { toFun := fun y => c⁻¹ • ∑ j, (y j : L) • b j
      map_add' := fun y z => by
        simp only [Pi.add_apply, Subring.coe_add, add_smul, Finset.sum_add_distrib, smul_add]
      map_smul' := fun a y => by
        simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
          Subring.coe_mul, mul_smul]
        exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _ }
  have hψ : ∀ y, ψ y = c⁻¹ • ∑ j, (y j : L) • b j := fun _ => rfl
  have hinj : LinearMap.ker ψ = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun y hy => ?_
    rw [hψ] at hy
    have h0 : ∑ j, (y j : L) • b j = 0 := (smul_eq_zero.1 hy).resolve_left (inv_ne_zero hc)
    have := Fintype.linearIndependent_iff.1 b.linearIndependent (fun j => (y j : L)) h0
    exact funext fun j => Subtype.ext (this j)
  let N : Submodule O (Fin m → O) :=
    { carrier := {y | ψ y ∈ Λ}
      add_mem' := fun {y z} hy hz => by
        simpa [map_add (f := _)] using Λ.add_mem hy hz
      zero_mem' := by simp [Λ.zero_mem]
      smul_mem' := fun a y hy => by
        simpa [map_smul, Subring.smul_def] using hO a a.2 _ hy }
  obtain ⟨n, bN⟩ := Submodule.basisOfPid (Pi.basisFun O (Fin m)) N
  let v : Fin n → V := fun i => ψ (bN i : Fin m → O)
  have hvΛ : ∀ i, v i ∈ Λ := fun i => (bN i).2

  have hrep : ∀ z ∈ Λ, ∃ o : Fin n → O, z = ∑ i, (o i : L) • v i := by
    intro z hz
    let y : Fin m → O := fun j => ⟨b.repr (c • z) j, h1 z hz j⟩
    have hy : ψ y = z := by
      rw [hψ]
      have : ∑ j, (y j : L) • b j = c • z := b.sum_repr (c • z)
      rw [this, smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hyN : y ∈ N := by
      change ψ y ∈ Λ
      rwa [hy]
    refine ⟨fun i => bN.repr ⟨y, hyN⟩ i, ?_⟩
    have h2 := congrArg (fun w : N => ψ (w : Fin m → O)) (bN.sum_repr ⟨y, hyN⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, hy] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun i _ => by rw [Subring.smul_def]

  have hliO : LinearIndependent O v := by
    have h3 : LinearIndependent O (fun i => (bN i : Fin m → O)) :=
      bN.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
    exact h3.map' ψ hinj
  have hli : LinearIndependent L v := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    obtain ⟨d, hd, hdg⟩ := exists_common_denom O hfrac Finset.univ g
    have h4 : ∑ j, (⟨(d : L) * g j, hdg j (Finset.mem_univ j)⟩ : O) • v j = 0 := by
      have : ∑ j, (⟨(d : L) * g j, hdg j (Finset.mem_univ j)⟩ : O) • v j
          = (d : L) • ∑ j, g j • v j := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [Subring.smul_def, mul_smul]
      rw [this, hg, smul_zero]
    have h5 := Fintype.linearIndependent_iff.1 hliO _ h4 i
    have h6 : (d : L) * g i = 0 := congrArg Subtype.val h5
    exact (mul_eq_zero.1 h6).resolve_left hd
  have hsp : ⊤ ≤ Submodule.span L (Set.range v) := by
    intro x _
    obtain ⟨a, ha, hax⟩ := hspan x
    obtain ⟨o, ho⟩ := hrep _ hax
    have hx : x = a⁻¹ • (a • x) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [hx, ho]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  let B := Module.Basis.mk hli hsp
  have hB : ∀ i, B i = v i := fun i => by simp [B]
  refine ⟨n, B, fun x => ⟨fun hx i => ?_, fun hx => ?_⟩⟩
  · obtain ⟨o, ho⟩ := hrep x hx
    have h7 : x = ∑ j, (o j : L) • B j := by simpa only [hB] using ho
    have h8 : B.repr x i = (o i : L) := by
      rw [h7, B.repr_sum_self]
    rw [h8]
    exact (o i).2
  · rw [← B.sum_repr x]
    exact Λ.sum_mem fun i _ => hO _ (hx i) _ (by rw [hB]; exact hvΛ i)

theorem stSandwich : StSandwich := by
  intro L _ _ hp V _ _ Λ₀ Λ c ⟨m, b, hb⟩ hc hcΛ hspan hO
  have hmem : ∀ x : L, x ∈ 𝒪[L] ↔ ‖x‖ ≤ 1 := fun x => Valued.integer.mem_iff
  haveI : CompactSpace 𝒪[L] := by
    have hset : ((𝒪[L] : Subring L) : Set L) = Metric.closedBall 0 1 := by
      ext x
      simp [hmem]
    have hk : IsCompact ((𝒪[L] : Subring L) : Set L) := by
      rw [hset]
      exact isCompact_closedBall 0 1
    exact isCompact_iff_compactSpace.1 hk
  haveI : (Valued.v : Valuation L NNReal).IsNontrivial := by
    obtain ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one L
    refine (Valued.v : Valuation L NNReal).isNontrivial_iff_exists_lt_one.2 ⟨x, ?_, ?_⟩
    · simpa using hx0
    · simpa [← NNReal.coe_lt_coe] using hx1
  haveI : IsDiscreteValuationRing 𝒪[L] := Valued.integer.isDiscreteValuationRing_of_compactSpace
  have hfrac : ∀ x : L, ∃ a : 𝒪[L], (a : L) ≠ 0 ∧ (a : L) * x ∈ 𝒪[L] := by
    intro x
    by_cases hx : ‖x‖ ≤ 1
    · exact ⟨1, by simp, by simpa using (hmem x).2 hx⟩
    · have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      have hlt : 1 < ‖x‖ := not_le.1 hx
      refine ⟨⟨x⁻¹, (hmem _).2 ?_⟩, by simpa using hx0, ?_⟩
      · rw [norm_inv]
        exact inv_le_one_of_one_le₀ hlt.le
      · simp [hx0, one_mem]
  obtain ⟨n, B, hB⟩ := exists_basis_of_pid 𝒪[L] hfrac b Λ c hc
    (fun x hx i => (hmem _).2 ((hb _).1 (hcΛ x hx) i)) hspan
    (fun a ha x hx => hO a ((hmem a).1 ha) x hx)
  exact ⟨n, B, fun x => (hB x).trans (forall_congr' fun i => hmem _)⟩

end GlobalTheory.CompanionTheory.Lattice
end
end

