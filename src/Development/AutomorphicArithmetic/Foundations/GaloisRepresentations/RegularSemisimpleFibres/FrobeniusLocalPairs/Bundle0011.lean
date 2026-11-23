module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.OneField
section
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open UpperTheory.Gal.InertialTypesAlt.L

section

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

private theorem sg_cont {σ : E ≃+* E} (hσ : Isom σ) : Continuous (sg σ : GL (Fin n) E → GL (Fin n) E) := by
  have hc : Continuous (σ : E → E) := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, (IsValuativeTopology.hasBasis_nhds x).tendsto_iff
      (IsValuativeTopology.hasBasis_nhds (σ x))]
    intro γ _
    refine ⟨γ, trivial, fun z hz => ?_⟩
    simp only [Set.mem_setOf_eq] at hz ⊢
    rw [← map_sub, hσ]
    exact hz
  exact Continuous.units_map _ (continuous_id.matrix_map hc)

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem map_diag {F : Type} [Field F] (f : E →+* F) (u : Fin n → Eˣ) :
    Matrix.GeneralLinearGroup.map f (diagT E (Fin n) u) = diagT F (Fin n) fun i => Units.map (f : E →* F) (u i) := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, val_diagT, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.diagonal_apply]
  split_ifs <;> simp

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem diag_comm (u v : Fin n → Eˣ) :
    diagT E (Fin n) u * diagT E (Fin n) v = diagT E (Fin n) v * diagT E (Fin n) u := by
  rw [← map_mul, ← map_mul, mul_comm]

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem diag_inj {u v : Fin n → Eˣ} (h : diagT E (Fin n) u = diagT E (Fin n) v) : u = v := by
  funext i
  have h1 := congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i i) h
  simp only [val_diagT, Matrix.diagonal_apply_eq] at h1
  exact Units.ext h1

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem sg_diag (σ : E ≃+* E) (p : Fin n → Eˣ) :
    sg σ (diagT E (Fin n) p) = diagT E (Fin n) (sgT σ p) := by
  exact map_diag (σ : E →+* E) p

private theorem cent_diag {σ : E ≃+* E} {q : ℕ} (hσ : Cyc σ q) {d : Fin n → Eˣ} (hd : Strict d) {δ y c : GL (Fin n) E}
    (hy : y⁻¹ * δ * sg σ y = diagT E (Fin n) d) (hc : c⁻¹ * δ * sg σ c = δ) : ∃ u, y⁻¹ * c * y = diagT E (Fin n) u := by
  have hc2 : δ * sg σ c = c * δ := by
    calc δ * sg σ c = c * (c⁻¹ * δ * sg σ c) := by group
      _ = c * δ := by rw [hc]
  have key : (y⁻¹ * c * y)⁻¹ * diagT E (Fin n) d * sg σ (y⁻¹ * c * y) = diagT E (Fin n) d := by
    rw [← hy]
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left]
    rw [← mul_assoc δ, hc2]
    simp only [mul_assoc, inv_mul_cancel_left]
  exact strictNormal E n σ q hσ d d hd hd _ key

private theorem diag_ball {r : ValueGroupWithZero E} {s : Fin n → Eˣ} (h : Near r s) : diagT E (Fin n) s ∈ ball n r := by
  intro i j
  rw [val_diagT]
  by_cases hij : i = j
  · subst hij
    simpa using h i
  · simp [Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]

private theorem near_of_ball {r : ValueGroupWithZero E} {s : Fin n → Eˣ} (h : diagT E (Fin n) s ∈ ball n r) : Near r s := by
  intro i
  have h1 := h i i
  simpa [val_diagT, Matrix.diagonal_apply_eq] using h1

end

theorem UpperTheory.Gal.InertialTypesAlt.L.oneField :
    UpperTheory.Gal.InertialTypesAlt.L.OneField := by
  intro E _ _ _ _ n σ q hσ r hr0 hr1 _ _ μ hμ A hA δ y d hd hy H hH ν hν R hR hRd
  obtain ⟨K, hK, hKo, hKc⟩ := ballSub E n r hr0 hr1
  have hsupp := (suppE E n σ q hσ r hr0 hr1 A hA).2 δ y d hd hy
  have hδ : δ = y * diagT E (Fin n) d * (sg σ y)⁻¹ := by
    rw [← hy]
    group
  have hfix : ∀ w, (y * diagT E (Fin n) w * y⁻¹)⁻¹ * δ * sg σ (y * diagT E (Fin n) w * y⁻¹) = δ ↔
      sgT σ w = w := by
    intro w
    have e : (y * diagT E (Fin n) w * y⁻¹)⁻¹ * δ * sg σ (y * diagT E (Fin n) w * y⁻¹) =
        y * ((diagT E (Fin n) w)⁻¹ * diagT E (Fin n) d * diagT E (Fin n) (sgT σ w)) * (sg σ y)⁻¹ := by
      rw [hδ, map_mul, map_mul, map_inv, sg_diag]
      group
    rw [e]
    constructor
    · intro h
      conv_rhs at h => rw [hδ]
      have h2 : (diagT E (Fin n) w)⁻¹ * diagT E (Fin n) d * diagT E (Fin n) (sgT σ w) = diagT E (Fin n) d :=
        mul_left_cancel (mul_right_cancel h)
      have h3 : diagT E (Fin n) d * diagT E (Fin n) (sgT σ w) = diagT E (Fin n) d * diagT E (Fin n) w := by
        calc diagT E (Fin n) d * diagT E (Fin n) (sgT σ w)
            = diagT E (Fin n) w * ((diagT E (Fin n) w)⁻¹ * diagT E (Fin n) d * diagT E (Fin n) (sgT σ w)) := by
              group
          _ = diagT E (Fin n) w * diagT E (Fin n) d := by rw [h2]
          _ = diagT E (Fin n) d * diagT E (Fin n) w := diag_comm w d
      exact diag_inj (mul_left_cancel h3)
    · intro h
      rw [h, hδ, mul_assoc (diagT E (Fin n) w)⁻¹, diag_comm d w]
      group
  have hcen : ∀ c ∈ H, ∃ u, y⁻¹ * c * y = diagT E (Fin n) u :=
    fun c hc => cent_diag hσ hd hy ((hH c).1 hc)
  have hback : ∀ c u, y⁻¹ * c * y = diagT E (Fin n) u → c = y * diagT E (Fin n) u * y⁻¹ := by
    intro c u hu
    rw [← hu]
    group
  have hfixH : ∀ c ∈ H, ∀ u, y⁻¹ * c * y = diagT E (Fin n) u → sgT σ u = u := by
    intro c hc u hu
    apply (hfix u).1
    rw [← hback c u hu]
    exact (hH c).1 hc
  have hclosed : IsClosed (H : Set (GL (Fin n) E)) := by
    have hset : (H : Set (GL (Fin n) E)) = {c | c⁻¹ * δ * sg σ c = δ} := Set.ext hH
    rw [hset]
    exact isClosed_eq ((continuous_inv.mul continuous_const).mul (sg_cont hσ.isom)) continuous_const
  have hcomm : ∀ a ∈ H, ∀ b ∈ H, Commute a b := by
    intro a ha b hb
    obtain ⟨u, hu⟩ := hcen a ha
    obtain ⟨v, hv⟩ := hcen b hb
    rw [hback a u hu, hback b v hv]
    show y * diagT E (Fin n) u * y⁻¹ * (y * diagT E (Fin n) v * y⁻¹) =
      y * diagT E (Fin n) v * y⁻¹ * (y * diagT E (Fin n) u * y⁻¹)
    calc y * diagT E (Fin n) u * y⁻¹ * (y * diagT E (Fin n) v * y⁻¹)
        = y * (diagT E (Fin n) u * diagT E (Fin n) v) * y⁻¹ := by group
      _ = y * (diagT E (Fin n) v * diagT E (Fin n) u) * y⁻¹ := by rw [diag_comm u v]
      _ = y * diagT E (Fin n) v * y⁻¹ * (y * diagT E (Fin n) u * y⁻¹) := by group
  have hV : ∀ ρ ∈ R, ∀ h : H, h ∈ {h : H | y⁻¹ * ↑h * y ∈ ball n r} ↔
      (y * diagT E (Fin n) ρ)⁻¹ * ↑h * (y * diagT E (Fin n) ρ) ∈ K := by
    intro ρ _ h
    obtain ⟨u, hu⟩ := hcen h h.2
    have e : (y * diagT E (Fin n) ρ)⁻¹ * ↑h * (y * diagT E (Fin n) ρ) = y⁻¹ * ↑h * y := by
      calc (y * diagT E (Fin n) ρ)⁻¹ * ↑h * (y * diagT E (Fin n) ρ)
          = (diagT E (Fin n) ρ)⁻¹ * (y⁻¹ * ↑h * y) * diagT E (Fin n) ρ := by group
        _ = y⁻¹ * ↑h * y := by
          rw [hu, mul_assoc, diag_comm u ρ, inv_mul_cancel_left]
    rw [Set.mem_setOf_eq, e, ← SetLike.mem_coe, hK]
  have hS : ∀ g, g ∈ {g : GL (Fin n) E | g⁻¹ * δ * sg σ g ∈ elemSet r A} ↔
      ∃ ρ ∈ R, ∃ h ∈ H, ∃ κ ∈ K, g = h * (y * diagT E (Fin n) ρ) * κ := by
    intro g
    rw [Set.mem_setOf_eq, hsupp g]
    constructor
    · rintro ⟨u, hu, κ, hκ, rfl⟩
      obtain ⟨ρ, hρR, p, s, hp, hs, rfl⟩ := (hR u).1 hu
      refine ⟨ρ, hρR, y * diagT E (Fin n) p * y⁻¹, (hH _).2 ((hfix p).2 hp), diagT E (Fin n) s * κ, ?_, ?_⟩
      · refine K.mul_mem ?_ ?_
        · rw [← SetLike.mem_coe, hK]
          exact diag_ball hs
        · rw [← SetLike.mem_coe, hK]
          exact hκ
      · rw [map_mul, map_mul, diag_comm ρ p]
        group
    · rintro ⟨ρ, hρR, h, hh, κ, hκ, rfl⟩
      obtain ⟨w, hw⟩ := hcen h hh
      have hw' := hfixH h hh w hw
      refine ⟨w * ρ, (hR _).2 ⟨ρ, hρR, w, 1, hw', fun i => by simp, by rw [mul_one, mul_comm]⟩, κ, ?_, ?_⟩
      · rw [← hK]
        exact hκ
      · rw [map_mul, hback h w hw]
        group
  have hD : ∀ i ∈ R, ∀ j ∈ R, (∃ h ∈ H, ∃ κ ∈ K, y * diagT E (Fin n) i = h * (y * diagT E (Fin n) j) * κ) →
      i = j := by
    rintro i hi j hj ⟨h, hh, κ, hκ, he⟩
    obtain ⟨w, hw⟩ := hcen h hh
    have hw' := hfixH h hh w hw
    have hk : κ = diagT E (Fin n) (w⁻¹ * j⁻¹ * i) := by
      calc κ = (h * (y * diagT E (Fin n) j))⁻¹ * (y * diagT E (Fin n) i) := by
            rw [he]
            group
        _ = diagT E (Fin n) (w⁻¹ * j⁻¹ * i) := by
          rw [hback h w hw, mul_comm w⁻¹ j⁻¹]
          simp only [map_mul, map_inv]
          group
    refine hRd i hi j hj ⟨w, w⁻¹ * j⁻¹ * i, hw', near_of_ball ?_, by group⟩
    rw [← hk, ← hK]
    exact hκ
  have key := cosetSum (GL (Fin n) E) μ hμ K H hKo hKc hclosed hcomm ν hν (Fin n → Eˣ) R
    (fun ρ => y * diagT E (Fin n) ρ) {h : H | y⁻¹ * ↑h * y ∈ ball n r}
    {g : GL (Fin n) E | g⁻¹ * δ * sg σ g ∈ elemSet r A} hV hS hD
  rw [hK] at key
  exact key
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.OrbTransfer
section
noncomputable section

open GlobalTheory.BCT

namespace UpperTheory.Gal.InertialTypesAlt.L

private theorem avg_const_frobenius_local_pairs {A : Type} [Group A] (c : ℂ) : avg (fun _ : A => c) = c := by
  have hS : rStab (fun _ : A => c) = ⊤ := by
    ext k
    simp [rStab]
  unfold avg
  rw [hS, Subgroup.index_top, Nat.cast_one, inv_one, one_mul]
  haveI : Subsingleton (A ⧸ (⊤ : Subgroup A)) := QuotientGroup.subsingleton_quotient_top
  exact finsum_eq_single (fun _ : A ⧸ (⊤ : Subgroup A) => c) 1
    (fun q hq => absurd (Subsingleton.elim q 1) hq)

private theorem conj_self {G : Type} [Group G] (S : Subgroup G) {s : G} (hs : s ∈ S) :
    S.map (MulAut.conj s).toMonoidHom = S := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact S.mul_mem (S.mul_mem hs hz) (S.inv_mem hs)
  · intro hy
    exact ⟨s⁻¹ * y * s, S.mul_mem (S.mul_mem (S.inv_mem hs) hy) hs, by group⟩

private theorem zpowers_closed {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (j : H →* G) (hj : Topology.IsClosedEmbedding j) (t : H) :
    IsCompact (closure (Subgroup.zpowers (j t) : Set G)) ↔ IsCompact (closure (Subgroup.zpowers t : Set H)) := by
  have hz : (Subgroup.zpowers (j t) : Set G) = j '' (Subgroup.zpowers t : Set H) := by
    rw [← MonoidHom.map_zpowers, Subgroup.coe_map]
  rw [hz, hj.closure_image_eq, hj.isInducing.isCompact_iff]

private theorem cpt_map {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (j : H →* G) (hj : Topology.IsClosedEmbedding j) (T : Subgroup H) :
    cptPart (T.map j) = (cptPart T).map j := by
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_image, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hc⟩
    exact ⟨t, ⟨ht, (zpowers_closed j hj t).1 hc⟩, rfl⟩
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, (zpowers_closed j hj t).2 hc⟩

private theorem conj_closed {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (c : G) :
    Topology.IsClosedEmbedding (MulAut.conj c).toMonoidHom := by
  have h : ((MulAut.conj c).toMonoidHom : G → G) = (Homeomorph.mulLeft c).trans (Homeomorph.mulRight c⁻¹) := by
    ext x
    simp [MulAut.conj_apply]
  rw [h]
  exact Homeomorph.isClosedEmbedding _

private def wt {G : Type} [Group G] [TopologicalSpace G] (T K : Subgroup G) (x : G) : ℕ :=
  (T ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex (cptPart T)

private theorem wt_inv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (T K : Subgroup G)
    {t κ : G} (ht : t ∈ T) (hκ : κ ∈ K) (x : G) : wt T K (t * x * κ) = wt T K x := by
  unfold wt
  have hinj : Function.Injective (MulAut.conj t).toMonoidHom := (MulAut.conj t).injective
  have hT : T.map (MulAut.conj t).toMonoidHom = T := conj_self T ht
  have hKm : K.map (MulAut.conj (t * x * κ)).toMonoidHom =
      (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
    ext y
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨x * (κ * k * κ⁻¹) * x⁻¹,
        ⟨κ * k * κ⁻¹, K.mul_mem (K.mul_mem hκ hk) (K.inv_mem hκ), rfl⟩, by group⟩
    · rintro ⟨z, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨κ⁻¹ * k * κ, K.mul_mem (K.mul_mem (K.inv_mem hκ) hk) hκ, by group⟩
  have hcpt : (cptPart T).map (MulAut.conj t).toMonoidHom = cptPart T := by
    rw [← cpt_map _ (conj_closed t) T, hT]
  have hI : T ⊓ (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom =
      (T ⊓ K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
    rw [Subgroup.map_inf_eq _ _ _ hinj, hT]
  rw [hKm]
  calc (T ⊓ (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom).relIndex (cptPart T)
      = ((T ⊓ K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom).relIndex
          ((cptPart T).map (MulAut.conj t).toMonoidHom) := by rw [hI, hcpt]
    _ = _ := Subgroup.relIndex_map_map_of_injective _ _ hinj

private theorem wt_map {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (j : H →* G) (hj : Topology.IsClosedEmbedding j) (T₀ : Subgroup H) (K : Subgroup G) (K₀ : Subgroup H)
    (hK : ∀ h, j h ∈ K ↔ h ∈ K₀) (h : H) : wt (T₀.map j) K (j h) = wt T₀ K₀ h := by
  unfold wt
  have h2 : T₀.map j ⊓ K.map (MulAut.conj (j h)).toMonoidHom =
      (T₀ ⊓ K₀.map (MulAut.conj h).toMonoidHom).map j := by
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, k, hk, hkt⟩
      refine ⟨t, ⟨ht, h⁻¹ * t * h, (hK _).1 ?_, by group⟩, rfl⟩
      have : k = j (h⁻¹ * t * h) := by
        simp only [map_mul, map_inv, ← hkt]
        group
      exact this ▸ hk
    · rintro ⟨t, ⟨ht, k, hk, rfl⟩, rfl⟩
      exact ⟨⟨_, ht, rfl⟩, j k, (hK k).2 hk, by simp⟩
  rw [h2, cpt_map j hj]
  exact Subgroup.relIndex_map_map_of_injective _ _ hj.injective

private theorem sum_transfer {G H : Type} [Group G] [Group H] (j : H →* G) (hj : Function.Injective j)
    (T : Subgroup G) (T₀ : Subgroup H) (hT : T = T₀.map j) (K : Subgroup G) (K₀ : Subgroup H)
    (hK : ∀ h, j h ∈ K ↔ h ∈ K₀) (F : G → ℂ) (F₀ : H → ℂ)
    (hinv : ∀ t ∈ T, ∀ κ ∈ K, ∀ x, F (t * x * κ) = F x) (hjF : ∀ h, F (j h) = F₀ h)
    (hsupp : ∀ x, F x ≠ 0 → ∃ h, ∃ κ ∈ K, x = j h * κ) :
    ∑ᶠ q : DoubleCoset.Quotient (T : Set G) (K : Set G), F (Quotient.out q) =
      ∑ᶠ q : DoubleCoset.Quotient (T₀ : Set H) (K₀ : Set H), F₀ (Quotient.out q) := by
  classical
  subst hT
  let e : DoubleCoset.Quotient (T₀ : Set H) (K₀ : Set H) →
      DoubleCoset.Quotient ((T₀.map j : Subgroup G) : Set G) (K : Set G) :=
    fun p => DoubleCoset.mk (T₀.map j) K (j (Quotient.out p))
  have hval : ∀ x, F (Quotient.out (DoubleCoset.mk (T₀.map j) K x)) = F x := by
    intro x
    obtain ⟨a, ha, b, hb, hx⟩ := DoubleCoset.mk_out_eq_mul (T₀.map j) K x
    rw [hx]
    exact hinv a ha b hb x
  have he' : ∀ h, e (DoubleCoset.mk T₀ K₀ h) = DoubleCoset.mk (T₀.map j) K (j h) := by
    intro h
    obtain ⟨a, ha, b, hb, hab⟩ := DoubleCoset.mk_out_eq_mul T₀ K₀ h
    show DoubleCoset.mk (T₀.map j) K (j (Quotient.out (DoubleCoset.mk T₀ K₀ h))) = _
    rw [hab, DoubleCoset.eq]
    refine ⟨(j a)⁻¹, (T₀.map j).inv_mem (Subgroup.mem_map_of_mem j ha), (j b)⁻¹,
      K.inv_mem ((hK b).mpr hb), ?_⟩
    simp only [map_mul]
    group
  have he : Function.Injective e := by
    intro p p' hpp
    have hpp' : DoubleCoset.mk (T₀.map j) K (j (Quotient.out p)) =
        DoubleCoset.mk (T₀.map j) K (j (Quotient.out p')) := hpp
    rw [DoubleCoset.eq] at hpp'
    obtain ⟨a, ha, b, hb, hab⟩ := hpp'
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    rw [← DoubleCoset.out_eq' p, ← DoubleCoset.out_eq' p', DoubleCoset.eq]
    have hjb : j ((a₀ * Quotient.out p)⁻¹ * Quotient.out p') = b := by
      rw [map_mul, map_inv, map_mul, hab]
      group
    refine ⟨a₀, ha₀, (a₀ * Quotient.out p)⁻¹ * Quotient.out p', ?_, by group⟩
    rw [← hK, hjb]
    exact hb
  have hsub : Function.support
      (fun q : DoubleCoset.Quotient ((T₀.map j : Subgroup G) : Set G) (K : Set G) =>
        F (Quotient.out q)) ⊆ Set.range e := by
    intro q hq
    obtain ⟨h, κ, hκ, hx⟩ := hsupp _ hq
    refine ⟨DoubleCoset.mk T₀ K₀ h, ?_⟩
    rw [he', ← DoubleCoset.out_eq' q, DoubleCoset.eq]
    exact ⟨1, (T₀.map j).one_mem, κ, hκ, by rw [hx, one_mul]⟩
  have hfull : ∑ᶠ q ∈ Set.range e, F (Quotient.out q) =
      ∑ᶠ q : DoubleCoset.Quotient ((T₀.map j : Subgroup G) : Set G) (K : Set G),
        F (Quotient.out q) := by
    rw [finsum_mem_def, Set.indicator_eq_self.mpr hsub]
  rw [← hfull, finsum_mem_range he]
  refine finsum_congr (fun p => ?_)
  show F (Quotient.out (DoubleCoset.mk (T₀.map j) K (j (Quotient.out p)))) = F₀ (Quotient.out p)
  rw [hval, hjF]

theorem orbTransfer : OrbTransfer := by
  intro G H _ _ _ _ _ _ _ _ j hj θ K K₀ hK δ γ hT φ f hφ hsupp hφf hθ
  have hconst : ∀ x : G, (avg fun k : K => φ ((x * k)⁻¹ * δ * θ (x * k))) = φ (x⁻¹ * δ * θ x) := by
    intro x
    have e : (fun k : K => φ ((x * k)⁻¹ * δ * θ (x * k))) = fun _ => φ (x⁻¹ * δ * θ x) := by
      funext k
      rw [← hφ (k : G) k.2 (x⁻¹ * δ * θ x)]
      congr 1
      rw [map_mul]
      group
    rw [e, avg_const_frobenius_local_pairs]
  have hconst₀ : ∀ y : H, (avg fun k : K₀ => f ((y * k)⁻¹ * γ * MonoidHom.id H (y * k))) =
      f (y⁻¹ * γ * y) := by
    intro y
    have e : (fun k : K₀ => f ((y * k)⁻¹ * γ * MonoidHom.id H (y * k))) = fun _ => f (y⁻¹ * γ * y) := by
      funext k
      rw [MonoidHom.id_apply, ← hφf, ← hφf, ← hφ (j k) ((hK k).2 k.2) ((j y)⁻¹ * δ * θ (j y))]
      congr 1
      rw [map_mul, map_mul]
      group
    rw [e, avg_const_frobenius_local_pairs]
  have hinv : ∀ t ∈ twCent θ δ, ∀ κ ∈ K, ∀ x : G,
      (fun x => (wt (twCent θ δ) K x : ℂ) * φ (x⁻¹ * δ * θ x)) (t * x * κ) =
      (fun x => (wt (twCent θ δ) K x : ℂ) * φ (x⁻¹ * δ * θ x)) x := by
    intro t ht κ hκ x
    have ht' : t * δ = δ * θ t := ht
    have e : (t * x * κ)⁻¹ * δ * θ (t * x * κ) = κ⁻¹ * (x⁻¹ * δ * θ x) * θ κ := by
      rw [map_mul, map_mul]
      calc (t * x * κ)⁻¹ * δ * (θ t * θ x * θ κ)
          = κ⁻¹ * x⁻¹ * t⁻¹ * (δ * θ t) * θ x * θ κ := by group
        _ = _ := by rw [← ht']; group
    simp only
    rw [wt_inv (twCent θ δ) K ht hκ x, e, hφ κ hκ]
  have hjF : ∀ y : H,
      (fun x => (wt (twCent θ δ) K x : ℂ) * φ (x⁻¹ * δ * θ x)) (j y) =
      (fun y => (wt (twCent (MonoidHom.id H) γ) K₀ y : ℂ) * f (y⁻¹ * γ * y)) y := by
    intro y
    simp only
    rw [hT, wt_map j hj _ K K₀ hK y, hφf]
  have hsupp' : ∀ x : G, (fun x => (wt (twCent θ δ) K x : ℂ) * φ (x⁻¹ * δ * θ x)) x ≠ 0 →
      ∃ y, ∃ κ ∈ K, x = j y * κ := by
    intro x hx
    apply hsupp x
    intro h0
    apply hx
    simp only [h0, mul_zero]
  unfold twOrb
  simp only [hconst, hconst₀]
  exact sum_transfer j hj.injective (twCent θ δ) (twCent (MonoidHom.id H) γ) hT K K₀ hK _ _
    hinv hjF hsupp'

end UpperTheory.Gal.InertialTypesAlt.L
end
end

