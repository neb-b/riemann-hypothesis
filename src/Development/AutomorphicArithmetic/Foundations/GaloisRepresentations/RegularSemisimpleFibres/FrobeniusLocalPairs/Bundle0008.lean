module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ElemPairJ
public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ContractB
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.SmallRadAlt
section
noncomputable section

open ValuativeRel Matrix GlobalTheory.SplitWeil UpperTheory.ConvolutionTheory.Loc UpperTheory.Gal.Join
open GlobalTheory.SmGL hiding iwahori

namespace UpperTheory.Gal.InertialTypesAlt.L

def BallLev : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (r : ValueGroupWithZero k),
    0 < r → r < 1 → ∀ K : Subgroup (GL (Fin n) k), (K : Set (GL (Fin n) k)) = ball n r → IwLev K ∧ ∀ t, dcos K t = elemSet r {t}

def LevOf : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (r : ValueGroupWithZero k),
    0 < r → r < 1 → ∀ D : Subgroup (Fin n → kˣ), IsCompact (D : Set (Fin n → kˣ)) → (∀ d ∈ D, ∀ i, valuation k (d i : k) = 1) →
    ∃ K : Subgroup (GL (Fin n) k), (∀ g, g ∈ K ↔ ∃ a ∈ ball n r, ∃ d ∈ D, g = a * diagT k (Fin n) d) ∧ IwLev K ∧
      ∀ t, dcos K t = elemSet r {x | ∃ d ∈ D, x = t * d}

def SmallRad : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ),
    (∀ U : Set (GL (Fin n) k), U ∈ nhds 1 → ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ ∀ r' ≤ r, ball n r' ⊆ U) ∧
    (∀ W : Set (Fin n → kˣ), W ∈ nhds 1 → ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ ∀ r' ≤ r, ∀ u, Near r' u → u ∈ W) ∧
    (∀ r : ValueGroupWithZero k, r < 1 → ∃ D : Subgroup (Fin n → kˣ), (∀ u, u ∈ D ↔ Near r u) ∧ IsCompact (D : Set (Fin n → kˣ))) ∧
    Continuous (diagT k (Fin n)) ∧ (∃ t : Fin n → kˣ, Strict t) ∧ ∀ t₀ t : Fin n → kˣ, Strict t₀ → Dom t → Strict (t₀ * t)

end UpperTheory.Gal.InertialTypesAlt.L
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.StrictNear
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

section

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem sg_diag (σ : E ≃+* E) (u : Fin n → Eˣ) :
    sg σ (diagT E (Fin n) u) = diagT E (Fin n) (sgT σ u) := by
  ext i j
  rw [sg, GeneralLinearGroup.map_apply, val_diagT, val_diagT]
  by_cases h : i = j
  · subst h
    simp [sgT]
  · simp [Matrix.diagonal_apply_ne _ h]

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem diag_inj : Function.Injective (diagT E (Fin n)) := by
  intro a b h
  funext i
  apply Units.ext
  have := congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i i) h
  simpa [val_diagT] using this

private theorem near_val {r : ValueGroupWithZero E} (hr : r < 1) {s : Fin n → Eˣ} (hs : Near r s) (i : Fin n) :
    valuation E (s i : E) = 1 := by
  have h1 : valuation E ((s i : E) - 1) < valuation E (1 : E) := by
    rw [map_one]
    exact lt_of_le_of_lt (hs i) hr
  have h2 := Valuation.map_add_eq_of_lt_right (valuation E) h1
  simpa using h2

private theorem strict_near {r : ValueGroupWithZero E} (hr : r < 1) {t s : Fin n → Eˣ} (ht : Strict t)
    (hs : Near r s) : Strict (t * s) := by
  have key : ∀ k, valuation E ((t * s) k : E) = valuation E (t k : E) := by
    intro k
    rw [Pi.mul_apply, Units.val_mul, map_mul, near_val hr hs k, mul_one]
  intro i j hij
  rw [key, key]
  exact ht i j hij

private theorem ball_sg {r : ValueGroupWithZero E} {σ : E ≃+* E} (hσ : Isom σ) {a : GL (Fin n) E}
    (ha : a ∈ ball n r) : sg σ a ∈ ball n r := by
  simp only [ball, Set.mem_setOf_eq] at ha ⊢
  intro i j
  have h : ((sg σ a : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j
      = σ ((a : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) := by
    rw [sg, GeneralLinearGroup.map_apply, map_sub]
    congr 1
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]
  rw [h, hσ]
  exact ha i j

private theorem diag_ball {r : ValueGroupWithZero E} {s : Fin n → Eˣ} (hs : Near r s) :
    diagT E (Fin n) s ∈ ball n r := by
  intro i j
  rw [val_diagT]
  by_cases h : i = j
  · subst h
    simpa using hs i
  · simp [Matrix.diagonal_apply_ne _ h, one_apply_ne h]

end

end UpperTheory.Gal.InertialTypesAlt.L

theorem UpperTheory.Gal.InertialTypesAlt.L.suppE :
    UpperTheory.Gal.InertialTypesAlt.L.SuppE := by
  intro E _ _ _ _ n σ q hc r hr0 hr1 A hA
  have hσ : Isom σ := hc.isom
  obtain ⟨K, hK, -, -⟩ := ballSub E n r hr0 hr1
  have bmul : ∀ a ∈ ball n r, ∀ b ∈ ball n r, a * b ∈ ball n r := by
    intro a ha b hb
    rw [← hK] at ha hb ⊢
    exact K.mul_mem ha hb
  have binv : ∀ a ∈ ball n r, a⁻¹ ∈ ball n r := by
    intro a ha
    rw [← hK] at ha ⊢
    exact K.inv_mem ha
  have step : ∀ δ g : GL (Fin n) E, g⁻¹ * δ * sg σ g ∈ UpperTheory.Gal.InertialTypesAlt.L.elemSet r A →
      ∃ k ∈ ball n r, ∃ t ∈ A, ∃ s, UpperTheory.Gal.InertialTypesAlt.L.Near r s ∧
        g⁻¹ * δ * sg σ g = k⁻¹ * diagT E (Fin n) (t * s) * sg σ k := by
    intro δ g hg
    obtain ⟨a, ha, b, hb, t, ht, he⟩ := hg
    obtain ⟨k, hk, s, hs, hks⟩ := contractB E n σ hσ t (hA t ht) r hr1 a ha b hb
    exact ⟨k, hk, t, ht, s, hs, he.trans hks⟩
  refine ⟨?_, ?_⟩
  · intro δ g hg
    obtain ⟨k, hk, t, ht, s, hs, he⟩ := step δ g hg
    refine ⟨g * k⁻¹, t, ht, s, hs, UpperTheory.Gal.InertialTypesAlt.L.strict_near hr1 (hA t ht) hs, ?_⟩
    calc (g * k⁻¹)⁻¹ * δ * sg σ (g * k⁻¹)
        = k * (g⁻¹ * δ * sg σ g) * (sg σ k)⁻¹ := by
          rw [map_mul, map_inv]
          group
      _ = diagT E (Fin n) (t * s) := by
          rw [he]
          group
  · intro δ y d hd hy g
    constructor
    · intro hg
      obtain ⟨k, hk, t, ht, s, hs, he⟩ := step δ g hg
      have hts : Strict (t * s) := UpperTheory.Gal.InertialTypesAlt.L.strict_near hr1 (hA t ht) hs
      have hx : (y⁻¹ * g * k⁻¹)⁻¹ * diagT E (Fin n) d * sg σ (y⁻¹ * g * k⁻¹)
          = diagT E (Fin n) (t * s) := by
        rw [← hy]
        calc (y⁻¹ * g * k⁻¹)⁻¹ * (y⁻¹ * δ * sg σ y) * sg σ (y⁻¹ * g * k⁻¹)
            = k * (g⁻¹ * δ * sg σ g) * (sg σ k)⁻¹ := by
              rw [map_mul, map_mul, map_inv, map_inv]
              group
          _ = diagT E (Fin n) (t * s) := by
              rw [he]
              group
      obtain ⟨u, hu⟩ := strictNormal E n σ q hc d (t * s) hd hts _ hx
      have h2 : u⁻¹ * d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u = t * s := by
        apply UpperTheory.Gal.InertialTypesAlt.L.diag_inj
        rw [map_mul, map_mul, map_inv, ← UpperTheory.Gal.InertialTypesAlt.L.sg_diag, ← hu]
        exact hx
      refine ⟨u, ⟨t, ht, ?_⟩, k, hk, ?_⟩
      · have h3 : d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t = s := by
          calc d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t = (u⁻¹ * d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u) / t := by
                simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
            _ = s := by
                rw [h2]
                simp
        rw [h3]
        exact hs
      · rw [← hu]
        group
    · rintro ⟨u, ⟨t, ht, hs⟩, κ, hκ, rfl⟩
      have hid : u⁻¹ * d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u = t * (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t) := by
        rw [mul_comm t, div_mul_cancel, div_eq_mul_inv, mul_comm (d * _) u⁻¹, mul_assoc]
      have hδ : δ = y * diagT E (Fin n) d * (sg σ y)⁻¹ := by
        rw [← hy]
        group
      refine ⟨κ⁻¹, binv κ hκ, diagT E (Fin n) (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t) * sg σ κ,
        bmul _ (UpperTheory.Gal.InertialTypesAlt.L.diag_ball hs) _ (UpperTheory.Gal.InertialTypesAlt.L.ball_sg hσ hκ), t, ht, ?_⟩
      rw [hδ]
      calc (y * diagT E (Fin n) u * κ)⁻¹ * (y * diagT E (Fin n) d * (sg σ y)⁻¹)
            * sg σ (y * diagT E (Fin n) u * κ)
          = κ⁻¹ * ((diagT E (Fin n) u)⁻¹ * diagT E (Fin n) d * sg σ (diagT E (Fin n) u)) * sg σ κ := by
            rw [map_mul, map_mul]
            group
        _ = κ⁻¹ * (diagT E (Fin n) t * diagT E (Fin n) (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t)) * sg σ κ := by
            rw [UpperTheory.Gal.InertialTypesAlt.L.sg_diag, ← map_inv (diagT E (Fin n)) u, ← map_mul, ← map_mul, ← map_mul, hid]
        _ = κ⁻¹ * diagT E (Fin n) t * (diagT E (Fin n) (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t) * sg σ κ) := by
            group
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.VolRatio
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem mem_diag (g : GL (Fin n) k) :
    g ∈ (diagT k (Fin n)).range ↔ ∀ i j, i ≠ j → (g : Matrix (Fin n) (Fin n) k) i j = 0 := by
  constructor
  · rintro ⟨t, rfl⟩ i j hij
    rw [val_diagT, diagonal_apply_ne _ hij]
  · intro h
    have hd : (g : Matrix (Fin n) (Fin n) k) = diagonal fun i => (g : Matrix (Fin n) (Fin n) k) i i := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · rw [diagonal_apply_ne _ hij, h i j hij]
    have hdet : (g : Matrix (Fin n) (Fin n) k).det ≠ 0 := g.isUnit.map Matrix.detMonoidHom |>.ne_zero
    have hne : ∀ i, (g : Matrix (Fin n) (Fin n) k) i i ≠ 0 := by
      intro i
      rw [hd, det_diagonal] at hdet
      exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ i)
    refine ⟨fun i => Units.mk0 _ (hne i), ?_⟩
    ext : 1
    rw [val_diagT]
    simp only [Units.val_mk0]
    exact hd.symm

private theorem isClosed_diag : IsClosed ((diagT k (Fin n)).range : Set (GL (Fin n) k)) := by
  haveI := GroundTheory.LocalField.t2Space_of_isNonarchimedeanLocalField k
  have he : ((diagT k (Fin n)).range : Set (GL (Fin n) k)) =
      Units.val ⁻¹' {M : Matrix (Fin n) (Fin n) k | ∀ i j, i ≠ j → M i j = 0} := by
    ext g
    exact mem_diag g
  rw [he]
  refine IsClosed.preimage Units.continuous_val ?_
  simp only [Set.setOf_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
  exact (continuous_apply j).comp (continuous_apply i)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem sg_refl (g : GL (Fin n) k) : sg (RingEquiv.refl k) g = g := by
  ext i j
  simp [sg]

private theorem cent_diag {γ y : GL (Fin n) k} {x : Fin n → kˣ} (hx : Strict x)
    (hy : y⁻¹ * γ * y = diagT k (Fin n) x) {t : GL (Fin n) k} (ht : t ∈ Subgroup.centralizer {γ}) :
    y⁻¹ * t * y ∈ (diagT k (Fin n)).range := by
  have hc : γ * t = t * γ := Subgroup.mem_centralizer_iff.1 ht γ (Set.mem_singleton γ)
  have hcyc : Cyc (RingEquiv.refl k) 1 := ⟨fun _ => rfl, one_pos, fun _ => rfl⟩
  have hz : (y⁻¹ * t * y)⁻¹ * diagT k (Fin n) x * sg (RingEquiv.refl k) (y⁻¹ * t * y) =
      diagT k (Fin n) x := by
    rw [sg_refl, ← hy]
    simp only [_root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
    rw [← mul_assoc γ t y, hc, mul_assoc t, inv_mul_cancel_left]
  obtain ⟨s, hs⟩ := strictNormal k n (RingEquiv.refl k) 1 hcyc x x hx hx _ hz
  exact ⟨s, hs.symm⟩

end

theorem UpperTheory.Gal.InertialTypesAlt.L.volRatio :
    UpperTheory.Gal.InertialTypesAlt.L.VolRatio := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hgen n _ _ r r' hr0 hr1 hr0' hr1' hrr'
  haveI : T2Space k := GroundTheory.LocalField.t2Space_of_isNonarchimedeanLocalField k
  have hemb : Topology.IsClosedEmbedding (incl : GL (Fin n) k →* GL (Fin n) E) :=
    ((bridge k E σ).2.2 n).2.2.2.1
  obtain ⟨KE, hKE, -, -⟩ := ballSub E n r hr0 hr1
  obtain ⟨Kk, hKk, hKko, -⟩ := ballSub k n r' hr0' hr1'
  set D : Subgroup (GL (Fin n) k) := (diagT k (Fin n)).range with hD
  set Cr : Subgroup (GL (Fin n) k) := D ⊓ KE.comap (incl : GL (Fin n) k →* GL (Fin n) E) with hCr
  set Hr : Subgroup (GL (Fin n) k) := D ⊓ Kk with hHr
  have hincl : ∀ (g : GL (Fin n) k) (i j : Fin n),
      ((incl g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j = algebraMap k E ((g : Matrix (Fin n) (Fin n) k) i j) := by
    intro g i j
    rfl
  have hHC : Hr ≤ Cr := by
    rintro d ⟨⟨s, rfl⟩, hd⟩
    refine ⟨⟨s, rfl⟩, ?_⟩
    have hd' : diagT k (Fin n) s ∈ ball n r' := by
      rw [← hKk]
      exact hd
    show incl (diagT k (Fin n) s) ∈ KE
    rw [← SetLike.mem_coe, hKE]
    intro i j
    rw [hincl, val_diagT]
    by_cases hij : i = j
    · subst hij
      have h1 := hd' i i
      rw [val_diagT] at h1
      simpa using hrr' (s i) (by simpa using h1)
    · simp [diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hCrc : IsCompact (Cr : Set (GL (Fin n) k)) := by
    have h1 : IsCompact ((incl : GL (Fin n) k →* GL (Fin n) E) ⁻¹' (KE : Set (GL (Fin n) E))) :=
      hemb.isCompact_preimage (by rw [hKE]; exact BallG.isCompact_ball hr1)
    exact h1.inter_left isClosed_diag
  have hidx : Hr.relIndex Cr ≠ 0 := by
    haveI : CompactSpace Cr := isCompact_iff_compactSpace.mp hCrc
    have hopen : IsOpen ((Hr.subgroupOf Cr : Subgroup Cr) : Set Cr) := by
      have he : ((Hr.subgroupOf Cr : Subgroup Cr) : Set Cr) = Subtype.val ⁻¹' (Kk : Set (GL (Fin n) k)) := by
        ext g
        simp only [Subgroup.coe_subgroupOf, Set.mem_preimage, SetLike.mem_coe]
        exact ⟨fun h => h.2, fun h => ⟨g.2.1, h⟩⟩
      rw [he]
      exact continuous_subtype_val.isOpen_preimage _ hKko
    haveI := Subgroup.quotient_finite_of_isOpen _ hopen
    exact Subgroup.index_ne_zero_of_finite
  refine ⟨(Hr.relIndex Cr : ℝ), Nat.cast_pos.2 (Nat.pos_of_ne_zero hidx), ?_⟩
  intro γ y x hx hy ν hν
  let c : GL (Fin n) k →* GL (Fin n) k :=
    { toFun := fun g => y⁻¹ * g * y
      map_one' := by simp
      map_mul' := by
        intro a b
        group }
  have hcs : Function.Surjective c := fun g => ⟨y * g * y⁻¹, by simp [c, mul_assoc]⟩
  set C : Subgroup (GL (Fin n) k) := Cr.comap c with hC
  set H : Subgroup (GL (Fin n) k) := Hr.comap c with hH
  have hTc : IsClosed ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) :=
    Set.isClosed_centralizer _
  have hCT : C ≤ Subgroup.centralizer {γ} := by
    intro g hg
    obtain ⟨s, hs⟩ := hg.1
    rw [Subgroup.mem_centralizer_iff]
    rintro h rfl
    have hγ : h = y * diagT k (Fin n) x * y⁻¹ := by
      rw [← hy]
      group
    have hg' : g = y * diagT k (Fin n) s * y⁻¹ := by
      rw [hs]
      simp only [c, MonoidHom.coe_mk, OneHom.coe_mk]
      group
    rw [hγ, hg']
    simp only [mul_assoc, inv_mul_cancel_left]
    congr 1
    rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, mul_comm]
  have hCc : IsCompact (C : Set (GL (Fin n) k)) :=
    ((Homeomorph.mulLeft y⁻¹).trans (Homeomorph.mulRight y)).isCompact_preimage.2 hCrc
  have hcD : ∀ t : Subgroup.centralizer {γ}, c t ∈ D := fun t => cent_diag hx hy t.2
  have hHo : IsOpen {t : Subgroup.centralizer {γ} | (t : GL (Fin n) k) ∈ H} := by
    have he : {t : Subgroup.centralizer {γ} | (t : GL (Fin n) k) ∈ H} =
        (fun t : Subgroup.centralizer {γ} => y⁻¹ * (t : GL (Fin n) k) * y) ⁻¹' (Kk : Set (GL (Fin n) k)) := by
      ext t
      exact ⟨fun h => h.2, fun h => ⟨hcD t, h⟩⟩
    rw [he]
    exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).isOpen_preimage _ hKko
  have hv := (volIdx (GL (Fin n) k) (Subgroup.centralizer {γ}) C H hTc ν hν hCT hCc
    (Subgroup.comap_mono hHC) hHo).2
  have hri : H.relIndex C = Hr.relIndex Cr := by
    rw [hH, hC, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hcs]
  have e1 : {t : Subgroup.centralizer {γ} | incl (y⁻¹ * (t : GL (Fin n) k) * y) ∈ ball n r} =
      {t : Subgroup.centralizer {γ} | (t : GL (Fin n) k) ∈ C} := by
    ext t
    show _ ↔ c t ∈ D ∧ incl (c t) ∈ KE
    rw [← SetLike.mem_coe (p := KE), hKE]
    exact ⟨fun h => ⟨hcD t, h⟩, fun h => h.2⟩
  have e2 : {t : Subgroup.centralizer {γ} | y⁻¹ * (t : GL (Fin n) k) * y ∈ ball n r'} =
      {t : Subgroup.centralizer {γ} | (t : GL (Fin n) k) ∈ H} := by
    ext t
    show _ ↔ c t ∈ D ∧ c t ∈ Kk
    rw [← SetLike.mem_coe (p := Kk), hKk]
    exact ⟨fun h => ⟨hcD t, h⟩, fun h => h.2⟩
  rw [e1, e2, hv, hri]
end
end

