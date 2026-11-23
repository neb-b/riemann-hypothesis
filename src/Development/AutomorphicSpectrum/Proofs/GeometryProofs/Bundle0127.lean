module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0104
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0066
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.DivMemLineLat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsHolomorphicChartAtPoint
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0050

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DetLatticeLineBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.DetLine

theorem matrix_eq_mul {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {r : ℕ} {b₀ c b : Fin r → E}
    {T T' A : Matrix (Fin r) (Fin r) Ω} (hb₀ : LinearIndependent Ω b₀)
    (hT : ∀ k, c k = ∑ k', T k' k • b₀ k') (hT' : ∀ k, b k = ∑ k', T' k' k • b₀ k')
    (hA : ∀ k, b k = ∑ i, A i k • c i) : T' = T * A := by
  ext i k
  have h : ∑ k', (T' k' k - (T * A) k' k) • b₀ k' = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, Matrix.mul_apply, Finset.sum_smul, ← hT']
    rw [sub_eq_zero, hA k, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT j, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_smul, _root_.mul_comm]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hb₀ _ h i)

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

theorem det_mem_span (L : Lat ξ E) {r : ℕ} {b₀ c b : Fin r → E} {q : Cpt ξ} {T T' : Matrix (Fin r) (Fin r) Ω}
    (hb₀ : LinearIndependent Ω b₀) (hc : L.IsFrameAt c q) (hb : L.IsFrameAt b q)
    (hT : ∀ k, c k = ∑ k', T k' k • b₀ k') (hT' : ∀ k, b k = ∑ k', T' k' k • b₀ k') :
    T'.det ∈ Submodule.span (regAt ξ q) {T.det} := by
  have hmem : ∀ k, b k ∈ Submodule.span (regAt ξ q) (Set.range c) := fun k => by
    rw [← hc.2, hb.2]
    exact Submodule.subset_span ⟨k, rfl⟩
  choose a ha using fun k => (Submodule.mem_span_range_iff_exists_fun (regAt ξ q)).1 (hmem k)
  let M : Matrix (Fin r) (Fin r) (regAt ξ q) := Matrix.of fun i k => a k i
  have hM : T' = T * (regAt ξ q).subtype.mapMatrix M :=
    matrix_eq_mul hb₀ hT hT' fun k => (ha k).symm
  refine Submodule.mem_span_singleton.2 ⟨M.det, ?_⟩
  rw [hM, Matrix.det_mul, ← RingHom.map_det, _root_.mul_comm]
  rfl

theorem isVB_detLat : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E]
    (L : Lat ξ E) (r : ℕ) (V : Submodule Ω E) (b₀ : Fin r → E), LinearIndependent Ω b₀ →
    Submodule.span Ω (Set.range b₀) = V → L.IsVB r V → (Cusp.detLat L b₀).IsVB 1 ⊤ := by
  intro X Ω _ ξ E _ _ L r V b₀ hb₀ hsp hL p _
  obtain ⟨U, hU, c, hc, hf⟩ := hL p trivial
  have hcV : ∀ k, c k ∈ Submodule.span Ω (Set.range b₀) := fun k => by
    rw [hsp, ← hc]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hbV : ∀ k, b₀ k ∈ Submodule.span Ω (Set.range c) := fun k => by
    rw [hc, ← hsp]
    exact Submodule.subset_span ⟨k, rfl⟩
  choose a ha using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hcV k)
  choose s hs using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hbV k)
  let T : Matrix (Fin r) (Fin r) Ω := Matrix.of fun i k => a k i
  let S : Matrix (Fin r) (Fin r) Ω := Matrix.of fun i k => s k i
  have hT : ∀ k, c k = ∑ k', T k' k • b₀ k' := fun k => (ha k).symm
  have hTS : (1 : Matrix (Fin r) (Fin r) Ω) = T * S :=
    matrix_eq_mul hb₀ hT (fun k => by simp [Matrix.one_apply, ite_smul]) fun k => (hs k).symm
  have ht : T.det ≠ 0 := fun h => by
    have := congrArg Matrix.det hTS
    rw [Matrix.det_one, Matrix.det_mul, h, zero_mul] at this
    exact one_ne_zero this
  refine ⟨U, hU, fun _ => T.det, ?_, fun q _ hq => ⟨?_, ?_⟩⟩
  · refine eq_top_iff.2 fun x _ => ?_
    have hx : x = (x * T.det⁻¹) • T.det := by
      rw [smul_eq_mul, _root_.mul_assoc, inv_mul_cancel₀ ht, _root_.mul_one]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  · exact linearIndependent_unique_iff.2 ht
  · have hr : Set.range (fun _ : Fin 1 => T.det) = {T.det} := Set.range_const
    rw [hr]
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨b, T', hfr, hT', rfl⟩
      exact det_mem_span L hb₀ (hf q trivial hq) hfr hT hT'
    · rintro _ rfl
      exact ⟨c, T, hf q trivial hq, hT, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.DetLine
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DimensionPlusFlagCount
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

namespace GlobalTheory.CompanionTheory.Ar.FlagStep

theorem card_strictLower (n : ℕ) [Fintype {lk : Fin n × Fin n // lk.2 < lk.1}] :
    Fintype.card {lk : Fin n × Fin n // lk.2 < lk.1} = n.choose 2 := by
  let e : {lk : Fin n × Fin n // lk.2 < lk.1} ≃ Σ i : Fin n, Fin i.val :=
    { toFun := fun x => ⟨x.1.1, ⟨x.1.2.val, x.2⟩⟩
      invFun := fun y => ⟨(y.1, ⟨y.2.val, y.2.2.trans y.1.2⟩), y.2.2⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id, Nat.choose_two_right]

theorem choose_two_add (p q : ℕ) :
    (p + q).choose 2 = p * q + p.choose 2 + q.choose 2 := by
  induction q with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Nat.choose_succ_succ' (p + k) 1, Nat.choose_succ_succ' k 1, ih,
      Nat.choose_one_right, Nat.choose_one_right]
    ring

theorem dim_add_card_strictLower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H)
    (c : Coeff l) [Fintype (CMType H)] [Fintype (Σ s : CMType H ⊕ CMType H, {lk : Fin (labelRk D s) × Fin (labelRk D s) // lk.2 < lk.1})],
    D.dim + Fintype.card (Σ s : CMType H ⊕ CMType H, {lk : Fin (labelRk D s) × Fin (labelRk D s) // lk.2 < lk.1}) =
      Top.dimFl (CMType H) (D.p + D.q) := by
  intro E _ _ _ H D l c _ _
  have hc : 2 * Fintype.card (CMType H) = Module.finrank ℚ E := by
    have h := (GlobalTheory.CompanionTheory.Ar.labels_all_once E H l c).2
    rw [Nat.card_eq_fintype_card, Fintype.card_sum] at h
    omega
  have hs : Fintype.card (Σ s : CMType H ⊕ CMType H,
      {lk : Fin (labelRk D s) × Fin (labelRk D s) // lk.2 < lk.1}) =
      Fintype.card (CMType H) * D.p.choose 2 + Fintype.card (CMType H) * D.q.choose 2 := by
    classical
    rw [← Nat.card_eq_fintype_card, Nat.card_sigma, Fintype.sum_sum_type]
    simp only [Nat.card_eq_fintype_card]
    rw [Finset.sum_congr rfl (fun a _ => card_strictLower (labelRk D (Sum.inl a))),
      Finset.sum_congr rfl (fun a _ => card_strictLower (labelRk D (Sum.inr a)))]
    simp only [labelRk, Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [hs, Top.dimFl, Datum.dim, ← hc, ← Nat.choose_two_right, choose_two_add,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  ring

end GlobalTheory.CompanionTheory.Ar.FlagStep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EmbedsGenericOfCharZero
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.EmbedsOfTie

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem isLocalRing_regAt {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) (p : Cpt ξ) :
    IsLocalRing (regAt ξ p) := by
  unfold regAt
  exact IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective

theorem unitAt_iff_isUnit {ξ : Spec (CommRingCat.of Ω) ⟶ X} (p : Cpt ξ) (s : regAt ξ p) :
    unitAt ξ p (s : Ω) ↔ IsUnit s := by
  constructor
  · rintro ⟨h0, -, hinv⟩
    refine isUnit_iff_exists_inv.mpr ⟨⟨(s : Ω)⁻¹, hinv⟩, ?_⟩
    exact Subtype.ext (mul_inv_cancel₀ h0)
  · intro hs
    obtain ⟨t, ht⟩ := isUnit_iff_exists_inv.mp hs
    have ht' : (s : Ω) * (t : Ω) = 1 := by simpa using congrArg Subtype.val ht
    have h0 : (s : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one ht'
    refine ⟨h0, s.2, ?_⟩
    rw [inv_eq_of_mul_eq_one_right ht']
    exact t.2

theorem mem_adjoin_rat_of_int [CharZero Ω] {S : Set Ω} {a : Ω} (h : a ∈ Algebra.adjoin ℤ S) :
    a ∈ Algebra.adjoin ℚ S := by
  induction h using Algebra.adjoin_induction with
  | mem y hy => exact Algebra.subset_adjoin hy
  | algebraMap r =>
    rw [eq_intCast (algebraMap ℤ Ω) r]
    exact intCast_mem _ r
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

theorem embedsGeneric_of_coordTie : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → EmbedsGeneric ξ x := by
  intro X Ω _ _ ξ κ x h
  unfold EmbedsGeneric
  intro p _
  refine ⟨h.cover p, fun i hi => ⟨?_, ?_⟩⟩
  · intro a ha
    obtain ⟨s, hs, hu, hsa⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x h i p hi a).mp ha
    exact ⟨s, mem_adjoin_rat_of_int hs, hu, mem_adjoin_rat_of_int hsa⟩
  · intro q _ hq hpq
    haveI := isLocalRing_regAt h.gen p
    have hmem : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x i), a ∈ regAt ξ p :=
      fun a ha => (h.ring i hi.1 a).mp ha p hi
    let φ : Algebra.adjoin ℤ (Set.range fun j => x j / x i) →+* regAt ξ p :=
      { toFun := fun s => ⟨s, hmem s s.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    let I : Ideal (Algebra.adjoin ℤ (Set.range fun j => x j / x i)) :=
      Ideal.comap φ (IsLocalRing.maximalIdeal (regAt ξ p))
    have hI : I.IsPrime := Ideal.comap_isPrime φ _
    have key : ∀ s : Algebra.adjoin ℤ (Set.range fun j => x j / x i), s ∉ I ↔ unitAt ξ p (s : Ω) := by
      intro s
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
      exact (unitAt_iff_isUnit p (φ s)).symm
    obtain ⟨p', -, huniq⟩ := _root_.GlobalTheory.CompanionTheory.Ar.chart_point_of_prime X Ω ξ ℤ κ x h i hi.1 I hI
    have e1 := huniq p ⟨hi, key⟩
    have e2 := huniq q ⟨hq, fun s => (key s).trans (hpq s (mem_adjoin_rat_of_int s.2))⟩
    exact e1.trans e2.symm

end GlobalTheory.CompanionTheory.Ar.EmbedsOfTie
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagBundleUnderEquiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagStep

theorem flagStep_linearEquiv_image {Ω F F' : Type} [Field Ω] [AddCommGroup F] [Module Ω F] [AddCommGroup F']
    [Module Ω F'] (Φ : F ≃ₗ[Ω] F') {r : ℕ} (d : Fin r → F) (i : ℕ) :
    flagStep Ω (fun k => Φ (d k)) i = (flagStep Ω d i).map Φ.toLinearMap := by
  unfold flagStep
  rw [Submodule.map_span, ← Set.image_comp]
  rfl

theorem isFlagVBOn_pull_map : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (E F F' : Type)
    [AddCommGroup E] [Module Ω₀ E] [AddCommGroup F] [Module Ω F] [AddCommGroup F'] [Module Ω F']
    (L : Lat ξ E) (j : E →+ F) (Φ : F ≃ₗ[Ω] F') (T : Set (Cpt ξ')) (r : ℕ) (b : Fin r → F),
    (L.pull ξ' f j).IsFlagVBOn T b →
    (L.pull ξ' f (Φ.toLinearMap.toAddMonoidHom.comp j)).IsFlagVBOn T (fun k => Φ (b k)) := by
  intro X X' Ω₀ Ω _ _ ξ ξ' f E F F' _ _ _ _ _ _ L j Φ T r b h
  unfold Lat.IsFlagVBOn at h ⊢
  intro p hp
  obtain ⟨U, hpU, c, hc, hframe⟩ := h p hp
  refine ⟨U, hpU, fun k => Φ (c k), fun i => ?_, fun q hq hqU => ?_⟩
  · rw [flagStep_linearEquiv_image, flagStep_linearEquiv_image, hc i]
  · have hq' := hframe q hq hqU
    unfold Lat.IsFrameAt at hq' ⊢
    obtain ⟨hli, hsp⟩ := hq'
    refine ⟨hli.map' Φ.toLinearMap Φ.ker, ?_⟩
    let φ : F →ₗ[regAt ξ' q] F' := Φ.toLinearMap.restrictScalars (regAt ξ' q)
    unfold Lat.pull at hsp ⊢
    rw [show Set.range (fun k => Φ (c k)) = φ '' Set.range c from Set.range_comp φ c]
    rw [← Submodule.map_span φ, ← hsp, Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨h, e, he, rfl⟩
      exact ⟨j e, ⟨h, e, he, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨h, e, he, rfl⟩, rfl⟩
      exact ⟨h, e, he, rfl⟩

end GlobalTheory.CompanionTheory.Ar.FlagStep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagCmTypeLatticeComparison
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptWedge

section LinAlg

variable {Ω₀ Ω V₀ V : Type} [Field Ω₀] [Field Ω] [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V] [Module Ω V]

theorem exists_wedge_eq_smul {n : ℕ} {e b : Fin n → V} (h : ∀ k, e k ∈ Submodule.span Ω (Set.range b)) :
    ∃ d : Ω, exteriorPower.ιMulti Ω n e = d • exteriorPower.ιMulti Ω n b := by
  choose T hT using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (h k)
  have he : e = fun k => ∑ l, (Matrix.of T) k l • b l := funext fun k => (hT k).symm
  exact ⟨(Matrix.of T).det, by rw [he]; exact GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family Ω V n b _⟩

theorem isPullWedge_smul_ιMulti (i : Ω₀ →+* Ω) (j : V₀ →+ V) (hj : IsExtOver i j) {n : ℕ} {u : Fin n → V₀}
    (hu : LinearIndependent Ω₀ u) {γ : Ω₀} (hγ : γ ≠ 0) :
    CptIn.IsPullWedge i j (γ • exteriorPower.ιMulti Ω₀ n u)
      (i γ • exteriorPower.ιMulti Ω n fun k => j (u k)) := by
  intro b α hab
  have hw := WedgeFrame.ιMulti_ne_zero hu
  have hα : α ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hab
    exact smul_ne_zero hγ hw hab
  have hbe : exteriorPower.ιMulti Ω₀ n b = (α⁻¹ * γ) • exteriorPower.ιMulti Ω₀ n u := by
    rw [mul_smul, hab, smul_smul, inv_mul_cancel₀ hα, one_smul]
  have hm := GlobalTheory.CompanionTheory.WedgeSpan.span_of_wedge_proportional Ω₀ V₀ n b u _ hu (mul_ne_zero (inv_ne_zero hα) hγ) hbe
  choose T hT using fun k => (Submodule.mem_span_range_iff_exists_fun Ω₀).1 (hm k)
  have hb : b = fun k => ∑ l, (Matrix.of T) k l • u l := funext fun k => (hT k).symm
  have h1 : exteriorPower.ιMulti Ω₀ n b = (Matrix.of T).det • exteriorPower.ιMulti Ω₀ n u := by
    rw [hb]; exact GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family Ω₀ V₀ n u _
  have h2 : γ = α * (Matrix.of T).det := by
    rw [h1, smul_smul] at hab
    exact smul_left_injective Ω₀ hw hab
  have h3 : (fun k => j (b k)) = fun k => ∑ l, (i.mapMatrix (Matrix.of T)) k l • j (u l) := by
    funext k
    rw [hb]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, hj.1]
    rfl
  rw [h3, GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family Ω V n _ _, ← RingHom.map_det, smul_smul, ← map_mul, ← h2]

end LinAlg

theorem exists_eq_smul_ιMulti {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type}
    [AddCommGroup E] [Module Ω E] {L : Lat ξ E} {r : ℕ} {u : Fin r → E} {x : Cpt ξ} (hu : L.IsFrameAt u x)
    {a : ⋀[Ω]^r E} {α : Ω} (hα : α ≠ 0) (hw : L.wedge r x = Submodule.span (regAt ξ x) {α • a}) :
    ∃ γ : Ω, γ ≠ 0 ∧ a = γ • exteriorPower.ιMulti Ω r u := by
  obtain ⟨h1, h2⟩ := WedgeFrame.wedge_eq_span_ιMulti X Ω ξ E L r u x hu
  have h3 : exteriorPower.ιMulti Ω r u ∈ Submodule.span (regAt ξ x) {α • a} := by
    rw [← hw, h1]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 h3
  have ht' : ((t : Ω) * α) • a = exteriorPower.ιMulti Ω r u := by
    rw [mul_smul]; exact ht
  have ht0 : (t : Ω) * α ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at ht'
    exact h2 ht'.symm
  exact ⟨((t : Ω) * α)⁻¹, inv_ne_zero ht0, by rw [← ht', smul_smul, inv_mul_cancel₀ ht0, one_smul]⟩

section Comparison₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {U : Set (Xo.XF c)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω}

theorem tie_act {Z : CptOver Y U} {𝔐 : HodgeCpt Y S y} {i : Z.Ω →+* Ω} {j : Z.V →+ 𝔐.Li}
    (h : CptIn.IsTie Z 𝔐 i j) (a : 𝓞 E) (e : Z.V) : j (Z.ρ a e) = 𝔐.ρ a (j e) := by
  obtain ⟨-, -, -, h4⟩ := h
  refine 𝔐.M.inj (Over.OverMorphism.ext (𝔐.m.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)))
  rw [h4, Z.act a e, 𝔐.act a (j e), Over.comp_left, Over.comp_left, Category.assoc, 𝔐.m.act, ← Category.assoc]
  exact (congrArg (· ≫ Over.Hom.left (Y.t.act.act a)) (h4 e).symm).trans (Category.assoc _ _ _)

theorem tie_mem_eigSp {Z : CptOver Y U} {𝔐 : HodgeCpt Y S y} {i : Z.Ω →+* Ω} {j : Z.V →+ 𝔐.Li}
    (h : CptIn.IsTie Z 𝔐 i j) (σ : 𝓞 E →+* c.F) {e : Z.V} (he : e ∈ eigSp Z.ρ (Z.inc.comp σ)) :
    j e ∈ eigSp 𝔐.ρ (𝔐.cst.comp σ) := by
  have hi := h.2.1
  have hs := h.2.2.1.1
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at he ⊢
  intro a
  rw [← tie_act h, he a, hs, ← hi]
  rfl

theorem exists_side {Z : CptOver Y U} {𝔐 : HodgeCpt Y S y} {i : Z.Ω →+* Ω} {j : Z.V →+ 𝔐.Li}
    (h : CptIn.IsTie Z 𝔐 i j) {L : Lat (Z.ξ₀ ≫ Y.j) Z.V} {r : ℕ} {u : Fin r → Z.V} {x : Cpt (Z.ξ₀ ≫ Y.j)}
    (hu : L.IsFrameAt u x) {a : ⋀[Z.Ω]^r Z.V} {α : Z.Ω} (hα : α ≠ 0)
    (hw : L.wedge r x = Submodule.span (regAt (Z.ξ₀ ≫ Y.j) x) {α • a}) {B : Fin r → 𝔐.Li}
    (hB : ∀ k, j (u k) ∈ Submodule.span Ω (Set.range B)) :
    ∃ (a' : ⋀[Ω]^r 𝔐.Li) (d : Ω), d ≠ 0 ∧ a' ≠ 0 ∧ CptIn.IsPullWedge i j a a' ∧
      a' = d • exteriorPower.ιMulti Ω r B := by
  obtain ⟨γ, hγ, rfl⟩ := exists_eq_smul_ιMulti hu hα hw
  have hj : IsExtOver i j := h.2.2.1
  have hind : LinearIndependent Ω fun k => j (u k) := hj.2 r u hu.1
  have hne := WedgeFrame.ιMulti_ne_zero hind
  obtain ⟨d, hd⟩ := exists_wedge_eq_smul hB
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hd
    exact hne hd
  have hiγ : i γ ≠ 0 := (map_ne_zero i).2 hγ
  exact ⟨_, i γ * d, mul_ne_zero hiγ hd0, smul_ne_zero hiγ hne, isPullWedge_smul_ιMulti i j hj hu.1 hγ,
    by rw [hd, smul_smul]⟩

end Comparison₂

theorem exists_pullWedge_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (τ : CMType H) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V), CptIn.IsTie Z 𝔐 i j → IsLineGenOn (Z.eig τ.1) (Z.eig (ComplexEmbedding.conjugate τ.1)) D.p D.q a b Z.genFib → ∃ (a' : ⋀[Ω]^D.p 𝔐.Li) (b' : ⋀[Ω]^D.q 𝔐.Li) (d₁ d₂ : Ω), d₁ ≠ 0 ∧ d₂ ≠ 0 ∧ a' ≠ 0 ∧ b' ≠ 0 ∧ CptIn.IsPullWedge i j a a' ∧ CptIn.IsPullWedge i j b b' ∧ a' = d₁ • (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) ∧ b' = d₂ • (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))) := by
  intro E _ _ _ H D l Xo c _ Y U Z S Ω _ K _ J _ y 𝔐 Fl τ i j a b hT hL
  have hfr : ∀ x : c.F, ∃ a b : 𝓞 c.F, algebraMap (𝓞 c.F) c.F b ≠ 0 ∧
      x * algebraMap (𝓞 c.F) c.F b = algebraMap (𝓞 c.F) c.F a := by
    intro x
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 c.F)) x
    exact ⟨a, b, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2, hab⟩
  obtain ⟨h1, h2, -, x, hx⟩ := isVBOn_eig_genFib E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y U Z τ.1
    ⟨FaithfulSMul.algebraMap_injective _ _, inferInstance, hfr⟩ τ.2
  obtain ⟨-, -, hg⟩ := hL
  obtain ⟨α, β, hα, hβ, hwa, hwb, -⟩ := hg x hx
  obtain ⟨W₁, hW₁, u₁, hs₁, hf₁⟩ := h1 x hx
  obtain ⟨W₂, hW₂, u₂, hs₂, hf₂⟩ := h2 x hx
  have hu₁ := hf₁ x hx hW₁
  have hu₂ := hf₂ x hx hW₂
  have hB₁ : ∀ k, j (u₁ k) ∈ Submodule.span Ω (Set.range (Fl.b (.inl τ))) := fun k => by
    rw [HodgeCptTest.flag_span 𝔐 Fl]
    have hk : u₁ k ∈ eigSp Z.ρ (Z.inc.comp (tauIn c τ.1)) := hs₁ ▸ Submodule.subset_span ⟨k, rfl⟩
    have := tie_mem_eigSp hT _ hk
    rwa [← CptInputs.labelEmb_inl] at this
  have hB₂ : ∀ k, j (u₂ k) ∈ Submodule.span Ω (Set.range (Fl.b (.inr τ))) := fun k => by
    rw [HodgeCptTest.flag_span 𝔐 Fl]
    have hk : u₂ k ∈ eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ.1))) :=
      hs₂ ▸ Submodule.subset_span ⟨k, rfl⟩
    have := tie_mem_eigSp hT _ hk
    rwa [← CptInputs.labelEmb_inr] at this
  obtain ⟨a', d₁, hd₁, ha', hpa, hea⟩ := exists_side hT hu₁ hα hwa (B := Fl.b (.inl τ)) hB₁
  obtain ⟨b', d₂, hd₂, hb', hpb, heb⟩ := exists_side hT hu₂ hβ hwb (B := Fl.b (.inr τ)) hB₂
  exact ⟨a', b', d₁, d₂, hd₁, hd₂, ha', hb', hpa, hpb, hea, heb⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CptWedge
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicAffinePolydiscChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem hol_polydisc_chart : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (d : ℕ) (T : Set X), SmoothOfRelativeDimension d s → Geo.ResK.HasSncCoords s d T → ∀ (x : Sp ℂ ⟶ X) (W : X.Opens), x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → ∃ (V : X.Opens) (hV : IsAffineOpen V) (a : ℕ) (ψ : (Fin d → ℂ) → (Γ(X, V) →+* ℂ)), V ≤ W ∧ a ≤ d ∧ IsHolPts (ball 0 1) ψ ∧ spMap (ψ 0) ≫ hV.fromSpec = x ∧ Set.InjOn ψ (ball 0 1) ∧ (∀ z ∈ ball (0 : Fin d → ℂ) 1, spMap (ψ z) ≫ hV.fromSpec ≫ s = spMap σ ∧ (centre (spMap (ψ z) ≫ hV.fromSpec) ∉ T ↔ z ∈ punct d a 1)) ∧ ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsHolTo B y → (∀ b ∈ B, y b ≫ s = spMap σ) → ∀ b₀ ∈ B, y b₀ = x → ∃ (ε : ℝ) (κ : (Fin m → ℂ) → (Fin d → ℂ)), 0 < ε ∧ ball b₀ ε ⊆ B ∧ DifferentiableOn ℂ κ (ball b₀ ε) ∧ κ b₀ = 0 ∧ ∀ b ∈ ball b₀ ε, κ b ∈ ball (0 : Fin d → ℂ) 1 ∧ y b = spMap (ψ (κ b)) ≫ hV.fromSpec :=
  @PositivityTheory.Xgn.exists_holomorphic_chart_at_point

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_baseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) E'), ∃ j : E →+ E', (∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M.pt e).left) ∧ (∀ (a : R) e, j (a • e) = algebraMap R R' a • j e) ∧ (Smooth G.hom → ∀ (n : ℕ) (b : Module.Basis (Fin n) R E), LinearIndependent R' (fun k => j (b k)) ∧ Submodule.span R' (Set.range fun k => j (b k)) = ⊤) :=
  PositivityTheory.HtPt.Htat.lie_bc

end GlobalTheory.CompanionTheory.Ar
end

