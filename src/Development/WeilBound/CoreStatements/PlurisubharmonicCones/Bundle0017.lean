module

public import Mathlib
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsUnitOfSum
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0167
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemHodgeDegree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0172
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodDecompositionNearBoundary
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0140
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0091
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.DetLatticeTensorIsDegOnMuTwDeg
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.TiePrimes

namespace LevelTowerAlt

namespace N1

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem}
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {W : CMType H → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} {S₀ : Finset ℕ}

theorem local_frame (Or : CptOrigin Y S₀ Dc Hd) {bb : ∀ τ, Fin Dc.N → W τ}
    {s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li} {lam : Ω}
    (hs : ∀ τ k, s τ k ∈ Or.𝔐.Vgen (Or.sm τ) ∧ Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - s τ k ∈ Or.𝔐.Vgen (Or.bg τ))
    (hΛ : Hd.Λ = lam • PiTensorProduct.tprod Ω (fun τ => quotWedge (Hd.F τ) Dc.j_le_N (bb τ)))
    {q : Cpt Or.𝔐.ξ} {ch : ∀ k, J k} (hq : InChart Or.𝔐.ξ (segreCoord Dc.y) ch q) :
    ∃ (s' : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li)
      (T : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) Ω) (u : Ω),
      (∀ τ, (Or.𝔐.V (Or.sm τ)).IsFrameAt (s' τ) q) ∧ (∀ τ k, s τ k = ∑ k', T τ k' k • s' τ k') ∧
      unitAt Or.𝔐.ξ q u ∧ u * chartMono Dc.y ch Hd.aMu = lam * ∏ τ, (T τ).det := by
  have hT : CoordTie ℤ Or.𝔐.ξ (segreCoord Dc.y) := Or.𝔐.tie
  have hreg := fun a ha => (hT.ring ch hq.1 a).1 ha q hq
  obtain ⟨m, f, cc, hf, hcc, hsum, hl⟩ := Hd.locally ch hq.1
  obtain ⟨i, hi⟩ := exists_unit_of_sum (p := q) (fun i => hreg _ (hf i)) (fun i => hreg _ (hcc i)) hsum
  obtain ⟨b, hb, u, ⟨hu0, ⟨n, hn⟩, n', hn'⟩, hΛ'⟩ := hl i
  have hu : unitAt Or.𝔐.ξ q u := ⟨hu0, mem_of_pow_mul hi (hreg _ hn), mem_of_pow_mul hi (hreg _ hn')⟩
  have hsm : ∀ τ k, ∃ x, x ∈ Or.𝔐.Vgen (Or.sm τ) ∧
      Or.i τ (b τ (tailIdx Dc.j_le_N k)) - x ∈ Or.𝔐.Vgen (Or.bg τ) := fun τ k => by
    have hm : Or.i τ (b τ (tailIdx Dc.j_le_N k)) ∈ Or.𝔐.Vgen (Or.bg τ) ⊔ Or.𝔐.Vgen (Or.sm τ) := by
      rw [← Or.i_range τ]
      exact ⟨_, rfl⟩
    obtain ⟨a, ha, e, he, hae⟩ := Submodule.mem_sup.1 hm
    exact ⟨e, he, by rw [← hae]; simpa using ha⟩
  choose s' hs' using hsm
  have hfr : ∀ τ, (Or.𝔐.V (Or.sm τ)).IsFrameAt (s' τ) q := fun τ => by
    have hrk : labelRk D (Or.bg τ) + labelRk D (Or.sm τ) = Dc.N := by
      rw [Or.rk_bg, Or.rk_sm]
      exact Nat.add_sub_cancel' Dc.j_le_N
    have hsum := _root_.GlobalTheory.CompanionTheory.Ar.HodgeSum.isVB_sup E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 (Or.bg τ) (Or.sm τ) (Or.bg_ne_sm τ τ)
    rw [hrk] at hsum
    have hvb : (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsVB Dc.N ⊤ :=
      BlockSumFrame.isVB_comap_of_range _ _ (Or.i τ) (Or.i_inj τ) (Or.i_range τ) hsum
    have h1 := (_root_.GlobalTheory.CompanionTheory.Ar.isFrameOver_iff_forall_isFrameAt Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y (W τ) Dc.N (Dc.W τ) _ hT hvb (Or.lat τ) ch (f i) (b τ)
      hq.1 (hf i) hi.1).1 (hb τ).1 q hq hi
    exact (_root_.GlobalTheory.CompanionTheory.Ar.BlockFrame.frame_of_sum_frame Or.𝔐.X Ω Or.𝔐.ξ Or.𝔐.Li (W τ) (Or.i τ) (Or.𝔐.V (Or.bg τ)) (Or.𝔐.V (Or.sm τ))
      (Or.𝔐.Vgen (Or.bg τ)) (Or.𝔐.Vgen (Or.sm τ)) Dc.N Dc.j Dc.j_le_N (b τ) (s' τ) q (Or.i_inj τ)
      (Or.i_range τ) (MuIndep.blocks_disjoint Or τ) (fun _ hx => MuIndep.stalk_le_gen _ _ _ hx)
      (fun _ hx => MuIndep.stalk_le_gen _ _ _ hx) h1 (by rw [(hb τ).2.2, Or.F_eq τ]) (hs' τ)).1
  have hq' := fun τ => MuIndep.quot_basis Dc.j_le_N (b := b τ) (F := Hd.F τ) (hb τ).1.2.2.2.1 (hb τ).2.1 (hb τ).2.2
  have hco : ∀ τ k, ∃ t : Fin (Dc.N - Dc.j) → Ω, ∑ a, t a • (Hd.F τ).mkQ (b τ (tailIdx Dc.j_le_N a)) =
      (Hd.F τ).mkQ (bb τ (tailIdx Dc.j_le_N k)) := fun τ k =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (by rw [(hq' τ).2]; trivial)
  choose t ht using hco
  refine ⟨s', fun τ => Matrix.of fun a k => t τ k a, u, hfr, fun τ k => ?_, hu, ?_⟩
  · have h1 : bb τ (tailIdx Dc.j_le_N k) - ∑ a, t τ k a • b τ (tailIdx Dc.j_le_N a) ∈ Hd.F τ := by
      refine (Submodule.Quotient.eq (Hd.F τ)).1 ?_
      have := ht τ k
      simp_rw [← map_smul] at this
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum] at this
      exact this.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Or.F_eq τ, Submodule.mem_comap, map_sub, map_sum] at h1
    rw [← sub_eq_zero]
    refine (Submodule.disjoint_def.1 (MuIndep.blocks_disjoint Or τ)) _ ?_
      (sub_mem (hs τ k).1 (sum_mem fun a _ => Submodule.smul_mem _ _ (hs' τ a).1))
    have e : s τ k - ∑ a, t τ k a • s' τ a =
        (Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - ∑ a, Or.i τ (t τ k a • b τ (tailIdx Dc.j_le_N a))) -
          (Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - s τ k) +
          ∑ a, t τ k a • (Or.i τ (b τ (tailIdx Dc.j_le_N a)) - s' τ a) := by
      simp only [map_smul, smul_sub, Finset.sum_sub_distrib]
      abel
    show s τ k - ∑ a, t τ k a • s' τ a ∈ _
    rw [e]
    exact add_mem (sub_mem h1 (hs τ k).2) (sum_mem fun a _ => Submodule.smul_mem _ _ (hs' τ a).2)
  · exact _root_.GlobalTheory.CompanionTheory.Ar.TopWedge.eq_mul_prod_det (CMType H) Ω (fun τ => W τ ⧸ Hd.F τ) (Dc.N - Dc.j)
      (fun τ a => (Hd.F τ).mkQ (b τ (tailIdx Dc.j_le_N a)))
      (fun τ a => (Hd.F τ).mkQ (bb τ (tailIdx Dc.j_le_N a))) (fun τ => Matrix.of fun a k => t τ k a) _ _
      (fun τ => (hq' τ).1) (fun τ => (hq' τ).2) (fun τ k => (ht τ k).symm) (hΛ'.symm.trans hΛ)

theorem local_change (Or : CptOrigin Y S₀ Dc Hd) (B : ℕ) (hpr : ∀ p ∈ S₀ ∪ Dc.SB B, p.Prime)
    (hvb : ∀ s, (Or.𝔐.VS (S₀ ∪ Dc.SB B) s).IsVB (labelRk D s) (Or.𝔐.Vgen s))
    {q : Cpt Or.𝔐.ξ} {ch : ∀ k, J k} (hq : InChart Or.𝔐.ξ (segreCoord Dc.y) ch q)
    {s' : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li} (hs' : ∀ τ, (Or.𝔐.V (Or.sm τ)).IsFrameAt (s' τ) q) :
    ∃ (b : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li)
      (A : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) Ω),
      (∀ τ, (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)).IsFrameAt (b τ) q) ∧ (∀ τ k, b τ k = ∑ k', A τ k' k • s' τ k') ∧
      unitAt Or.𝔐.ξ q ((∏ τ, (A τ).det) / ∏ p ∈ Dc.SB B,
        (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) * chartMono Dc.y ch (-Dc.vdeg p))) := by
  have hS : ∀ p ∈ Dc.SB B, p ∈ Dc.S := fun p hp => (Finset.mem_filter.1 hp).1
  have patch_values (S : Finset ℕ) (s : CMType H ⊕ CMType H) (hprime : ∀ p ∈ S, p.Prime) :
      ((∀ p ∈ S, ¬ InFibre Or.𝔐.ξ p q) → Lat.patch S (Or.𝔐.dR s) (fun p => Or.𝔐.HT p s) q = Or.𝔐.dR s q) ∧
      ∀ p ∈ S, InFibre Or.𝔐.ξ p q → Lat.patch S (Or.𝔐.dR s) (fun p => Or.𝔐.HT p s) q = Or.𝔐.HT p s q := by
    exact ⟨fun h => Lat.patch_of_not S _ _ h, fun p hp h => Lat.patch_of_unique S _ _ hp h
      fun p' hp' h' => inFibre_unique (hprime p hp) (hprime p' hp') h h'⟩
  have P := fun s => patch_values (S₀ ∪ Dc.SB B) s hpr
  have P₀ := fun s => patch_values S₀ s Or.𝔐.S_prime
  have hoff : ∀ p ∈ Dc.SB B, ¬ InFibre Or.𝔐.ξ p q → unitAt Or.𝔐.ξ q
      (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) * chartMono Dc.y ch (-Dc.vdeg p)) :=
    fun p hp h => unit_off_fibre hq (Dc.vertical p (hS p hp)) h
  by_cases h : ∃ p ∈ Dc.SB B, InFibre Or.𝔐.ξ p q
  · obtain ⟨p, hp, hf⟩ := h
    have hb : ∀ τ, ∃ (b : Fin (Dc.N - Dc.j) → Or.𝔐.Li) (A : Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) Ω),
        (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)).IsFrameAt b q ∧ ∀ k, b k = ∑ k', A k' k • s' τ k' := fun τ => by
      have h1 := hvb (Or.sm τ)
      rw [Or.rk_sm τ] at h1
      obtain ⟨U, hU, b, hsp, hfr⟩ := h1 q trivial
      have h2 : ∀ k, ∃ t : Fin (Dc.N - Dc.j) → Ω, ∑ a, t a • s' τ a = b k := fun k =>
        (Submodule.mem_span_range_iff_exists_fun Ω).1 (le_span_frame (L := Or.𝔐.V (Or.sm τ))
          (U := Or.𝔐.Vgen (Or.sm τ)) (Or.𝔐.vb (Or.sm τ)) (hs' τ) (hsp ▸ Submodule.subset_span ⟨k, rfl⟩))
      choose t ht using h2
      exact ⟨b, Matrix.of fun a k => t k a, hfr q trivial hU, fun k => (ht k).symm⟩
    choose b A hb hA using hb
    refine ⟨b, A, hb, hA, ?_⟩
    have hHT : ∀ τ, (Or.𝔐.HT p (Or.sm τ)).IsFrameAt (b τ) q := fun τ =>
      ⟨(hb τ).1, ((P (Or.sm τ)).2 p (Finset.mem_union_right _ hp) hf).symm.trans (hb τ).2⟩
    have hv := Or.vert p (hS p hp) q hf ch hq (fun τ => s' τ ∘ Fin.cast (Or.rk_sm τ))
      (fun τ => b τ ∘ Fin.cast (Or.rk_sm τ)) (fun τ => (A τ).submatrix (Fin.cast (Or.rk_sm τ)) (Fin.cast (Or.rk_sm τ)))
      (fun τ => cast_frame _ (hs' τ)) (fun τ => cast_frame _ (hHT τ)) (fun τ k => cast_sum _ (hA τ) k)
    simp only [cast_det] at hv
    have hrest := unitAt_prod ((Dc.SB B).erase p) _ fun p' hp' => hoff p' (Finset.mem_of_mem_erase hp')
      (not_inFibre_two (Dc.S_prime p (hS p hp)) (Dc.S_prime p' (hS p' (Finset.mem_of_mem_erase hp')))
        (Finset.ne_of_mem_erase hp').symm hf)
    rw [← Finset.mul_prod_erase _ _ hp, ← div_div, div_eq_mul_inv (_ / _)]
    exact unitAt_mul hv (unitAt_inv hrest)
  · push Not at h
    refine ⟨s', fun _ => 1, fun τ => ⟨(hs' τ).1, Eq.trans ?_ (hs' τ).2⟩, fun τ k => by simp [Matrix.one_apply], ?_⟩
    · by_cases h' : ∃ p ∈ S₀, InFibre Or.𝔐.ξ p q
      · obtain ⟨p, hp, hq⟩ := h'
        exact ((P _).2 p (Finset.mem_union_left _ hp) hq).trans ((P₀ _).2 p hp hq).symm
      · push Not at h'
        exact ((P _).1 fun p hp => (Finset.mem_union.1 hp).elim (h' p) (h p)).trans ((P₀ _).1 h').symm
    · simp only [Matrix.det_one, Finset.prod_const_one, one_div]
      exact unitAt_inv (unitAt_prod _ _ fun p hp => hoff p hp (h p hp))

end Main

end N1

open N1

theorem det_lattice_tensor_isDegOn_muTwDeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B : ℕ) (bb : ∀ τ, Fin Dc.N → W τ) (s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) (lam : Ω), (∀ τ k, s τ k ∈ Or.𝔐.Vgen (Or.sm τ) ∧ Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - s τ k ∈ Or.𝔐.Vgen (Or.bg τ)) → Hd.Λ = lam • PiTensorProduct.tprod Ω (fun τ => quotWedge (Hd.F τ) Dc.j_le_N (bb τ)) → (∀ τ, LinearIndependent Ω (s τ)) ∧ (Lat.tens (fun τ => detLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ Dc.y (muTwDeg Hd B) (lam⁻¹ * ∏ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vden p) / MvPolynomial.aeval Dc.y (Dc.vnum p)) := by
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B bb s lam hs hΛ
  obtain ⟨hpr, -, -, hvb⟩ := component_data_height_identity E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B
  have hS : ∀ p ∈ Dc.SB B, p ∈ Dc.S := fun p hp => (Finset.mem_filter.1 hp).1
  have hnd : ∀ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vnum p) ≠ 0 ∧ MvPolynomial.aeval Dc.y (Dc.vden p) ≠ 0 := by
    intro p hp
    have hv := Dc.vertical p (hS p hp)
    obtain ⟨bf, bg, hf, hg, -⟩ := hv.degrees
    exact ⟨fun h => hv.num_not_mem ((mem_coord_iff _ hf).2 h), fun h => hv.den_not_mem ((mem_coord_iff _ hg).2 h)⟩
  have hP : ∏ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vden p) / MvPolynomial.aeval Dc.y (Dc.vnum p) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p hp => div_ne_zero (hnd p hp).2 (hnd p hp).1
  obtain ⟨c₀, hc₀⟩ := Or.𝔐.tie.cover ⟨genPt Or.𝔐.ξ, specializes_rfl⟩
  obtain ⟨s₀, T₀, u₀, hf₀, hT₀, hu₀, e₀⟩ := local_frame Or hs hΛ hc₀
  have n₀ : lam * ∏ τ, (T₀ τ).det ≠ 0 := e₀ ▸ mul_ne_zero hu₀.1 (chartMono_ne (ne_of_seg hc₀.1) _)
  have hlam : lam ≠ 0 := left_ne_zero_of_mul n₀
  have hli : ∀ τ, LinearIndependent Ω (s τ) := fun τ => li_of_det (hf₀ τ).1 (hT₀ τ)
    (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul n₀) τ (Finset.mem_univ τ))
  refine ⟨hli, mul_ne_zero (inv_ne_zero hlam) hP, fun q _ ch hq => ?_⟩
  have hc := ne_of_seg hq.1
  obtain ⟨s', T, u, hf, hT, hu, e⟩ := local_frame Or hs hΛ hq
  have n₁ : ∏ τ, (T τ).det ≠ 0 := right_ne_zero_of_mul (e ▸ mul_ne_zero hu.1 (chartMono_ne hc _))
  have hd : ∀ τ, (T τ).det ≠ 0 := fun τ => Finset.prod_ne_zero_iff.1 n₁ τ (Finset.mem_univ τ)
  obtain ⟨b, A, hb, hA, hun⟩ := local_change Or B hpr hvb hq hf
  have hg : ∀ τ, (detLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) (s τ)).IsGenAt q ((T τ)⁻¹ * A τ).det := fun τ =>
    determinant_lattice_generator _ _ _ _ _ _ _ _ _ _ (hli τ) (hb τ) (mat_comp (mat_inv (hT τ) (hd τ)) (hA τ))
  rw [(tens_gen (fun _ => -1) hg).2]
  have n₂ := chartMono_ne hc (muTwDeg Hd B)
  refine span_eq_of_unit (mul_ne_zero n₂ (mul_ne_zero (inv_ne_zero hlam) hP)) ?_
  have e1 : ∏ τ, ((T τ)⁻¹ * A τ).det ^ (-1 : ℤ) = (∏ τ, (T τ).det) / ∏ τ, (A τ).det := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', _root_.zpow_neg_one, mul_inv, inv_inv,
      div_eq_mul_inv]
  have e2 : ∏ p ∈ Dc.SB B, (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) *
      chartMono Dc.y ch (-Dc.vdeg p)) =
      (∏ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vden p) / MvPolynomial.aeval Dc.y (Dc.vnum p))⁻¹ *
        (chartMono Dc.y ch (∑ p ∈ Dc.SB B, Dc.vdeg p))⁻¹ := by
    rw [chartMono_sum hc, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => by rw [inv_div, chartMono_neg]
  have n₃ := chartMono_ne hc Hd.aMu
  have n₄ := chartMono_ne hc (∑ p ∈ Dc.SB B, Dc.vdeg p)
  have n₅ : ∏ τ, (A τ).det ≠ 0 := fun h0 => hun.1 (by rw [h0, zero_div])
  rw [e2] at hun
  have e3 : ∏ τ, (T τ).det = u * chartMono Dc.y ch Hd.aMu / lam := by rw [e]; field_simp
  convert unitAt_mul hu (unitAt_inv hun) using 1
  show _ / (chartMono Dc.y ch (Hd.aMu + ∑ p ∈ Dc.SB B, Dc.vdeg p) * _) = _
  rw [e1, e3, chartMono_add hc]
  field_simp

end LevelTowerAlt
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsSeqCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace LevelTowerAlt.Val
open GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.QuotLoc GlobalTheory.UU GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree
open GroundTheory.Heights₂.Heights.Regular (logCover expCover)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {σ₀ : KA l →+* ℂ} {n a : ℕ}

theorem abPart_principal (C : Flat.BdryChart Xo σ₀ n a) {z : Fin n → ℂ} (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1)
    (P : AbPart C.t (spMap (C.ψ z))) : IsPrincipal P.tB := by
  obtain ⟨V, _, _, _, f, r, tV, mV, hV, hr, hker, hrf, hpol⟩ := _root_.GlobalTheory.CompanionTheory.Ar.QuotLoc.exists_curve_through_point E H D l Xo σ₀ n a C z hz
  have key : ∀ (z₀ : Sp ℂ ⟶ Sp C.R), z₀ = spMap r ≫ spMap f → ∀ P : AbPart C.t z₀, IsPrincipal P.tB := by
    rintro _ rfl P
    obtain ⟨m', -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.AbPartPull.exists_sabMap_tK E H _ _ tV C.t _ mV ℂ (spMap r) P
    exact _root_.PositivityTheory.HtPt.Ppic.dvr E H V r tV hV hr hker hpol ⟨P.tK, m', P.τ, P.tB, P.e, P.e_hom, P.act, P.pp⟩
  refine key _ ?_ P
  rw [← hrf]
  show Spec.map (CommRingCat.ofHom (r.comp f)) = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem exists_seq_cover (h : a ≤ n) : ∃ ws : ℕ → Fin n → ℂ, (∀ k, ws k ∈ logCover h) ∧
    Tendsto (fun k => expCover a (ws k)) atTop (𝓝 0) := by
  refine ⟨fun m i => if (i : ℕ) < a then -((m : ℂ) + 1) else 0, fun m => ⟨fun i => ?_, fun i hi => ?_⟩, ?_⟩
  · have hi : ((Fin.castLE h i : Fin n) : ℕ) < a := by simp
    simp only [hi, ↓reduceIte, Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  · have hi' : ¬ ((i : ℕ) < a) := by omega
    simp [hi']
  · rw [tendsto_pi_nhds]
    intro i
    by_cases hi : (i : ℕ) < a
    · simp only [expCover, hi, ↓reduceIte, Pi.zero_apply]
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [Complex.norm_exp, Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
      exact Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))
    · simp only [expCover, hi, ↓reduceIte, Pi.zero_apply]
      exact tendsto_const_nhds

theorem periods_inj {g : ℕ} {Λ : Type} [AddCommGroup Λ] (L₀ : Flat.LogPeriods n a g Λ) {w : Fin n → ℂ}
    (hw : w ∈ logCover L₀.a_le) : Function.Injective (L₀.P w) := by
  intro x x' hxx
  have h0 : L₀.P w (x - x') = 0 := by rw [map_sub, hxx, sub_self]
  have hE : L₀.E (x - x') = 0 := by
    refine LinearMap.ext fun y => ?_
    have him := L₀.im w hw (x - x') y
    rw [h0] at him
    have h2 : ((L₀.E (x - x') y : ℤ) : ℝ) = 0 := by
      rw [← him]
      simp
    rw [LinearMap.zero_apply]
    exact_mod_cast h2
  exact sub_eq_zero.1 (L₀.unimod.1 (hE.trans (map_zero L₀.E).symm))

theorem centre_phi (C : Flat.BdryChart Xo σ₀ n a) {X : Scheme.{0}} {tt : SAB H X} {jj : Sp C.R ⟶ X}
    (m : SABMap C.t tt jj) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (e : Flat.FamExp C.t.G C.M (Metric.ball 0 ρ) C.ψ)
    {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (L : ActPeriods E n a C.g Λ)
    (hlink : ∀ w ∈ logCover L.a_le, (∀ p, p ∈ e.per ((ρ : ℂ) • expCover a w) ↔ ∃ x, L.P w x = p) ∧
      ∀ (N : ℕ) (ζ : ℂˣ) (x x' : Λ), 0 < N → CubWeil C.t.cub N (e.ex ((ρ : ℂ) • expCover a w) ((N : ℂ)⁻¹ • L.P w x))
        (e.ex ((ρ : ℂ) • expCover a w) ((N : ℂ)⁻¹ • L.P w x')) (unitOn ζ) →
        (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((L.toLogPeriods.E x x' : ℤ) : ℂ) / N))
    (hB : ∀ c x, e.ex ((ρ : ℂ) • 0) (L.B 0 c x) = e.ex ((ρ : ℂ) • 0) x ≫ C.t.act.act c)
    {A : Type} [Fintype A] {k : ℕ} (σ : A → (𝓞 E →+* ℂ)) (b : A → Fin k → (Fin n → ℂ) → Fin C.g → ℂ)
    (sc : A → Fin k → Fin C.g → C.R) (hb0 : ∀ τ i, b τ i 0 = fun j => C.ψ ((ρ : ℂ) • 0) (sc τ i j))
    (hσ : IsCMFam σ) (hb : IsEigFrames (Metric.ball 0 1) L.B σ b)
    (P : AbPart tt (spMap (C.ψ ((ρ : ℂ) • 0)) ≫ jj))
    {V : Type} [AddCommGroup V] [Module ℂ V] (MV : LieModel P.tK.G (𝟙 (Sp ℂ)) V)
    (ρV : 𝓞 E →+* Module.End ℂ V) (I₀ : AddSubgroup V) (hf : V → V → ℂ) (hact : MV.IsActOf P.tK.act.act ρV)
    (hI₀ : P.IsCochars MV I₀)
    (hh : ∀ x x', HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (MV.pt x ≫ P.τ.q ≫ P.e.hom) (MV.pt x' ≫ P.τ.q ≫ P.e.hom) (hf x x'))
    (bz : A → Fin k → V) (hbz : ∀ τ i, (MV.pt (bz τ i)).left ≫ P.m.φ =
      spMap (dualMap (C.ψ ((ρ : ℂ) • 0))) ≫ (C.M.pt (sc τ i)).left ≫ m.φ)
    {ν : ℝ} (hν : PhiNormSq ρV hf I₀ (4 * Real.pi)⁻¹ σ bz ν) :
    ∃ I : Submodule (𝓞 E) Λ, IsSaturated I ∧ IsIsoSub L.toLogPeriods.E I ∧ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ w (hw : w ∈ logCover L.a_le), ‖expCover a w‖ < δ →
        Real.log ν - ε ≤ (Fintype.card A : ℝ) * ((k : ℝ) * Real.log Real.pi) +
          (L.riem w hw).logDet (fun τ i => b τ i (expCover a w)) - Real.log ((L.riem w hw).nz σ I) := by
  obtain ⟨W, I, per, s, Hb, hI, hsat, -, hs, hlim, -, hH, hIm, hrad, hlimν⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.limit_at_centre E n a C.g Λ A L σ k b hσ hb
  have h00 : (ρ : ℂ) • (0 : Fin n → ℂ) = 0 := smul_zero _
  have hbρ : (ρ : ℂ) • (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
    rw [h00]; exact Metric.mem_ball_self hρ0
  have hol : Flat.IsHolPts (Metric.ball 0 ρ) C.ψ :=
    ⟨Metric.isOpen_ball, fun r => (C.hol.2 r).mono (Metric.ball_subset_ball hρ1)⟩
  obtain ⟨ws, hws, hw0⟩ := exists_seq_cover L.a_le
  have hper : ∀ x : W, Tendsto (fun j => L.P (ws j) x) atTop (𝓝 (per x)) := fun x => by
    obtain ⟨h1, h2, h3⟩ := hs x
    have := h1.tendsto.comp hw0
    rw [h2] at this
    exact this.congr fun j => h3 _ (hws j)
  have hfour : ∀ (x : ℕ → Λ) (p : Fin C.g → ℂ), Tendsto (fun j => L.P (ws j) (x j)) atTop (𝓝 p) →
      ∃ x₀ : W, p = per x₀ ∧ ∀ᶠ j in atTop, x j = x₀ := by
    intro x p hx
    obtain ⟨x₀, rfl⟩ := hlim ws x p hws hw0 hx
    refine ⟨x₀, rfl, ?_⟩
    have h1 : Tendsto (fun j => ((ρ : ℂ) • expCover a (ws j), L.P (ws j) (x j - x₀))) atTop (𝓝 ((ρ : ℂ) • 0, 0)) := by
      refine (hw0.const_smul _).prodMk_nhds ?_
      have := hx.sub (hper x₀)
      rw [sub_self] at this
      simpa only [map_sub] using this
    filter_upwards [h1.eventually (per_small e hbρ (Metric.isOpen_ball.mem_nhds hbρ))] with j hj
    have h2 := hj (((hlink _ (hws j)).1 _).2 ⟨_, rfl⟩)
    exact sub_eq_zero.1 (periods_inj L.toLogPeriods (hws j) (h2.trans (map_zero _).symm))
  obtain ⟨hA, hBp, hC⟩ := _root_.GlobalTheory.CompanionTheory.Ar.QuotLoc.limit_lattice E H C.R C.t C.g n a C.M C.ψ ρ e Λ L.toLogPeriods hρ0 hρ1 hol hlink 0
    (Metric.mem_ball_self one_pos) ws (W.restrictScalars ℤ) per hws hw0 hper hfour
  replace hA : ∀ x : W, per x ∈ e.per ((ρ : ℂ) • 0) := hA
  replace hBp : ∀ p ∈ e.per ((ρ : ℂ) • 0), ∃ x : W, per x = p := hBp
  obtain ⟨m', hm'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.AbPartPull.exists_sabMap_tK E H _ _ C.t tt jj m ℂ _ P
  let P' : AbPart C.t (spMap (C.ψ ((ρ : ℂ) • 0))) := ⟨P.tK, m', P.τ, P.tB, P.e, P.e_hom, P.act, P.pp⟩
  have hP := abPart_principal C (Metric.ball_subset_ball hρ1 hbρ) P'
  obtain ⟨Mz, hMz⟩ := _root_.GlobalTheory.CompanionTheory.Ar.QuotUnif.frame_lieModel_fibre E H D l Xo σ₀ n a C ((ρ : ℂ) • 0)
  have hL : ∀ i, ((Mz.pt (Pi.single i 1)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ ((ρ : ℂ) • 0))) ≫ (C.M.pt (Pi.single i 1)).left) := fun i => by
    have h1 := hMz (Pi.single i 1)
    have h2 : (fun j => C.ψ ((ρ : ℂ) • 0) ((Pi.single i 1 : Fin C.g → C.R) j)) = (Pi.single i 1 : Fin C.g → ℂ) := by
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [Pi.single_apply, h]
    rwa [h2] at h1
  obtain ⟨Φ, f1, f2, f3, f4⟩ := centre_ident e hbρ P' hP Mz hL MV ρV I₀ hf hact hI₀ hh (L.B 0) hB Hb hH
    (fun y hy y' hy' => by
      obtain ⟨x, rfl⟩ := hBp y hy
      obtain ⟨x', rfl⟩ := hBp y' hy'
      exact ⟨_, hIm x x', fun N ζ hN hζ => hC N ζ x x' hN hζ⟩)
    {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x}
    (fun p => ⟨by
      rintro ⟨x, hx, rfl⟩
      refine ⟨hA x, fun y hy => ?_⟩
      obtain ⟨x', rfl⟩ := hBp y hy
      rw [hIm x x', ((hI _).1 hx).2 _ x'.2, Int.cast_zero], by
      rintro ⟨hp, h0⟩
      obtain ⟨x, rfl⟩ := hBp p hp
      refine ⟨x, (hI _).2 ⟨x.2, fun y hy => ?_⟩, rfl⟩
      have := h0 _ (hA ⟨y, hy⟩)
      rw [hIm x ⟨y, hy⟩] at this
      exact_mod_cast this⟩)
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact hrad x hx)
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  let Ψ : V ≃ₗ[ℂ] (Fin C.g → ℂ) := Φ.trans (LinearEquiv.smulOfNeZero ℂ _ _ hc)
  have hΨ : ∀ x, Ψ x = (2 * Real.pi * Complex.I : ℂ) • Φ x := fun x => rfl
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  obtain ⟨ν', hν', hνe⟩ := phi_transport ρV (L.B 0) Ψ (fun c x => by rw [hΨ, hΨ, map_smul, f2]) hf
    (fun x y => y ⬝ᵥ Hb *ᵥ star x) (4 * Real.pi)⁻¹
    (fun x x' => by
      rw [f3, hΨ, hΨ, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
      simp only [smul_eq_mul, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
      push_cast
      field_simp
      linear_combination (4 * (Φ x' ⬝ᵥ Hb *ᵥ star (Φ x))) * Complex.I_mul_I)
    I₀ (AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x})
    (by
      rw [← AddSubgroup.closure_eq (I₀.map Ψ.toLinearMap.toAddMonoidHom)]
      congr 1
      ext p
      rw [f4]
      exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩⟩)
    σ bz (fun τ i => b τ i 0) _ hc
    (fun τ i => by
      rw [hΨ, hb0]
      congr 1
      refine Mz.inj (Over.OverMorphism.ext (m.cart.1.hom_ext ?_ ?_))
      · have h1 := hMz (sc τ i)
        change _ ≫ _ = _ ≫ _ at h1
        rw [Category.comp_id] at h1
        rw [f1, h1, Category.assoc, Category.assoc]
        exact (congrArg _ hm').trans (hbz τ i)
      · rw [Over.w (Mz.pt _), Over.w (Mz.pt _)])
    ν hν
  obtain ⟨hpos, hlim'⟩ := hlimν ν' hν'
  have e1 : (4 * Real.pi)⁻¹ * ‖(2 * Real.pi * Complex.I : ℂ)‖ ^ 2 = Real.pi := by
    have := Real.pi_pos
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat, Real.norm_of_nonneg this.le]
    field_simp
    ring
  have e2 : Real.log ν = (Fintype.card A : ℝ) * ((k : ℝ) * Real.log Real.pi) + Real.log ν' := by
    rw [hνe, e1, Real.log_mul (pow_ne_zero _ Real.pi_ne_zero) hpos.ne', Real.log_pow]
    push_cast
    ring
  refine ⟨I, hsat, fun v hv w hw => ((hI _).1 hv).2 _ ((hI _).1 hw).1, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, h⟩ := hlim' ε hε
  refine ⟨δ, hδ, fun w hw h1 => ?_⟩
  have := (abs_lt.1 (h w hw h1)).1
  linarith

end LevelTowerAlt.Val
end
end

