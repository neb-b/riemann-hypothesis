module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.LeviForms.TailBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0041
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LinearIndependentImg

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsPshPull
section
noncomputable section

namespace LevelTowerAlt.Comparison₂

open Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB

variable {e e' : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] {A : FinHolAtlas e X} {A' : FinHolAtlas e' Z}

theorem holo_mono {U V : Set X} {g : X → ℂ} (h : A.HoloOn U g) (hVU : V ⊆ U) : A.HoloOn V g :=
  fun j => (h j).mono fun _ hy => ⟨hy.1, hVU hy.2⟩

theorem holo_cont {U : Set X} {g : X → ℂ} (h : A.HoloOn U g) {x : X} (hx : x ∈ U) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  have hc := (h j _ ⟨(A.chart j).map_source hj, by rwa [Set.mem_preimage, (A.chart j).left_inv hj]⟩).continuousAt
  refine (hc.comp ((A.chart j).continuousAt hj)).congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem holo_comp {U : Set Z} {g : Z → ℂ} (hg : A'.HoloOn U g) {h : X → Z} (hh : HoloMap A A' h) :
    A.HoloOn (h ⁻¹' U) (g ∘ h) := by
  intro j y hy
  obtain ⟨k, hk⟩ := A'.cover (h ((A.chart j).symm y))
  have h1 := hh.2 j k y ⟨hy.1, hk⟩
  have h2 := hg k (A'.chart k (h ((A.chart j).symm y)))
    ⟨(A'.chart k).map_source hk, by rw [Set.mem_preimage, (A'.chart k).left_inv hk]; exact hy.2⟩
  refine (AnalyticAt.comp (f := A'.chart k ∘ h ∘ (A.chart j).symm) h2 h1).congr ?_
  have hc : ContinuousAt (h ∘ (A.chart j).symm) y := hh.1.continuousAt.comp ((A.chart j).continuousAt_symm hy.1)
  filter_upwards [hc.eventually_mem ((A'.chart k).open_source.mem_nhds hk)] with y' hy'
  have : (A'.chart k).symm (A'.chart k (h ((A.chart j).symm y'))) = h ((A.chart j).symm y') := (A'.chart k).left_inv hy'
  simp [this]

def LocRe (A : FinHolAtlas e X) (u : X → ℝ) (x : X) : Prop :=
  ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, u y = (G y).re

theorem LocRe.congr {u u' : X → ℝ} {x : X} (h : LocRe A u x) (hu : ∀ᶠ y in 𝓝 x, u' y = u y) : LocRe A u' x := by
  obtain ⟨V, hV, hx, G, hG, h⟩ := h
  obtain ⟨W, hW, hWo, hxW⟩ := eventually_nhds_iff.1 hu
  exact ⟨V ∩ W, hV.inter hWo, ⟨hx, hxW⟩, G, holo_mono hG Set.inter_subset_left, fun y hy => (hW y hy.2).trans (h y hy.1)⟩

theorem LocRe.zero (x : X) : LocRe A (fun _ => 0) x :=
  ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, fun _ _ _ => analyticAt_const, fun _ _ => rfl⟩

theorem LocRe.add {u u' : X → ℝ} {x : X} (h : LocRe A u x) (h' : LocRe A u' x) : LocRe A (fun y => u y + u' y) x := by
  obtain ⟨V, hV, hx, G, hG, h⟩ := h
  obtain ⟨V', hV', hx', G', hG', h'⟩ := h'
  exact ⟨V ∩ V', hV.inter hV', ⟨hx, hx'⟩, _, holoOn_add A hG hG', fun y hy => by simp [h y hy.1, h' y hy.2]⟩

theorem LocRe.mul {u : X → ℝ} {x : X} (h : LocRe A u x) (c : ℝ) : LocRe A (fun y => c * u y) x := by
  obtain ⟨V, hV, hx, G, hG, h⟩ := h
  exact ⟨V, hV, hx, _, holoOn_mul A hG c, fun y hy => by simp [h y hy]⟩

theorem LocRe.sum {I : Type} (s : Finset I) {u : I → X → ℝ} {x : X} (h : ∀ i ∈ s, LocRe A (u i) x) :
    LocRe A (fun y => ∑ i ∈ s, u i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LocRe.zero x
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (by simp)).add (ih fun j hj => h j (by simp [hj]))

theorem LocRe.comp {u : Z → ℝ} {h : X → Z} (hh : HoloMap A A' h) {x : X} (hu : LocRe A' u (h x)) : LocRe A (fun y => u (h y)) x := by
  obtain ⟨V, hV, hx, G, hG, hu⟩ := hu
  exact ⟨h ⁻¹' V, hV.preimage hh.1, hx, _, holo_comp hG hh, fun y hy => hu _ hy⟩

theorem LocRe.log {U : Set X} (hU : IsOpen U) {f : X → ℂ} (hf : A.HoloOn U f) {x : X} (hx : x ∈ U) (h0 : f x ≠ 0) :
    LocRe A (fun y => Real.log ‖f y‖) x := by
  have hc : ContinuousOn (fun y => f y / f x) U := fun y hy => ((holo_cont hf hy).div_const _).continuousWithinAt
  refine ⟨U ∩ (fun y => f y / f x) ⁻¹' Complex.slitPlane, hc.isOpen_inter_preimage hU Complex.isOpen_slitPlane,
    ⟨hx, by simp [div_self h0]⟩, fun y => Complex.log (f y / f x) + (Real.log ‖f x‖ : ℝ), fun j y hy => ?_, fun y hy => ?_⟩
  · exact (((hf j y ⟨hy.1, hy.2.1⟩).div_const (c := f x)).clog hy.2.2).add analyticAt_const
  · have h1 : f y ≠ 0 := fun h => by simpa [h] using hy.2
    simp [Complex.log_re, Real.log_div, h1, h0]

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem log_h_smul (L : HermLine J) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (L.h fun p => c p.1 * z p) = ∑ k, (L.a k : ℝ) * Real.log ‖c k‖ + Real.log (L.h z) := by
  have hp : ∀ k, ‖c k‖ ^ L.a k ≠ 0 := fun k => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [L.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => hp k) (L.pos z hz).ne', Real.log_prod fun k _ => hp k]
  simp only [Real.log_zpow]

theorem log_diff_orbit {L L' : HermLine J} (h : L.a = L'.a) {z z' : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0)
    (ho : SameOrbit z z') : Real.log (L.h z) - Real.log (L'.h z) = Real.log (L.h z') - Real.log (L'.h z') := by
  obtain ⟨c, hc, rfl⟩ := ho
  rw [log_h_smul L hc hz, log_h_smul L' hc hz, h]
  ring

theorem locRe_orbit (L : HermLine J) {U : Set X} (hU : IsOpen U) {s s' : X → (Σ k, J k) → ℂ}
    (hs : ∀ p, A.HoloOn U fun y => s y p) (hs' : ∀ p, A.HoloOn U fun y => s' y p) (hne : ∀ y ∈ U, ∀ k, ∃ i, s' y ⟨k, i⟩ ≠ 0)
    (ho : ∀ y ∈ U, SameOrbit (s y) (s' y)) {x : X} (hx : x ∈ U) :
    LocRe A (fun y => Real.log (L.h (s y)) - Real.log (L.h (s' y))) x := by
  choose i hi using hne x hx
  have hi' : ∀ k, s x ⟨k, i k⟩ ≠ 0 := fun k => by
    obtain ⟨c, hc, e⟩ := ho x hx
    rw [e]
    exact mul_ne_zero (hc k) (hi k)
  have h1 := LocRe.sum (A := A) Finset.univ (x := x) (u := fun k y => (L.a k : ℝ) *
      (Real.log ‖s y ⟨k, i k⟩‖ + -1 * Real.log ‖s' y ⟨k, i k⟩‖)) fun k _ =>
    ((LocRe.log hU (hs _) hx (hi' k)).add ((LocRe.log hU (hs' _) hx (hi k)).mul _)).mul _
  refine h1.congr ?_
  filter_upwards [hU.mem_nhds hx, eventually_all.2 fun k => (holo_cont (hs' ⟨k, i k⟩) hx).eventually_ne (hi k)] with y hy hy'
  obtain ⟨c, hc, e⟩ := ho y hy
  rw [e, log_h_smul L hc (hne y hy), add_sub_cancel_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hc k)) (norm_ne_zero_iff.2 (hy' k))]
  ring

theorem psh_of_locRe {P Q : LocPot X} (hP : IsPotential A P) (hQ : IsPotential A Q)
    (h : ∀ x, LocRe A (fun y => P.φ x y - Q.φ x y) x) (hq : IsPsh A Q) : IsPsh A P := by
  have hz : A.Smooth (fun _ : X => (0 : ℝ)) := fun j => contDiffOn_const
  have h1 := (PshPull.isPsh_pull e e X X A A id (holoMap_id A) P Q (fun _ => 0) hP hQ hz (fun x _ => h x)).1
    (TailBoundAlt.isPsh_congr A _ _ hq (fun x y hy => hy.1) (by funext x y; exact add_zero _))
  exact TailBoundAlt.isPsh_congr A _ _ h1 (fun x y hy => ⟨hy, trivial⟩) (by funext x y; exact (add_zero _).symm)

theorem pot_rsmul {P : LocPot X} (hP : IsPotential A P) (c : ℝ) : IsPotential A (P.rsmul c) :=
  isPotential_mul A P hP c _ rfl fun _ _ => rfl

theorem exists_psh_pull [CompactSpace X] [T2Space X] {h : X → Z} (hh : HoloMap A A' h) {Θ : LocPot X} (hΘ : IsPotential A Θ)
    (hΘp : IsPosPot A Θ) {Θ' : LocPot Z} (hΘ' : IsPotential A' Θ') :
    ∃ C : ℝ, ∀ (P : LocPot X) (Q : LocPot Z), IsPotential A P → IsPotential A' Q → IsPsh A' (Q + Θ') →
      (∀ x, LocRe A (fun y => P.φ x y - Q.φ (h x) (h y)) x) → IsPsh A (P + Θ.rsmul C) := by
  have hp := isPotentialPullback A' A h hh Θ' hΘ'
  obtain ⟨C, -, -, hC⟩ := TailBoundAlt.exists_psh_chern_bound A Θ _ hΘ hΘp hp
  refine ⟨C, fun P Q hP hQ hq hl => ?_⟩
  have hz : A'.Smooth (fun _ : Z => (0 : ℝ)) := fun j => contDiffOn_const
  have hQ' := isPotentialAdd A' _ _ hQ hΘ'
  have hP' := isPotentialPullback A' A h hh _ hQ'
  have h1 := (PshPull.isPsh_pull e e' X Z A A' h hh _ (Q + Θ') (fun _ => 0) hP' hQ' hz
    (fun x _ => (LocRe.zero x).congr (Eventually.of_forall fun y => sub_self _))).1
    (TailBoundAlt.isPsh_congr A' _ _ hq (fun x y hy => hy.1) (by funext x y; exact add_zero _))
  have h2 : IsPsh A ((Q + Θ').pullback h hh.1) :=
    TailBoundAlt.isPsh_congr A _ _ h1 (fun x y hy => ⟨hy, trivial⟩) (by funext x y; exact (add_zero _).symm)
  have hR := isPotentialAdd A _ _ (pot_rsmul hΘ C) (pot_rsmul hp (-1))
  refine psh_of_locRe (isPotentialAdd A _ _ hP (pot_rsmul hΘ C)) (isPotentialAdd A _ _ hP' hR) (fun x => ?_)
    (isPshAdd A _ _ hP' hR h2 hC)
  refine (hl x).congr (Eventually.of_forall fun y => ?_)
  show P.φ x y + C * Θ.φ x y - (Q.φ (h x) (h y) + Θ'.φ (h x) (h y) + (C * Θ.φ x y + -1 * Θ'.φ (h x) (h y))) = _
  ring

end LevelTowerAlt.Comparison₂
end
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.LabelDegreeLogIndex
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights

theorem LevelTowerAlt.label_degree_log_index : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r k : ℕ) (v : Fin r → V) (s : Ψ ⊕ Ψ) (q : Fin k → A.Λ), 2 * Fintype.card Ψ = Module.finrank ℚ E → IsOFamily A.ρ A.I v → (∀ c, (q c : V) ∈ A.eig s) → A.IsAdapted s v q → A.labDeg s (A.eig s) v q = logIdx (A.tor s) (fun a => eigComp A.ρ (A.σ s) (v a)) / Module.finrank ℚ L + A.Bq.normDegree (A.img s) := by
  intro E L Ψ _ _ _ _ _ V _ _ _ _ A r k v s q hΨ hv hq had
  obtain ⟨-, -, h3, h4⟩ := LevelTowerAlt.tor_facts A hΨ hv s
  obtain ⟨h5, h6⟩ := LevelTowerAlt.sub_eig A had.2
  have h7 := LevelTowerAlt.relIndex_ne_zero had.1 h5 h6 h5
  obtain ⟨e1, e2⟩ := LevelTowerAlt.index_split A had.1 h3 h4 hq
  rw [LinPt.fam, e1] at h7
  have h8 := (LevelTowerAlt.rank_img A (LevelTowerAlt.linearIndependent_img A had.1 h4 hq) hq (right_ne_zero_of_mul h7)).2
  rw [LinPt.labDeg, HermitianBundle.normDegree, h8, logIdx, logIdx, LinPt.fam, e1, e2, Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.2 (left_ne_zero_of_mul h7)) (Nat.cast_ne_zero.2 (right_ne_zero_of_mul h7))]
  ring
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.OrthogonalFamilyAdaptedBasis
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights

namespace LevelTowerAlt

theorem exists_isOFamily {E L V : Type} [Field E] [NumberField E] [Field L] [CharZero L] [AddCommGroup V] [Module L V]
    (ρ : 𝓞 E →+* Module.End L V) (I : AddSubgroup V) (hst : ∀ a, ∀ x ∈ I, ρ a x ∈ I) {n : ℕ} (e : Fin n → V)
    (he : AddSubgroup.closure (Set.range e) = I) : ∃ (r : ℕ) (v : Fin r → V), IsOFamily ρ I v := by
  letI : Module (𝓞 E) V := Module.compHom V ρ
  have hρ : ∀ (a : 𝓞 E) (x : V), a • x = ρ a x := fun _ _ => rfl
  let N : Submodule (𝓞 E) V := Submodule.span (𝓞 E) (Set.range e)
  let N' : Submodule (𝓞 E) V := { I.toAddSubmonoid with smul_mem' := fun a x hx => hst a x hx }
  have hN : N.toAddSubgroup = I := by
    refine le_antisymm (fun x hx => ?_) ?_
    · have : N ≤ N' := Submodule.span_le.2 fun y hy => by
        change y ∈ I
        rw [← he]
        exact AddSubgroup.subset_closure hy
      exact this hx
    · rw [← he, AddSubgroup.closure_le]
      exact Submodule.subset_span
  haveI : Module.Finite (𝓞 E) N := Module.Finite.span_of_finite _ (Set.finite_range e)
  obtain ⟨y, hy⟩ := exists_linearIndependent_fin (K := E) (E := N)
  have hfin := finite_quotient_span hy (Fintype.card_fin _)
  refine ⟨_, fun i => (y i : V), fun i => ?_, fun a ha => ?_, ?_⟩
  · rw [← hN]
    exact (y i).2
  · funext i
    refine Fintype.linearIndependent_iff.1 hy a (Subtype.ext ?_) i
    simpa [hρ] using ha
  · have h1 : oSpan ρ (fun i => (y i : V)) =
        ((Submodule.span (𝓞 E) (Set.range y)).map N.subtype).toAddSubgroup := by
      ext x
      rw [TorPart.mem_oSpan_iff, Submodule.map_span, ← Set.range_comp, Submodule.mem_toAddSubgroup,
        Submodule.mem_span_range_iff_exists_fun]
      exact exists_congr fun c => eq_comm
    have h2 : ((Submodule.span (𝓞 E) (Set.range y)).map N.subtype).toAddSubgroup.relIndex N.toAddSubgroup =
        Nat.card (N ⧸ ((Submodule.span (𝓞 E) (Set.range y)).map N.subtype).comap N.subtype) := rfl
    rw [h1, ← hN, h2, Submodule.comap_map_eq_of_injective N.injective_subtype]
    exact Nat.card_pos.ne'

theorem exists_append {L V : Type} [Field L] [AddCommGroup V] [Module L V] [Module.Finite L V] {r : ℕ} {w : Fin r → V}
    (hw : LinearIndependent L w) (S : Set V) :
    ∃ (k : ℕ) (q : Fin k → V), (∀ c, q c ∈ S) ∧ LinearIndependent L (Fin.append w q) ∧
      S ⊆ Submodule.span L (Set.range (Fin.append w q)) := by
  set W := Submodule.span L (Set.range w) with hW
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' L (fun x : S => W.mkQ (x : V))
  haveI : Finite κ := hli.finite
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin κ
  refine ⟨k, fun c => (a (e.symm c) : V), fun c => (a _).2, ?_, fun x hx => ?_⟩
  · have h1 : LinearIndependent L fun i => (⟨w i, Submodule.subset_span ⟨i, rfl⟩⟩ : W) :=
      LinearIndependent.of_comp W.subtype hw
    have h2 := h1.sumElim_of_quotient (fun c => (a (e.symm c) : V)) (hli.comp e.symm e.symm.injective)
    have h3 := h2.comp finSumFinEquiv.symm finSumFinEquiv.symm.injective
    have h4 : Fin.append w (fun c => (a (e.symm c) : V)) =
        Sum.elim w (fun c => (a (e.symm c) : V)) ∘ finSumFinEquiv.symm := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
    rw [h4]
    exact h3
  · have h1 : W.mkQ x ∈ Submodule.span L (Set.range ((fun x : S => W.mkQ (x : V)) ∘ a)) := by
      rw [hsp]
      exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
    have h2 : Set.range ((fun x : S => W.mkQ (x : V)) ∘ a) = W.mkQ '' Set.range fun c => (a (e.symm c) : V) := by
      rw [← Set.range_comp, ← e.symm.surjective.range_comp]
      rfl
    rw [h2, ← Submodule.map_span, ← Submodule.mem_comap, Submodule.comap_map_mkQ] at h1
    rw [range_append, Submodule.span_union]
    exact h1

theorem orthogonal_family_adapted_basis : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V), 2 * Fintype.card Ψ = Module.finrank ℚ E → (∃ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v) ∧ ∀ (r : ℕ) (v : Fin r → V), IsOFamily A.ρ A.I v → ∀ s, ∃ (k : ℕ) (q : Fin k → A.Λ), (∀ c, (q c : V) ∈ A.eig s) ∧ A.IsAdapted s v q ∧ r + k = Module.finrank L (eigSp A.ρ (A.σ s)) ∧ A.Bq.rank (A.img s) = k ∧ ∀ ι, 0 < A.gramDet ι q := by
  intro E L Ψ _ _ _ _ _ V _ _ _ _ A hΨ
  refine ⟨?_, fun r v hv s => ?_⟩
  · obtain ⟨n, e, -, he⟩ := A.I_basis
    exact exists_isOFamily A.ρ A.I A.I_stable e he
  haveI : Module.Finite L V := by
    obtain ⟨S, hS⟩ := A.fg
    refine ⟨S, ?_⟩
    rw [← A.span, ← hS, Submodule.span_span_of_tower]
  obtain ⟨h1, h2, h3, h4⟩ := tor_facts A hΨ hv s
  obtain ⟨k, q, hq, hli, hsp⟩ := exists_append h1 (A.eig s : Set V)
  have had : A.IsAdapted s v fun c => ⟨q c, (hq c).1⟩ := by
    refine ⟨hli, le_antisymm ?_ fun x hx => ?_⟩
    · rw [LinPt.fam, range_append, Submodule.span_le]
      rintro _ (⟨a, rfl⟩ | ⟨c, rfl⟩)
      · exact h2 a
      · exact (hq c).2
    · obtain ⟨c, hc, h5⟩ := exists_smul_mem_eig A s hx
      have hcL : algebraMap (𝓞 L) L c ≠ 0 := by
        rw [map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)]
        exact hc
      have h6 := hsp h5
      rw [← algebraMap_smul L c] at h6
      exact (Submodule.smul_mem_iff _ hcL).1 h6
  obtain ⟨h5, h6⟩ := sub_eig A had.2
  have h7 := relIndex_ne_zero had.1 h5 h6 h5
  rw [LinPt.fam, (index_split A had.1 h3 h4 hq).1] at h7
  have h8 := linearIndependent_img A had.1 h4 hq
  refine ⟨k, _, hq, had, ?_, (rank_img A h8 hq (right_ne_zero_of_mul h7)).1, fun ι => ?_⟩
  · rw [← had.2, finrank_span_eq_card had.1, Fintype.card_fin]
  · rw [gramDet_eq]
    exact gramDet_pos _ _ h8

end LevelTowerAlt
end

