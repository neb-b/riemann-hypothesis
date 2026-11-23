module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0095
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormUniqueUpToUnipotent
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open Formalism.HermitianLatticeCounting.P
namespace GlobalTheory.DegAsm.NFUnique
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

def Cmp (H : HermSpace K V) (p q : V × V) : Prop := H.B p.1 q.1 = H.B p.2 q.2

theorem Cmp.symm {p q : V × V} (h : Cmp H p q) : Cmp H q p := by
  unfold Cmp at *
  rw [← H.herm, h, H.herm]

theorem cmp_span_left {S : Set (V × V)} {q : V × V} (h : ∀ p ∈ S, Cmp H p q) :
    ∀ p ∈ Submodule.span K S, Cmp H p q := by
  intro p hp
  induction hp using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp [Cmp]
  | add x y _ _ h1 h2 => simp only [Cmp] at *; simp [h1, h2]
  | smul a x _ h1 => simp only [Cmp] at *; simp [h1]

theorem exists_isometry (S : Set (V × V)) (h : ∀ p ∈ S, ∀ q ∈ S, Cmp H p q)
    (h1 : (Submodule.span K S).map (LinearMap.fst K V V) = ⊤)
    (h2 : (Submodule.span K S).map (LinearMap.snd K V V) = ⊤) :
    ∃ s : V ≃ₗ[K] V, (∀ x y, H.B (s x) (s y) = H.B x y) ∧ ∀ p ∈ S, s p.1 = p.2 := by
  have hG : ∀ p ∈ Submodule.span K S, ∀ q ∈ Submodule.span K S, Cmp H p q := fun p hp q hq =>
    cmp_span_left (fun p hp => (cmp_span_left (fun q hq => h q hq p hp) q hq).symm) p hp
  set G := Submodule.span K S with hGdef
  have s1 : ∀ v : V, ∃ p : G, p.1.1 = v := fun v => by
    obtain ⟨p, hp, e⟩ := Submodule.mem_map.1 (h1.symm ▸ Submodule.mem_top (x := v))
    exact ⟨⟨p, hp⟩, e⟩
  have s2 : ∀ v : V, ∃ p : G, p.1.2 = v := fun v => by
    obtain ⟨p, hp, e⟩ := Submodule.mem_map.1 (h2.symm ▸ Submodule.mem_top (x := v))
    exact ⟨⟨p, hp⟩, e⟩
  have b1 : Function.Bijective ((LinearMap.fst K V V).comp G.subtype) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun p hp => ?_, s1⟩
    have e1 : p.1.1 = 0 := hp
    refine Subtype.ext (Prod.ext e1 (H.nondeg _ fun y => ?_))
    obtain ⟨q, rfl⟩ := s2 y
    have := hG _ p.2 _ q.2
    rw [Cmp, e1] at this
    simpa using this.symm
  have b2 : Function.Bijective ((LinearMap.snd K V V).comp G.subtype) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun p hp => ?_, s2⟩
    have e1 : p.1.2 = 0 := hp
    refine Subtype.ext (Prod.ext (H.nondeg _ fun y => ?_) e1)
    obtain ⟨q, rfl⟩ := s1 y
    have := hG _ p.2 _ q.2
    rw [Cmp, e1] at this
    simpa using this
  have key : ∀ p : G, ((LinearEquiv.ofBijective _ b1).symm.trans (LinearEquiv.ofBijective _ b2)) p.1.1 = p.1.2 := by
    intro p
    have : (LinearEquiv.ofBijective _ b1).symm p.1.1 = p := (LinearEquiv.symm_apply_eq _).2 rfl
    rw [LinearEquiv.trans_apply, this]
    rfl
  refine ⟨_, fun x y => ?_, fun p hp => key ⟨p, Submodule.subset_span hp⟩⟩
  obtain ⟨p, rfl⟩ := s1 x
  obtain ⟨q, rfl⟩ := s1 y
  rw [key, key]
  exact Eq.symm (hG _ p.2 _ q.2)

theorem gram_eq {F G : FlagD H r} (hT : F.T = G.T) (a b : Fin (r + 1)) :
    H.B (F.e a) (F.e b) = H.B (G.e a) (G.e b) := by
  refine Fin.lastCases ?_ (fun a => ?_) a <;> refine Fin.lastCases ?_ (fun b => ?_) b
  · rw [F.zz, G.zz, hT]
  · rw [B_swap0 H (F.zperp b), B_swap0 H (G.zperp b)]
  · rw [F.zperp, G.zperp]
  · rw [F.iso, G.iso]

theorem flag_vector_mem_base_lattice (F F' : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F F' :=
  Fin.lastCases (lastVector_mem_jointSpan_left F F') (fun a => isotropicSpan_le_jointSpan_left _ _ (e_mem_X _ a)) a

theorem hermFlag_secondFrame_mem_frameSpan (F F' : FlagD H r) (a : Fin (r + 1)) : F'.e a ∈ V0 F F' :=
  Fin.lastCases (lastVector_mem_jointSpan_right F F') (fun a => isotropicSpan_le_jointSpan_right _ _ (e_mem_X _ a)) a

theorem perp_transfer {F G : FlagD H r} (h : SameGr F G) {w : V} (hw : ∀ a, H.B (F.e a) w = 0) (a : Fin (r + 1)) :
    H.B (G.e a) w = 0 := by
  have h1 := perp_X F (fun b => hw b.castSucc) _ (Xa_le_X F _ (h a))
  simpa [hw a] using h1

variable [NumberField K]

theorem wt_e (N : NF H r) {w : V} (hw : w ∈ N.Wt) (a : Fin (r + 1)) : H.B (N.F.e a) w = 0 :=
  (NFGeom.mem_perp' _ _).1 hw _ (Submodule.mem_sup_left (flag_vector_mem_base_lattice _ _ a))

theorem wt_e' (N : NF H r) {w : V} (hw : w ∈ N.Wt) (a : Fin (r + 1)) : H.B (N.F'.e a) w = 0 :=
  (NFGeom.mem_perp' _ _).1 hw _ (Submodule.mem_sup_left (hermFlag_secondFrame_mem_frameSpan _ _ a))

theorem wt_ist (N : NF H r) {w : V} (hw : w ∈ N.Wt) (b : Fin r) (hb : N.j ≤ b.val) : H.B (N.ist b) w = 0 :=
  (NFGeom.mem_perp' _ _).1 hw _ (Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, rfl⟩))

variable [FiniteDimensional K V]

theorem decomp (N : NF H r) {w : V} (hw : ∀ a, H.B (N.F.e a) w = 0) : ∃ w' ∈ N.Wt, w' - w ∈ N.F.X := by
  obtain ⟨x, hx, hp⟩ := (NFGeom.full N).2.2.2.2.2.2.2.1 w hw
  obtain ⟨u, hu, i, hi, e⟩ := Submodule.mem_sup.1 ((NFGeom.isLift N).2.2 _ hp)
  refine ⟨u, hu, ?_⟩
  have : u - w = -(x + i) := by rw [← sub_eq_zero, ← sub_eq_zero.2 e]; abel
  rw [this]
  exact Submodule.neg_mem _ (Submodule.add_mem _ hx hi.1)

theorem eq_top (N : NF H r) (M : Submodule K V) (h1 : ∀ a, N.F.e a ∈ M) (h2 : ∀ a, N.F'.e a ∈ M)
    (h3 : ∀ b : Fin r, N.j ≤ b.val → N.ist b ∈ M) (h4 : N.Wt ≤ M) : M = ⊤ := by
  rw [eq_top_iff, ← (NFGeom.isCompl N).sup_eq_top, NFGeom.Pi_eq]
  refine sup_le h4 (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) <;> refine Submodule.span_le.2 ?_
  · rintro _ ⟨b, -, rfl⟩; exact h1 _
  · rintro _ ⟨b, -, rfl⟩; exact h2 _
  · rintro _ (rfl | rfl)
    · exact h1 _
    · exact h2 _
  · rintro _ ⟨b, hb, rfl⟩; exact h3 b hb

theorem main (N₀ N₁ : NF H r) (h : SameGr N₀.F N₁.F) (hj : N₀.j = N₁.j) (hc : N₀.c = N₁.c) (hT : N₀.T = N₁.T)
    (hM : pairM N₀.F N₀.F' N₀.j = pairM N₁.F N₁.F' N₁.j) :
    ∃ s : V ≃ₗ[K] V, N₀.F.InN (s : V →ₗ[K] V) ∧ ∀ a, s (N₀.F.e a) = N₁.F.e a ∧ s (N₀.F'.e a) = N₁.F'.e a := by
  have hX : N₁.F.X = N₀.F.X := AdaptInv.x_eq h
  have ee := gram_eq (F := N₀.F) (G := N₁.F) (by rw [N₀.hT, N₁.hT, hT])
  have e'e' := gram_eq (F := N₀.F') (G := N₁.F') (by rw [N₀.hT', N₁.hT', hT])
  have ee' : ∀ a b, H.B (N₀.F.e a) (N₀.F'.e b) = H.B (N₁.F.e a) (N₁.F'.e b) := by
    intro a b
    by_cases hb : N₀.j ≤ b.val
    · rw [N₀.same b hb, N₁.same b (hj ▸ hb)]
      simp [ee, hc]
    by_cases ha : N₀.j ≤ a.val
    · rw [NFGeom.e_eq N₀ a ha, NFGeom.e_eq N₁ a (hj ▸ ha)]
      simp [e'e', hc]
    have := congrFun (congrFun hM a) b
    simpa [pairM, ← hj, not_le.1 ha, not_le.1 hb] using this
  have ei : ∀ a (b : Fin r), N₀.j ≤ b.val → H.B (N₀.F.e a) (N₀.ist b) = H.B (N₁.F.e a) (N₁.ist b) := by
    intro a b hb
    refine Fin.lastCases ?_ (fun a => ?_) a
    · exact (N₀.normalForm_dual_orthogonal_last b hb).trans (N₁.normalForm_dual_orthogonal_last b (hj ▸ hb)).symm
    · rw [N₀.ist_e a b hb, N₁.ist_e a b (hj ▸ hb)]
  have e'i : ∀ a (b : Fin r), N₀.j ≤ b.val → H.B (N₀.F'.e a) (N₀.ist b) = H.B (N₁.F'.e a) (N₁.ist b) := by
    intro a b hb
    by_cases ha : N₀.j ≤ a.val
    · rw [N₀.same a ha, N₁.same a (hj ▸ ha)]
      simp [ei a b hb, hc]
    have hl : a.val < r := lt_of_lt_of_le (not_le.1 ha) N₀.j_le
    exact (N₀.ist_e' ⟨a.val, hl⟩ b (not_le.1 ha) hb).trans
      (N₁.ist_e' ⟨a.val, hl⟩ b (hj ▸ not_le.1 ha) (hj ▸ hb)).symm
  have ww : ∀ p q : V × V, p.1 ∈ N₀.Wt → q.1 ∈ N₀.Wt → p.2 - p.1 ∈ N₀.F.X → q.2 - q.1 ∈ N₀.F.X → Cmp H p q := by
    intro p q hp hq hp' hq'
    have a1 := perp_X N₀.F (fun b => wt_e N₀ hq b.castSucc) _ hp'
    have a2 := B_swap0 H (perp_X N₀.F (fun b => wt_e N₀ hp b.castSucc) _ hq')
    have a3 := X_iso N₀.F hp' hq'
    simp only [map_sub, LinearMap.sub_apply] at a1 a2 a3
    unfold Cmp
    linear_combination -a1 - a2 - a3
  obtain ⟨s, hs, hS⟩ := exists_isometry (H := H)
    {p | (∃ a, p = (N₀.F.e a, N₁.F.e a)) ∨ (∃ a, p = (N₀.F'.e a, N₁.F'.e a)) ∨
      (∃ b : Fin r, N₀.j ≤ b.val ∧ p = (N₀.ist b, N₁.ist b)) ∨ (p.1 ∈ N₀.Wt ∧ p.2 ∈ N₁.Wt ∧ p.2 - p.1 ∈ N₀.F.X)}
    (by
      rintro p (⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, ha, rfl⟩ | ⟨p0, p1, p2⟩) q (⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨q0, q1, q2⟩)
      · exact ee a b
      · exact ee' a b
      · exact ei a b hb
      · exact (wt_e N₀ q0 a).trans (wt_e N₁ q1 a).symm
      · exact Cmp.symm (ee' b a)
      · exact e'e' a b
      · exact e'i a b hb
      · exact (wt_e' N₀ q0 a).trans (wt_e' N₁ q1 a).symm
      · exact Cmp.symm (ei b a ha)
      · exact Cmp.symm (e'i b a ha)
      · exact (N₀.ist_iso a b ha hb).trans (N₁.ist_iso a b (hj ▸ ha) (hj ▸ hb)).symm
      · exact (wt_ist N₀ q0 a ha).trans (wt_ist N₁ q1 a (hj ▸ ha)).symm
      · exact Cmp.symm ((wt_e N₀ p0 b).trans (wt_e N₁ p1 b).symm)
      · exact Cmp.symm ((wt_e' N₀ p0 b).trans (wt_e' N₁ p1 b).symm)
      · exact Cmp.symm ((wt_ist N₀ p0 b hb).trans (wt_ist N₁ p1 b (hj ▸ hb)).symm)
      · exact ww p q p0 q0 p2 q2)
    (by
      refine eq_top N₀ _ (fun a => ⟨_, Submodule.subset_span (Or.inl ⟨a, rfl⟩), rfl⟩)
        (fun a => ⟨_, Submodule.subset_span (Or.inr (Or.inl ⟨a, rfl⟩)), rfl⟩)
        (fun b hb => ⟨_, Submodule.subset_span (Or.inr (Or.inr (Or.inl ⟨b, hb, rfl⟩))), rfl⟩) fun w hw => ?_
      obtain ⟨u, hu, hx⟩ := decomp N₁ (perp_transfer h (wt_e N₀ hw))
      exact ⟨(w, u), Submodule.subset_span (Or.inr (Or.inr (Or.inr ⟨hw, hu, hX ▸ hx⟩))), rfl⟩)
    (by
      refine eq_top N₁ _ (fun a => ⟨_, Submodule.subset_span (Or.inl ⟨a, rfl⟩), rfl⟩)
        (fun a => ⟨_, Submodule.subset_span (Or.inr (Or.inl ⟨a, rfl⟩)), rfl⟩)
        (fun b hb => ⟨_, Submodule.subset_span (Or.inr (Or.inr (Or.inl ⟨b, hj ▸ hb, rfl⟩))), rfl⟩) fun w hw => ?_
      obtain ⟨u, hu, hx⟩ := decomp N₀ (perp_transfer (AdaptInv.sameGr_symm h) (wt_e N₁ hw))
      exact ⟨(u, w), Submodule.subset_span (Or.inr (Or.inr (Or.inr ⟨hu, hw, by
        simpa using Submodule.neg_mem _ hx⟩))), rfl⟩)
  have se : ∀ a, s (N₀.F.e a) = N₁.F.e a := fun a => hS (_, _) (Or.inl ⟨a, rfl⟩)
  refine ⟨s, ⟨hs, s.bijective, fun a => ?_, fun y hy => ?_⟩,
    fun a => ⟨se a, hS (_, _) (Or.inr (Or.inl ⟨a, rfl⟩))⟩⟩
  · rw [LinearEquiv.coe_coe, se]
    exact h a.castSucc
  · let M : Submodule K V := N₀.F.X.comap ((s : V →ₗ[K] V) - LinearMap.id)
    have m1 : ∀ a, N₀.F.e a ∈ M := fun a => by
      change s (N₀.F.e a) - N₀.F.e a ∈ N₀.F.X
      rw [se]
      exact Xa_le_X _ _ (h a)
    have m2 : N₀.F.X ≤ M := Submodule.span_le.2 (by rintro _ ⟨b, -, rfl⟩; exact m1 _)
    have m3 : N₀.Wt ≤ M := fun w hw => by
      obtain ⟨u, hu, hx⟩ := decomp N₁ (perp_transfer h (wt_e N₀ hw))
      change s w - w ∈ N₀.F.X
      rw [show s w = u from hS (w, u) (Or.inr (Or.inr (Or.inr ⟨hw, hu, hX ▸ hx⟩))), ← hX]
      exact hx
    obtain ⟨u, hu, hx⟩ := decomp N₀ (w := y + star (H.B N₀.F.z y / N₀.F.T) • N₀.F.z) (fun a => by
      refine Fin.lastCases ?_ (fun a => ?_) a
      · have := N₀.F.hT
        change H.B N₀.F.z _ = 0
        simp only [map_add (f := _), LinearMap.map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul, pairing_lastVector_lastVector]
        field_simp
        ring
      · simp [hy a, pairing_isotropicSpan_lastVector N₀.F (e_mem_X _ a)])
    have m4 : y ∈ M := by
      have := M.sub_mem (M.sub_mem (m3 hu) (m2 hx))
        (M.smul_mem (star (H.B N₀.F.z y / N₀.F.T)) (m1 (Fin.last r)))
      simpa [FlagD.z] using this
    exact m4

end GlobalTheory.DegAsm.NFUnique

namespace GlobalTheory.DegAsm

theorem nf_unique : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F : FlagD H r) (N₀ N₁ : NF H r), SameGr F N₀.F → SameGr F N₁.F → N₀.j = N₁.j → N₀.c = N₁.c → N₀.T = N₁.T → pairM N₀.F N₀.F' N₀.j = pairM N₁.F N₁.F' N₁.j → ∃ s : V ≃ₗ[K] V, F.InN (s : V →ₗ[K] V) ∧ ∀ a, s (N₀.F.e a) = N₁.F.e a ∧ s (N₀.F'.e a) = N₁.F'.e a := by
  intro K V _ _ _ _ _ _ _ _ H _ r F N₀ N₁ h₀ h₁ hj hc hT hM
  have h : SameGr N₀.F N₁.F := fun a => by
    rw [AdaptInv.xa_eq h₀]
    simpa using Submodule.sub_mem _ (h₁ a) (h₀ a)
  obtain ⟨s, hs, he⟩ := NFUnique.main N₀ N₁ h hj hc hT hM
  exact ⟨s, AdaptInv.inN_of (AdaptInv.sameGr_symm h₀) _ hs, he⟩

end GlobalTheory.DegAsm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesFirstTypeAmpSqBound
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FirstType

theorem geom_le (x : ℝ) (hx : 2 ≤ x) (n : ℕ) : ∑ i ∈ Finset.range (n + 1), x ^ i ≤ 2 * x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have : 0 ≤ x ^ n := by positivity
    nlinarith

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}

theorem mass_le_sum (S : Frames L r k) (d : S.Datum) (P : Submodule L.O S.V → Prop) {ι : Type}
    (s : Finset ι) (Q : ι → Submodule L.O S.V → Prop)
    (h : ∀ Λ, S.IsTerm d Λ → P Λ → ∃ i ∈ s, Q i Λ) : S.mass d P ≤ ∑ i ∈ s, S.mass d (Q i) := by
  unfold Frames.mass
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun o => ?_
  split_ifs with ho
  · obtain ⟨i, hi, hq⟩ := h _ ho.1 ho.2
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) hi)
    rw [if_pos ⟨ho.1, hq⟩]
  · exact zero_le

theorem mass_mono (S : Frames L r k) (d : S.Datum) (P Q : Submodule L.O S.V → Prop)
    (h : ∀ Λ, P Λ → Q Λ) : S.mass d P ≤ S.mass d Q := by
  simpa using mass_le_sum S d P ({()} : Finset Unit) (fun _ => Q) (fun Λ _ hp => ⟨(), by simp, h Λ hp⟩)

theorem first_type_bound : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ β : ℕ, (S.ampSq fun d Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β) ≤ ENNReal.ofReal (2 * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * S.Hp ^ (4 * (r + 1))) * (S.q : ℝ) ^ (-((k : ℤ) - 1))) * S.nn := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk β
  have hk1 : 1 ≤ k := by omega
  obtain ⟨hamp, hbasic⟩ := BasicIneq.basic_inequality L r k S hk1
  have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
  have hqR : (2 : ℝ) ≤ S.q := by exact_mod_cast hq
  have hH : 0 ≤ S.Hp := by unfold Frames.Hp; positivity
  set A₀ : ℝ := S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) with hA₀
  set A₁ : ℝ := 4 * S.Hp ^ (4 * (r + 1)) with hA₁
  have hA0 : 0 ≤ A₀ := by positivity
  have hA1 : 0 ≤ A₁ := by positivity
  by_cases hex : ∃ d Λ, S.IsTerm d Λ ∧ ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β
  · obtain ⟨d₀, Λ₀, ht₀, hb₀, -, hβ₀⟩ := hex
    obtain ⟨-, -, -, -, -, ⟨m, -, hm⟩, hiff, -⟩ := Defect.exponents_and_defect L r k S d₀ Λ₀ ht₀
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := by
      rcases m with _ | n
      · exact absurd (hiff.2 (by simpa using hm)) hb₀
      · exact ⟨n, rfl⟩
    have hβ : β = S.q ^ (n + 1) := hβ₀ ▸ hm
    obtain ⟨e, rfl⟩ : ∃ e, k = e + 1 := ⟨k - 1, by omega⟩
    have hx : (2 : ℝ) ≤ (S.q : ℝ) ^ e := by
      have : (S.q : ℝ) ^ 1 ≤ (S.q : ℝ) ^ e := pow_le_pow_right₀ (by linarith) (by omega)
      rw [pow_one] at this
      linarith
    have hmass : ∀ d, S.mass d (fun Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β) ≤
        ENNReal.ofReal (A₀ * (2 * ((S.q : ℝ) ^ e) ^ n)) := by
      intro d
      refine (mass_le_sum S d _ (Finset.range (n + 1)) (fun i Λ => S.cardI d Λ = S.q ^ i) ?_).trans ?_
      · rintro Λ ht ⟨h1, h2, h3⟩
        obtain ⟨⟨i, hi⟩, -, hle⟩ := SmallImage.small_image L r (e + 1) S d Λ ht
        have h4 := hle h1 h2
        rw [hi, h3, hβ, ← pow_succ'] at h4
        have := (Nat.pow_le_pow_iff_right (by omega)).1 h4
        exact ⟨i, Finset.mem_range.2 (by omega), hi⟩
      · refine (Finset.sum_le_sum fun i _ => (_root_.GlobalTheory.HL.MassGlue.mass_le_and_finite L r (e + 1) S hk1 d).1 (S.q ^ i)).trans ?_
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ hA0
        refine le_trans (le_of_eq ?_) (geom_le _ hx n)
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Nat.add_sub_cancel, Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm]
    have h1 := hbasic (fun d Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β) _ 1 zero_le_one hmass
      (fun d => by simpa using hamp d _)
    have h2 : (S.sumData fun d => S.mass d (fun Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β)) ≤
        S.sumData fun d => S.mass d fun Λ => S.be d Λ = β := by
      unfold Frames.sumData
      refine ENNReal.tsum_le_tsum fun o => ?_
      gcongr
      exact mass_mono S _ _ _ fun Λ h => h.2.2
    have h3 := _root_.GlobalTheory.DefectShare.mass_defect_order_le L r (e + 1) S hk β (by rw [hβ]; exact Nat.one_le_pow _ _ (by omega))
    refine h1.trans ((mul_le_mul_right (h2.trans h3) _).trans (le_of_eq ?_))
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    have hq0 : (S.q : ℝ) ≠ 0 := by positivity
    have : (-(((e + 1 : ℕ) : ℤ) - 1)) = -(e : ℤ) := by push_cast; ring
    rw [this, zpow_neg, zpow_natCast, hβ, Nat.add_sub_cancel, Nat.cast_pow, ← hA₁]
    field_simp
    ring
  · have hmass : ∀ d, S.mass d (fun Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β) ≤
        ENNReal.ofReal 0 := by
      intro d
      simpa using mass_le_sum S d (fun Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β)
        (∅ : Finset Unit) (fun _ _ => True) (fun Λ ht hp => absurd ⟨d, Λ, ht, hp⟩ hex)
    have h1 := hbasic (fun d Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β) _ 1 zero_le_one hmass
      (fun d => by simpa using hamp d _)
    refine h1.trans ?_
    simp

end GlobalTheory.HL.FirstType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HilbertSchmidtLowerBoundInverseDifferent
section
open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset

namespace GlobalTheory.DualBound

theorem opNorm_sq_le_hs {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℂ) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖ ^ 2 ≤ ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  have hS : 0 ≤ ∑ i, ∑ j, ‖M i j‖ ^ 2 := by positivity
  have h : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖ ≤
      Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, Real.sq_sqrt hS, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M) x) i‖ ≤
        ∑ j, ‖M i j‖ * ‖x j‖ := by
      have : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M) x) i =
          ∑ j, M i j * x j := by
        simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
      rw [this]
      exact (norm_sum_le _ _).trans (le_of_eq (by simp))
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  calc _ ≤ (Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt hS

theorem card_mul_geom_sq_le {ι : Type} [Fintype ι] [Nonempty ι] (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (Fintype.card ι : ℝ) * ((∏ i, z i) ^ ((1 : ℝ) / (Fintype.card ι : ℝ))) ^ 2 ≤
      ∑ i, z i ^ 2 := by
  have hf : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : ι => (1 : ℝ) / (Fintype.card ι : ℝ)) (fun i => z i ^ 2)
    (fun _ _ => by positivity) (by simp [hf.ne']) (fun _ _ => by positivity)
  have hp : 0 ≤ ∏ i, z i := Finset.prod_nonneg fun i _ => hz i
  rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity), Finset.prod_pow, ← Finset.mul_sum] at h
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp, mul_comm (1 / _ : ℝ), Real.rpow_mul hp,
    Real.rpow_natCast]
  calc _ ≤ (Fintype.card ι : ℝ) * (1 / (Fintype.card ι : ℝ) * ∑ i, z i ^ 2) :=
        mul_le_mul_of_nonneg_left h hf.le
    _ = _ := by field_simp

theorem size_different_smul {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
    {a : ℕ} (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (hX : ∀ w, IsUnit (X w).det)
    {N : Submodule (𝓞 K) (Fin a → K)} (hN : N.FG) (hN0 : N ≠ ⊥) :
    Formalism.HN.size (Pi.basisFun K (Fin a)) X (differentIdeal ℤ (𝓞 K) • N) =
      Formalism.HN.size (Pi.basisFun K (Fin a)) X N * |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ))) := by
  have hd : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  have hrk : rkK (differentIdeal ℤ (𝓞 K) • N) = rkK N := by
    unfold rkK; rw [Formalism.HN.DualPolygon.twist_span_smul N _ hd]
  have hnorm : (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) = |(NumberField.discr K : ℝ)| := by
    rw [NumberField.absNorm_differentIdeal K (𝓞 K), Nat.cast_natAbs, Int.cast_abs]
  have hj : (rkK N : ℝ) ≠ 0 := by exact_mod_cast (Formalism.LFunctionChainParameters.slopeLatticeData.rkK_pos hN0).ne'
  have hf : (Formalism.HN.nPl K : ℝ) ≠ 0 := by
    have : 0 < Formalism.HN.nPl K := Fintype.card_pos
    exact_mod_cast this.ne'
  unfold Formalism.HN.size
  rw [Formalism.LFunctionChainParameters.slopeLatticeData.ht_ideal _ X hX hN hd, hrk, hnorm,
    Real.mul_rpow (Formalism.LFunctionChainParameters.slopeLatticeData.ht_pos _ X hX hN).le (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  congr 2
  field_simp

theorem hs_lower_bound :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (a b : ℕ) (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (X' : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ) (A : Submodule (𝓞 K) (Fin a → K)) (B : Submodule (𝓞 K) (Fin b → K)) (lo hi : ℝ), (∀ w, IsUnit (X w).det) → (∀ w, IsUnit (X' w).det) → A.FG → B.FG → 0 < lo → (∀ N, N ≤ A → N ≠ ⊥ → lo ≤ Formalism.HN.size (Pi.basisFun K (Fin a)) X N) → Formalism.HN.largestSize (Pi.basisFun K (Fin b)) X' B ≤ hi → ∀ ψ : Matrix (Fin a) (Fin b) K, (∃ y ∈ B, ψ *ᵥ y ≠ 0) → (∀ δ ∈ differentIdeal ℤ (𝓞 K), ∀ y ∈ B, δ • (ψ *ᵥ y) ∈ A) → (Formalism.HN.nPl K : ℝ) * (lo / (|(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ))) * hi)) ^ 2 ≤ ∑ w, ∑ i, ∑ j, ‖((X w)⁻¹ * ψ.map w.embedding * X' w) i j‖ ^ 2 := by
  intro K _ _ _ _ a b X X' A B lo hi hX hX' _ hB hlo hA hhi ψ ⟨y, hyB, hy⟩ hψ
  set φ : (Fin b → K) →ₗ[K] (Fin a → K) := Matrix.toLin' ψ with hφ
  set A' : Submodule (𝓞 K) (Fin a → K) := B.map (φ.restrictScalars (𝓞 K)) with hA'
  set rd : ℝ := |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ))) with hrd
  have hrdpos : 0 < rd :=
    Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero K)) _
  have hA'fg : A'.FG := hB.map _
  have hA'0 : A' ≠ ⊥ := by
    intro h
    have : ψ *ᵥ y ∈ A' := ⟨y, hyB, by simp [hφ]⟩
    rw [h] at this
    exact hy this
  have hB0 : B ≠ ⊥ := by
    rintro rfl
    exact hA'0 (by rw [hA', Submodule.map_bot])
  have hd : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  have hleast : lo / rd ≤ leastSize (Pi.basisFun K (Fin a)) X A' := by
    refine le_csInf ⟨_, A', le_rfl, hA'0, rfl⟩ ?_
    rintro t ⟨N, hN, hN0, rfl⟩
    have hNfg : N.FG := Submodule.FG.of_le hA'fg hN
    have h1 : differentIdeal ℤ (𝓞 K) • N ≤ A := by
      refine Submodule.smul_le.2 fun δ hδ v hv => ?_
      obtain ⟨z, hz, rfl⟩ := hN hv
      simpa [hφ] using hψ δ hδ z hz
    have h2 : differentIdeal ℤ (𝓞 K) • N ≠ ⊥ := by
      intro h
      have h3 := Formalism.HN.DualPolygon.twist_span_smul N _ hd
      rw [h] at h3
      apply hN0
      rw [eq_bot_iff]
      intro v hv
      have : v ∈ Submodule.span K (N : Set (Fin a → K)) := Submodule.subset_span hv
      rw [← h3] at this
      simpa using this
    have h3 := hA _ h1 h2
    rw [size_different_smul X hX hNfg hN0] at h3
    rw [div_le_iff₀ hrdpos]
    exact h3
  have hLpos : 0 < Formalism.HN.largestSize (Pi.basisFun K (Fin b)) X' B := by
    rw [(sizeMu K _ _ (Pi.basisFun K (Fin b)) X' hX' B hB hB0).2.2.2.2.1]
    exact Real.exp_pos _
  have hM := sizeIneq K _ _ _ _ (Pi.basisFun K (Fin b)) X' (Pi.basisFun K (Fin a)) X hX' hX φ B A'
    hB hA'fg le_rfl hA'0
  have hhipos : 0 < hi := hLpos.trans_le hhi
  have h4 : lo / (rd * hi) ≤
      (∏ v, opNormAt (Pi.basisFun K (Fin b)) X' (Pi.basisFun K (Fin a)) X v φ) ^
        ((1 : ℝ) / (Formalism.HN.nPl K : ℝ)) := by
    refine le_trans ?_ hM
    rw [← div_div]
    exact div_le_div₀ ((div_pos hlo hrdpos).le.trans hleast) hleast hLpos hhi
  have h5 := card_mul_geom_sq_le
    (fun v => opNormAt (Pi.basisFun K (Fin b)) X' (Pi.basisFun K (Fin a)) X v φ)
    (fun v => norm_nonneg _)
  calc _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h4 2) (Nat.cast_nonneg _)
    _ ≤ _ := h5
    _ ≤ _ := by
      refine Finset.sum_le_sum fun w _ => ?_
      have h6 : LinearMap.toMatrix (Pi.basisFun K (Fin b)) (Pi.basisFun K (Fin a)) φ = ψ := by
        ext i j
        simp [hφ]
      unfold opNormAt
      rw [h6]
      exact opNorm_sq_le_hs _

end GlobalTheory.DualBound
end

