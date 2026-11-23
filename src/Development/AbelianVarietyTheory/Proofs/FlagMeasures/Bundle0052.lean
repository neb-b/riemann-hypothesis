module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0048
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0044

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameMoveCharacterNeOne
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MoveChar

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem coords {g : Fin (r + 1) → S.V} {n : S.GLV} (hn : n ∈ S.Nof g) (j : Fin r) {x : S.V}
    (hx : x ∈ S.spanTo g (j + 1)) :
    ∃ c : Fin (r + 1) → E, (∀ i : Fin (r + 1), (j : ℕ) + 1 ≤ i → c i = 0) ∧ x = ∑ i, c i • n (g i) := by
  have h1 : ∀ v, n v ∈ S.spanTo g (j + 1) ↔ v ∈ S.spanTo g (j + 1) :=
    (Subgroup.mem_iInf.1 hn.1.2 j).1
  obtain ⟨y, rfl⟩ := n.surjective x
  have hy := (h1 y).1 hx
  clear hx
  induction hy using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, hi, rfl⟩ := hv
    refine ⟨Pi.single i 1, fun i' hi' => Pi.single_eq_of_ne ?_ _, ?_⟩
    · rintro rfl
      exact absurd hi (not_lt.2 hi')
    · simp [Pi.single_apply]
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨c, h, e⟩ := ha
    obtain ⟨c', h', e'⟩ := hb
    exact ⟨c + c', fun i hi => by simp [h i hi, h' i hi],
      by rw [map_add (f := _), e, e']; simp [add_smul, Finset.sum_add_distrib]⟩
  | smul t a _ ha =>
    obtain ⟨c, h, e⟩ := ha
    exact ⟨t • c, fun i hi => by simp [h i hi],
      by rw [map_smul, e]; simp [Finset.smul_sum, mul_smul]⟩

theorem uniq {g g' : Fin (r + 1) → S.V} (hl : LinearIndependent E (Sum.elim g g'))
    {a a' b b' : Fin (r + 1) → E}
    (h : ∑ i, a i • g i + ∑ i, a' i • g' i = ∑ i, b i • g i + ∑ i, b' i • g' i) :
    a = b ∧ a' = b' := by
  have := Fintype.linearIndependent_iffₛ.1 hl (Sum.elim a a') (Sum.elim b b')
    (by simpa [Fintype.sum_sum_type] using h)
  exact ⟨funext fun i => this (.inl i), funext fun i => this (.inr i)⟩

theorem lev_le_iff {g g' : Fin (r + 1) → S.V} (hl : LinearIndependent E (Sum.elim g g'))
    (a a' : Fin (r + 1) → E) (j : ℕ) :
    S.lev g g' (∑ i, a i • g i + ∑ i, a' i • g' i) ≤ j ↔
      ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (a i) (a' i) := by
  refine ⟨fun h i hi => ?_, fun h => Nat.sInf_le ⟨a, a', rfl, h⟩⟩
  have hne : {j : ℕ | ∃ al al' : Fin (r + 1) → E,
      ∑ i, a i • g i + ∑ i, a' i • g' i = ∑ i, al i • g i + ∑ i, al' i • g' i ∧
      ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (al i) (al' i)}.Nonempty :=
    ⟨r + 1, a, a', rfl, fun i hi => absurd i.2 (not_lt.2 hi)⟩
  obtain ⟨b, b', e, hb⟩ := Nat.sInf_mem hne
  obtain ⟨rfl, rfl⟩ := uniq S hl e
  exact hb i (le_trans h hi)

theorem exists_family {g g' : Fin (r + 1) → S.V} (hl : LinearIndependent E (Sum.elim g g'))
    {J : ℕ} (hJ : J ≤ r + 1) : ∃ y : Fin (J + J) → S.V, LinearIndependent E y ∧
      Submodule.span E (Set.range y) = S.spanTo g J ⊔ S.spanTo g' J := by
  refine ⟨Sum.elim g g' ∘ (Sum.map (Fin.castLE hJ) (Fin.castLE hJ) ∘ finSumFinEquiv.symm),
    hl.comp _ (((Fin.castLE_injective hJ).sumMap (Fin.castLE_injective hJ)).comp
      finSumFinEquiv.symm.injective), ?_⟩
  have e : ∀ g : Fin (r + 1) → S.V, Set.range (g ∘ Fin.castLE hJ) = g '' {i | (i : ℕ) < J} := by
    intro g
    rw [Set.range_comp, Fin.range_castLE]
  rw [← Function.comp_assoc, finSumFinEquiv.symm.surjective.range_comp, Sum.elim_comp_map,
    Set.Sum.elim_range, e, e, Submodule.span_union]
  rfl

end GlobalTheory.HL.MoveChar

theorem GlobalTheory.HL.MoveChar.chi_ne_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x ∈ S.spanTo S.f (j + 1), ∀ x' ∈ S.spanTo S.f' (j + 1), S.InTh Λ (x + x') → S.lev (S.fr d Λ) (S.fr' d Λ) (x + x') = j + 1 → ∀ al al' : Fin (r + 1) → E, x = ∑ i, al i • S.fr d Λ i → x' = ∑ i, al' i • S.fr' d Λ i → ∃ u ∈ Λ, u ∈ perp L S.Hm (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)) ∧ L.psi0 (-(algebraMap F E S.th⁻¹ * S.h (al j.castSucc • S.fr d Λ j.succ + al' j.castSucc • S.fr' d Λ j.succ) u)) ≠ 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hFF x hx x' hx' _ hlev al al' ex ex'
  obtain ⟨hSD, hW, -, h1, h2, hl, -⟩ := TermBasic.term_basic L r k S d Λ hT
  obtain ⟨hl0, -, -, -, -, hth, -⟩ := GlobalTheory.FrameBasic.main L r k S
  obtain ⟨-, -, hn, hn', -⟩ := hW

  have hRR : ¬ S.RR (al j.castSucc) (al' j.castSucc) := by
    intro hR
    obtain ⟨c, hc, e⟩ := MoveChar.coords S hn j hx
    obtain ⟨c', hc', e'⟩ := MoveChar.coords S hn' j hx'
    obtain ⟨rfl, rfl⟩ := MoveChar.uniq S hl (a := al) (a' := al') (b := c) (b' := c')
      (by rw [← ex, ← ex']; exact congrArg₂ (· + ·) e e')
    have : S.lev (S.fr d Λ) (S.fr' d Λ) (x + x') ≤ j := by
      rw [ex, ex', MoveChar.lev_le_iff S hl]
      intro i hi
      rcases hi.eq_or_lt with hi | hi
      · rwa [show i = j.castSucc from Fin.ext hi.symm]
      · rw [hc i hi, hc' i hi]
        exact ⟨L.O.zero_mem, 0, L.O.zero_mem, by simp⟩
    omega
  by_contra hcon
  push Not at hcon
  set z := al j.castSucc • S.fr d Λ j.succ + al' j.castSucc • S.fr' d Λ j.succ with hz
  obtain ⟨y, hy, ey⟩ := MoveChar.exists_family S hl0 (J := j + 1) (by omega)
  have hd := (DualInter.dual_inter L S.Hm S.herm Λ hSD _ y hy).2.1 (algebraMap F E S.th⁻¹ • z)
  rw [ey] at hd
  obtain ⟨a, ha, haY⟩ := hd.1 fun u hu huY => by
    have : -(algebraMap F E S.th⁻¹ * S.h z u) ∈ L.O := by
      refine (L.additive_character_dual_ring _).1 fun c hc => ?_
      have := hcon (L.cj c • u) (Λ.smul_mem ⟨_, GlobalTheory.UnramOrder.cj_mem L hc⟩ hu)
        (Submodule.smul_mem _ _ huY)
      rw [← this, Frames.h, Frames.h, DualInter.smul_r, L.cj_cj]
      congr 1
      ring
    rw [← DualInter.cj_hf S.herm, DualInter.smul_l]
    exact GlobalTheory.UnramOrder.cj_mem L (neg_mem_iff.1 this)
  have hjr : (j : ℕ) + 1 ≤ r + 1 := by omega
  have hzM : z ∈ S.ME :=
    Submodule.add_mem_sup
      (Submodule.smul_mem _ _ ((h1 (r + 1) le_rfl _).2 (Submodule.subset_span ⟨j.succ, j.succ.2, rfl⟩)).2)
      (Submodule.smul_mem _ _ ((h2 (r + 1) le_rfl _).2 (Submodule.subset_span ⟨j.succ, j.succ.2, rfl⟩)).2)
  have haM : a ∈ S.ME := by
    have := S.ME.sub_mem (S.ME.smul_mem (algebraMap F E S.th⁻¹) hzM)
      (sup_le_sup (TermBasic.spanTo_mono S S.f hjr) (TermBasic.spanTo_mono S S.f' hjr) haY)
    rwa [sub_sub_cancel] at this
  have hla : S.levC d Λ a ≤ j + 1 := hFF.2.2.1 a ⟨ha, haM⟩
  obtain ⟨v, hv, v', hv', e0⟩ := Submodule.mem_sup.1 (Submodule.smul_mem _ (algebraMap F E S.th) haY)
  obtain ⟨c, hc, e⟩ := MoveChar.coords S hn j hv
  obtain ⟨c', hc', e'⟩ := MoveChar.coords S hn' j hv'
  have key : algebraMap F E S.th • a =
      ∑ i, (Pi.single j.succ (al j.castSucc) - c : Fin (r + 1) → E) i • S.fr d Λ i +
        ∑ i, (Pi.single j.succ (al' j.castSucc) - c' : Fin (r + 1) → E) i • S.fr' d Λ i := by
    rw [smul_sub, smul_smul, ← map_mul, mul_inv_cancel₀ hth, map_one, one_smul] at e0
    have e1 : v = ∑ i, c i • S.fr d Λ i := e
    have e2 : v' = ∑ i, c' i • S.fr' d Λ i := e'
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, ← e1, ← e2, Pi.single_apply, ite_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [sub_add_sub_comm, e0, ← hz, sub_sub_cancel]
  rw [Frames.levC, key, MoveChar.lev_le_iff S hl] at hla
  have := hla j.succ (by simp)
  rw [Pi.sub_apply, Pi.sub_apply, hc _ (by simp), hc' _ (by simp), Pi.single_eq_same, Pi.single_eq_same,
    sub_zero, sub_zero] at this
  exact hRR this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesLocalHeightEqResidueCard
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordHeight

section Val

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)
  (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
include hϖ

theorem vE_one : vE L ϖ (algebraMap F E 1) = 0 := by
  have h := (GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).1 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  omega

theorem vE_unit (x : F) (hx : x ≠ 0) (h1 : algebraMap F E x ∈ L.O)
    (h2 : ∃ y ∈ L.O, algebraMap F E x * y = 1) : vE L ϖ (algebraMap F E x) = 0 := by
  obtain ⟨hadd, -, hint, -⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  obtain ⟨-, -, -, -, hO, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  obtain ⟨y, hy, hxy⟩ := h2
  have e : y = algebraMap F E x⁻¹ := by
    calc y = algebraMap F E (x⁻¹ * x) * y := by rw [inv_mul_cancel₀ hx, map_one, one_mul]
      _ = algebraMap F E x⁻¹ := by rw [map_mul, mul_assoc, hxy, mul_one]
  have a1 := (hint x hx).2 ((hO x).1 h1)
  have a2 := (hint x⁻¹ (inv_ne_zero hx)).2 ((hO _).1 (e ▸ hy))
  have a3 := hadd x x⁻¹ hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, vE_one L ϖ hϖ] at a3
  omega

theorem vE_pow (x : F) (hx : x ≠ 0) (n : ℕ) :
    vE L ϖ (algebraMap F E (x ^ n)) = n * vE L ϖ (algebraMap F E x) := by
  induction n with
  | zero => simpa using vE_one L ϖ hϖ
  | succ n ih =>
    rw [pow_succ, (GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).1 _ _ (pow_ne_zero n hx) hx, ih]
    push_cast
    ring

theorem vE_neg_one : vE L ϖ (algebraMap F E (-1)) = 0 := by
  have h := vE_pow L ϖ hϖ (-1) (by simp) 2
  rw [neg_one_sq, vE_one L ϖ hϖ] at h
  omega

omit [IsNonarchimedeanLocalField F] [CharZero F] hϖ in
theorem norm_mem (x : E) (hx : IsUnit x) : ∃ c : F, c ≠ 0 ∧ x * L.cj x = algebraMap F E c := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)
  obtain ⟨c, hc⟩ := (L.cj_fix (x * L.cj x)).1 (by rw [map_mul, L.cj_cj, mul_comm])
  refine ⟨c, ?_, hc.symm⟩
  rintro rfl
  rw [map_zero] at hc
  exact (hx.mul (hx.map L.cj)).ne_zero hc.symm

end Val

section Transport

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
include c

theorem Dm_eq (l : Fin (r + 2)) : P.Dm l = S.D l := by
  have hZ : H.Zhat P.A.f P.B.f = S.Zh := by
    ext a b
    simp only [HermSp.Zhat, Frames.Zh, Matrix.of_apply, c.f_eq, c.f'_eq, c.h_eq]
  unfold LocNG.FPair.Dm HermSp.Dl Frames.D lead
  rw [dite_eq_left (Nat.lt_succ_iff.mp l.2), hZ]

theorem Gv_eq : P.Gv = S.G := by
  have h1 := Dm_eq c (Fin.last (r + 1))
  have h2 := Dm_eq c (Fin.last r).castSucc
  unfold LocNG.FPair.Gv HermSp.Gdet HermSp.normE Frames.G
  rw [← h1, ← h2, c.T_eq, c.T'_eq]
  rfl

theorem theta_eq : LocNG.theta M = S.th := by
  unfold LocNG.theta Frames.th
  cases h : M.split with
  | none => simp [c.gg_none h]
  | some g =>
    obtain ⟨h1, h2⟩ := c.gg_some g h
    simp [h1, h2]

end Transport

theorem height_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), P.Hp = S.Hp ∧ LocNG.qF F = S.q ∧ (P.PrimeTo → S.gg = false ∧ vE M.L S.ϖ S.G = 0 ∧ ∀ l, S.D l ≠ 0 → vE M.L S.ϖ (S.D l * M.L.cj (S.D l)) = 0) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c
  have := hM.loc
  have := hM.char0
  obtain ⟨hq, hmod⟩ := GlobalTheory.BaseModule.modK_algebraMap M hM S.ϖ S.ϖ_irr
  obtain ⟨-, -, ⟨g, hg0, hg⟩, -, hD, hth, -⟩ := GlobalTheory.FrameBasic.main M.L r k S
  obtain ⟨hadd, hvp, -, -⟩ := GlobalTheory.UnramVal.vE_valuation M.L S.ϖ S.ϖ_irr
  obtain ⟨-, hcj, -, -, -, -, hq2, -⟩ := GlobalTheory.UnramOrder.order_facts M.L S.ϖ S.ϖ_irr
  have hnt : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [M.L.rank]; norm_num)
  have hgram := GlobalTheory.det_gram_frame_generators M hM H r k P
  rw [theta_eq c, Gv_eq c, hg] at hgram
  have hvth : vE M.L S.ϖ (algebraMap F E S.th) = S.vth := by
    unfold Frames.th Frames.vth
    split_ifs
    · exact hvp
    · exact vE_one M.L S.ϖ S.ϖ_irr
  have hends : ∀ l : Fin (r + 2), (l : ℕ) ∈ P.ends ↔ l ≠ 0 ∧ S.D l ≠ 0 := by
    intro l
    unfold LocNG.FPair.ends
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [Dm_eq c]
    constructor
    · rintro ⟨-, h1, h2⟩
      refine ⟨?_, h2.ne_zero⟩
      rintro rfl
      simp at h1
    · rintro ⟨h1, h2⟩
      refine ⟨l.2, ?_, hD l h2⟩
      exact Nat.one_le_iff_ne_zero.mpr fun h => h1 (Fin.ext h)
  refine ⟨?_, hq, ?_⟩
  · have hq0 : (0 : ℝ) < (resQ S.ϖ : ℝ) := by
      have : 0 < resQ S.ϖ := by omega
      exact_mod_cast this
    set d : F := (-1) ^ (r + 1) * g * (S.th ^ (2 * (r + 1)))⁻¹ with hd
    have hp0 : S.th ^ (2 * (r + 1)) ≠ 0 := pow_ne_zero _ hth
    have hs0 : ((-1 : F) ^ (r + 1)) ≠ 0 := pow_ne_zero _ (by simp)
    have hd0 : d ≠ 0 := mul_ne_zero (mul_ne_zero hs0 hg0) (inv_ne_zero hp0)
    have hdet : (H.gram P.MMgen).det = algebraMap F E d := by
      calc (H.gram P.MMgen).det
          = (H.gram P.MMgen).det * algebraMap F E (S.th ^ (2 * (r + 1)) * (S.th ^ (2 * (r + 1)))⁻¹) := by
            rw [mul_inv_cancel₀ hp0, map_one, mul_one]
        _ = algebraMap F E d := by
            rw [map_mul, ← mul_assoc, map_pow, hgram, hd]
            simp only [map_mul, map_pow, map_neg, map_one]
    have hva : vE M.L S.ϖ (algebraMap F E d) = S.a := by
      have e : d * S.th ^ (2 * (r + 1)) = (-1) ^ (r + 1) * g := by
        rw [hd, mul_assoc, inv_mul_cancel₀ hp0, mul_one]
      have h1 := hadd _ _ hd0 hp0
      rw [e, hadd _ _ hs0 hg0, vE_pow M.L S.ϖ S.ϖ_irr _ hth, vE_pow M.L S.ϖ S.ϖ_irr _ (by simp),
        vE_neg_one M.L S.ϖ S.ϖ_irr, hvth] at h1
      unfold Frames.a
      rw [hg]
      push_cast at h1
      linarith
    have hprod : ∏ l ∈ P.ends, M.modK (P.Dm l * M.L.cj (P.Dm l)) = (resQ S.ϖ : ℝ) ^ (-(2 * S.vD)) := by
      have hsub : P.ends ⊆ Finset.range (r + 2) := by
        unfold LocNG.FPair.ends
        exact @Finset.filter_subset _ _ (_) _
      rw [← Finset.inter_eq_right.mpr hsub, ← Finset.prod_ite_mem, Finset.prod_range]
      unfold Frames.vD
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      have hz : ∀ (s : Finset (Fin (r + 2))) (f : Fin (r + 2) → ℤ),
          (resQ S.ϖ : ℝ) ^ (∑ i ∈ s, f i) = ∏ i ∈ s, (resQ S.ϖ : ℝ) ^ f i := by
        intro s f
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hq0.ne', ih]
      rw [hz]
      refine Finset.prod_congr rfl fun l _ => ?_
      by_cases hl : l ≠ 0 ∧ S.D l ≠ 0
      · rw [if_pos ((hends l).2 hl), if_pos hl, Dm_eq c]
        obtain ⟨n, hn0, hn⟩ := norm_mem M.L _ (hD l hl.2)
        rw [hn, hmod n hn0]
      · rw [if_neg (fun h => hl ((hends l).1 h)), if_neg hl]
        simp
    unfold LocNG.FPair.Hp Frames.Hp Frames.q
    rw [hprod, hdet, theta_eq c, hmod _ hth, hmod _ hd0, hvth, hva, ← zpow_add₀ hq0.ne',
      ← zpow_add₀ hq0.ne', ← Real.rpow_intCast, ← Real.rpow_mul hq0.le, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  · rintro ⟨h1, h2, h3⟩
    refine ⟨c.gg_none h1, ?_, fun l hl => ?_⟩
    · rw [Gv_eq c, hg] at h2
      rw [hg]
      exact vE_unit M.L S.ϖ S.ϖ_irr g hg0 h2.1 h2.2
    · have hu : LocNG.IsUnitO M (S.D l) := by
        by_cases h0 : l = 0
        · have : S.D l = 1 := by
            subst h0
            unfold Frames.D lead
            exact Matrix.det_isEmpty (n := Fin 0)
          rw [this]
          exact ⟨M.L.O.one_mem, 1, M.L.O.one_mem, mul_one 1⟩
        · have := h3 l ((hends l).2 ⟨h0, hl⟩)
          rwa [Dm_eq c] at this
      obtain ⟨n, hn0, hn⟩ := norm_mem M.L _ (hD l hl)
      obtain ⟨hm, y, hy, hxy⟩ := hu
      rw [hn]
      refine vE_unit M.L S.ϖ S.ϖ_irr n hn0 ?_ ⟨y * M.L.cj y, M.L.O.mul_mem hy (hcj y hy).1, ?_⟩
      · rw [← hn]
        exact M.L.O.mul_mem hm (hcj _ hm).1
      · rw [← hn, mul_mul_mul_comm, ← map_mul, hxy, map_one, mul_one]

end GlobalTheory.HL.CoordHeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalFramesJointGramInvMulSelf
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GamInv

theorem hf_add_right {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) {n : ℕ}
    (H : Matrix (Fin n) (Fin n) E) (x y z : Fin n → E) :
    hf L H x (y + z) = hf L H x y + hf L H x z := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_right {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) {n : ℕ}
    (H : Matrix (Fin n) (Fin n) E) (x z : Fin n → E) (c : E) :
    hf L H x (c • z) = L.cj c * hf L H x z := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k), (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j))⁻¹ * (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j)) = 1 := by
  intro F E _ _ _ _ _ sig A r k G
  classical
  set g : Fin (r + 1) ⊕ Fin (r + 1) → Fin (k + 2 * r + 1) → E := Sum.elim G.f G.f' with hg
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  let p : HeightOneSpectrum (𝓞 F) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩
  obtain ⟨hinj, -, -, -, hform, hind⟩ := GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  obtain ⟨hli, hco, -⟩ := GlobalTheory.FrameBasic.main (A.L p) r k (G.S p)
  set S := G.S p with hS
  set Ep := (A.loc p).Ep
  let s : Fin (r + 1) ⊕ Fin (r + 1) → Epˣ := fun q =>
    Units.map (algebraMap (A.loc p).Fp Ep).toMonoidHom (G.c p ^ (r - (Sum.elim (fun a : Fin (r + 1) => (a : ℕ)) (fun a => (a : ℕ)) q)))
  have hu : ∀ q, A.bc p (g q) = ((s q : Epˣ) : Ep) • Sum.elim S.f S.f' q := by
    intro q
    rcases q with a | a
    · simp only [hg, Sum.elim_inl, s, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
      exact (G.f_eq p a).symm
    · simp only [hg, Sum.elim_inr, s, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
      exact (G.f'_eq p a).symm
  have hgli : LinearIndependent E g := by
    let e := (finSumFinEquiv (m := r + 1) (n := r + 1))
    refine (linearIndependent_equiv e.symm).1 ((hind _ (g ∘ e.symm)).2 ?_)
    have : (fun q => A.bc p (g q)) = s • Sum.elim S.f S.f' := by
      funext q; rw [hu]; rfl
    have h2 : LinearIndependent Ep (fun q => A.bc p (g q)) := by
      rw [this]; exact hli.units_smul s
    exact (linearIndependent_equiv e.symm).2 h2
  have hME : S.ME = Submodule.span Ep (Set.range (Sum.elim S.f S.f')) := by
    have h1 : ∀ v : Fin (r + 1) → S.V, S.spanTo v (r + 1) = Submodule.span Ep (Set.range v) := by
      intro v
      unfold Frames.spanTo
      congr 1
      ext y
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
      exact ⟨fun ⟨a, _, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨a, a.isLt, h⟩⟩
    rw [Frames.ME, h1, h1, Set.Sum.elim_range, Submodule.span_union]
  set Γ : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
    Matrix.of fun k l => ∑ i, ∑ j, g k i * G.Hm i j * sig (g l j) with hΓ
  have key : ∀ v : Fin (r + 1) ⊕ Fin (r + 1) → E, Matrix.vecMul v Γ = 0 → v = 0 := by
    intro v hv
    set x : Fin (k + 2 * r + 1) → E := ∑ q, v q • g q with hx
    have hx0 : ∀ l, ∑ i, ∑ j, x i * G.Hm i j * sig (g l j) = 0 := by
      intro l
      have h : Matrix.vecMul v Γ l = 0 := congrFun hv l
      rw [← h]
      simp only [Matrix.vecMul, dotProduct, hΓ, Matrix.of_apply, hx, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Finset.sum_mul, Finset.mul_sum, Pi.zero_apply]
      symm
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => by ring
    have hloc : ∀ q, hf (A.L p) S.Hm (A.bc p x) (A.bc p (g q)) = 0 := by
      intro q
      rw [G.Hm_eq p, hform, hx0, map_zero]
    have hbcx : A.bc p x = ∑ q, (A.loc p).ιE (v q) • A.bc p (g q) := by
      funext i
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Places.bc, hx, Finset.sum_apply, map_sum]
    have hmem : A.bc p x ∈ S.ME := by
      rw [hbcx, hME]
      refine Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ ?_
      rw [hu]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
    have hperp : A.bc p x ∈ S.W0 := by
      show ∀ y ∈ S.ME, hf (A.L p) S.Hm (A.bc p x) y = 0
      intro y hy
      rw [hME] at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨q, rfl⟩ := hy
        have e1 : Sum.elim S.f S.f' q = ((s q)⁻¹ : Epˣ) • A.bc p (g q) := by
          rw [hu, ← Units.smul_def, inv_smul_smul]
        rw [e1, Units.smul_def, hf_smul_right, hloc q, mul_zero]
      | zero => simp [hf]
      | add y z _ _ hy hz => rw [hf_add_right, hy, hz, add_zero]
      | smul c y _ hy => rw [hf_smul_right, hy, mul_zero]
    have hbot : A.bc p x = 0 := by
      have h : A.bc p x ∈ S.ME ⊓ S.W0 := ⟨hmem, hperp⟩
      rw [hco.inf_eq_bot] at h
      exact (Submodule.mem_bot _).1 h
    have hx00 : x = 0 := hinj (by rw [hbot]; funext i; simp [Places.bc])
    funext q
    exact Fintype.linearIndependent_iff.1 hgli v (by rw [← hx]; exact hx00) q
  have hU : IsUnit Γ := Matrix.vecMul_injective_iff_isUnit.1 fun a b h =>
    sub_eq_zero.1 (key _ (by rw [Matrix.sub_vecMul]; exact sub_eq_zero.2 h))
  exact Matrix.nonsing_inv_mul Γ ((Matrix.isUnit_iff_isUnit_det Γ).1 hU)

end GlobalTheory.HL.GamInv
end

