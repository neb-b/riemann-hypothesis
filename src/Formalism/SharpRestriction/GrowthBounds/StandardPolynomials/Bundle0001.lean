module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColGen

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.LatticeLeSpanPsiImage
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.PolBridge

section Span

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N r : ℕ} [NeZero r]

theorem lattice_le_span_psi_image {D : Formalism.BasicNotions.D7} (hA2 : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) {p : ℕ} [Fact p.Prime]
    (S : UniformizedDVR p O) (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (hJ : ∀ k, J k ≤ N) :
    YjtZ O (r := r) LL J M ≤ Submodule.span O (psiR (KK O) LL '' sAll LL J M) := by
  have hp : p.Prime := Fact.out
  have hKz : CharZero (KK O) := dvr_fraction_field_charZero S hp
  have hinj : Function.Injective (algebraMap O (KK O)) := IsFractionRing.injective O (KK O)
  obtain ⟨hli, hspan⟩ := hA2 O N r (⟨LL.vec⟩ : Letters (Fin N)) LL.deg
  have hli' : LinearIndependent O (psiR (r := r) O LL) := hli
  have hrange : Submodule.span O (Set.range (psiR (r := r) O LL)) = Pol O r LL.deg := by
    rw [← hspan]
    congr 1
    ext G
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x.1.1, x.1.2, x.2, rfl⟩
    · rintro ⟨P, I, h, rfl⟩; exact ⟨⟨(P, I), h⟩, rfl⟩
  have hfin : Finite (Tx r LL) := tx_finite LL hli' hrange
  obtain ⟨Bd, hBd⟩ := exists_bound (r := r) (Lt := (⟨LL.vec⟩ : Letters (Fin N))) (B := LL.deg)
  have hC1 := one_cond D LL hrange hspan (fun th M => (hA3 p O S N r _ LL.deg th M).1) Bd hBd J M hJ
  intro F hF
  obtain ⟨hY, G, hG⟩ := hF
  let φ : MvPolynomial (Fin N × Fin r) O →ₗ[O] MvPolynomial (Fin N × Fin r) (KK O) :=
    (MvPolynomial.mapAlgHom (Algebra.ofId O (KK O))).toLinearMap
  have hG' : MvPolynomial.map (algebraMap O (KK O)) G = F := hG
  have hY' : MvPolynomial.map (algebraMap O (KK O)) G ∈ Yjt (KK O) (r := r) LL J M := by rw [hG']; exact hY
  rw [Yjt, Submodule.mem_inf, Submodule.mem_iInf] at hY'
  have hGP : G ∈ Pol O r LL.deg := (map_mem_Pol_iff _ hinj _ G).1 hY'.1
  have hGs : G ∈ Submodule.span O (psiR O LL '' sAll LL J M) :=
    mem_span_iInter hli' (sK LL J M) (hrange ▸ hGP) (fun k => (hC1 k G hGP).1 (hY'.2 k))
  have h1 : F ∈ Submodule.map φ (Submodule.span O (psiR O LL '' sAll LL J M)) := ⟨G, hGs, hG⟩
  rw [Submodule.map_span, ← Set.image_comp] at h1
  have h2 : (φ ∘ psiR (r := r) O LL) = psiR (KK O) LL := funext fun x => psiR_map LL x
  rwa [h2] at h1

end Span

section Xi

variable {O : Type} [CommRing O] [IsDomain O]

theorem xiVar_inj (N r t : ℕ) : Function.Injective (xiVar N r t) := by
  intro c d h
  simpa [xiVar] using h

theorem xiSpan (N r t b : ℕ) :
    XiPolZ O N r t b ≤ Submodule.span O
      {g : MvPolynomial (BVar N r t) (KK O) | ∃ γ : Fin r → ℕ, ∑ c, γ c = b ∧ g = ∏ c, X (xiVar N r t c) ^ γ c} := by
  intro f hf
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hf
  obtain ⟨g, rfl⟩ := LinearMap.mem_range.1 h2
  have hinj : Function.Injective (algebraMap O (KK O)) := IsFractionRing.injective O (KK O)
  have hmap : ∀ p : MvPolynomial (BVar N r t) O,
      (MvPolynomial.mapAlgHom (Algebra.ofId O (KK O)) : MvPolynomial (BVar N r t) O →ₐ[O] _).toLinearMap p =
        MvPolynomial.map (algebraMap O (KK O)) p := fun p => rfl
  have hsup : ∀ m ∈ g.support, (∀ v ∈ m.support, ∃ c, v = xiVar N r t c) ∧ ∑ c, m (xiVar N r t c) = b := by
    intro m hm
    have hm' : m ∈ (MvPolynomial.map (algebraMap O (KK O)) g).support := by
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map]
      exact (map_ne_zero_iff _ hinj).2 (MvPolynomial.mem_support_iff.1 hm)
    rw [hmap] at h1
    exact ((MvPolynomial.mem_restrictSupport_iff (KK O)).1 h1) (Finset.mem_coe.2 hm')
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hmap, MvPolynomial.as_sum g, map_sum]
  refine Submodule.sum_mem _ (fun m hm => ?_)
  obtain ⟨hv, hb⟩ := hsup m hm
  have hmon : m.prod (fun v e => (X v : MvPolynomial (BVar N r t) (KK O)) ^ e) =
      ∏ c, X (xiVar N r t c) ^ m (xiVar N r t c) := by
    rw [Finsupp.prod, ← Finset.prod_image (fun c _ c' _ h => xiVar_inj N r t h)
      (f := fun v => (X v : MvPolynomial (BVar N r t) (KK O)) ^ m v)]
    apply Finset.prod_subset
    · intro v hv'
      obtain ⟨c, rfl⟩ := hv v hv'
      exact Finset.mem_image_of_mem _ (Finset.mem_univ c)
    · intro v _ hv'
      have h0 : m v = 0 := by simpa using hv'
      rw [h0, pow_zero]
  have hprod1 : m.prod (fun v e => (X v : MvPolynomial (BVar N r t) (KK O)) ^ e) = MvPolynomial.monomial m 1 := by
    rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul]
  have hterm : MvPolynomial.map (algebraMap O (KK O)) (MvPolynomial.monomial m (g.coeff m)) =
      g.coeff m • ∏ c, X (xiVar N r t c) ^ m (xiVar N r t c) := by
    rw [← hmon, hprod1, MvPolynomial.smul_monomial, Algebra.smul_def, mul_one, MvPolynomial.map_monomial]
  rw [hterm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun c => m (xiVar N r t c), hb, rfl⟩)

end Xi

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N r : ℕ} [NeZero r]

theorem genSet_le {D : Formalism.BasicNotions.D7} (hA2 : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) {p : ℕ} [Fact p.Prime]
    (S : UniformizedDVR p O) (B : BlockData N) (hJ : ∀ k, B.T.J k ≤ N) :
    genSet O (r := r) B ⊆ Submodule.span O (colGens O (r := r) B) := by
  intro x hx
  simp only [genSet, Set.mem_iUnion] at hx
  obtain ⟨j, jp, hok, y, hy, g, hg, rfl⟩ := hx
  have key : ∀ y ∈ Submodule.span O (psiR (KK O) (B.lettersAt j jp) '' sAll (B.lettersAt j jp) B.T.J B.T.thr),
      ∀ g ∈ Submodule.span O {g : MvPolynomial (BVar N r B.T.t) (KK O) |
        ∃ γ : Fin r → ℕ, ∑ c, γ c = B.B - jp ∧ g = ∏ c, X (xiVar N r B.T.t c) ^ γ c},
      ((∏ i, B.Ehat O (r := r) i ^ j i) * B.Eplus O (r := r) ^ jp *
          (∏ i, X (scalZ N r B.T.t (Fin.castSucc i)) ^ B.T.z i) * X (scalZ N r B.T.t (Fin.last B.T.t)) ^ B.zPlus) * rename (chainEmb N r B.T.t) y * g ∈ Submodule.span O (colGens O (r := r) B) := by
    intro y hy g hg
    induction hy using Submodule.span_induction with
    | mem y0 hy0 =>
      induction hg using Submodule.span_induction with
      | mem g0 hg0 =>
        obtain ⟨yy, hyy, rfl⟩ := hy0
        obtain ⟨γ, hγ, rfl⟩ := hg0
        exact Submodule.subset_span ⟨j, jp, hok, yy, hyy, γ, hγ, rfl⟩
      | zero => simp
      | add g1 g2 _ _ h1 h2 =>
        rw [mul_add]
        exact Submodule.add_mem _ h1 h2
      | smul a g1 _ h1 =>
        rw [mul_smul_comm]
        exact Submodule.smul_mem _ a h1
    | zero => simp
    | add y1 y2 _ _ h1 h2 =>
      rw [map_add (f := _), mul_add, add_mul]
      exact Submodule.add_mem _ h1 h2
    | smul a y1 _ h1 =>
      rw [AlgHom.map_smul_of_tower, mul_smul_comm, smul_mul_assoc]
      exact Submodule.smul_mem _ a h1
  exact key y (lattice_le_span_psi_image (r := r) hA2 hA3 S (B.lettersAt j jp) B.T.J B.T.thr hJ hy) g
    (xiSpan (O := O) N r B.T.t (B.B - jp) hg)

theorem blockData_J_le (p : ℕ) {s r : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r)
    (k : Fin (blockData p S aTop aPlus m b).T.q) : (blockData p S aTop aPlus m b).T.J k ≤ 2 * s + 1 := by
  show (if h : (k : ℕ) < S.t then 2 * (uTop S ⟨k, h⟩ : ℕ) + 1 else 2 * s + 1) ≤ 2 * s + 1
  split_ifs with h
  · have := (uTop S ⟨k, h⟩).isLt
    omega
  · exact le_rfl

end Gen

theorem asmRTAt_of_facSys {D : Formalism.BasicNotions.D7} (hA2 : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D)
    {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hF : FacSysAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    AsmRTAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro _ _ X _ _ O _ _ _ _ S hSq hD1 hHI hCB mm hmm n hn1 hnc β hβ s hs
  have hmem : symFam (KK O) X.p C0 CE1 CE2 X β s ∈
      liftSub C0 Cde CE1 CE2 X O S.w mm n (ordFam C0 CE1 CE2 X β) :=
    symFam_span β (fun j => colGens O (r := X.m)
        (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j))) _
      (fun s' hs' => (hF X O S hSq hD1 hHI hCB mm hmm n hn1 hnc β hβ s' hs').some.liftable S.w_irr.ne_zero) s
      (fun j => genSet_le hA2 hA3 S _ (blockData_J_le _ _ _ _ _ _) (hs j))
  obtain ⟨raw, hc, τ, hτ, hw⟩ := hmem
  exact ⟨raw, τ, hc, hτ, hw⟩

theorem restAsmRT_of_facSys {D : Formalism.BasicNotions.D7} (hA : admitted D) (h : FacSysCondition) : RestAsmRT := by
  unfold admitted at hA
  obtain ⟨-, -, -, -, -, h6, -, -, -, -, -, -, -, -, h15, -⟩ := hA
  intro Cc hCc
  obtain ⟨T0, hT0, h1⟩ := h Cc hCc
  refine ⟨T0, hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, h2⟩ := h1 C0 hC0
  refine ⟨T1, hT1, fun CE1 CE2 Cm hE1 hE2 hm => ?_⟩
  obtain ⟨T2, hT2, h3⟩ := h2 CE1 CE2 Cm hE1 hE2 hm
  exact ⟨T2, hT2, fun CYb Cde Ck CD Cb a b c d e =>
    asmRTAt_of_facSys (D := D) h15 h6 (h3 CYb Cde Ck CD Cb a b c d e)⟩

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TCoreDef
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def ioA (K : Type) [CommRing K] (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) :
    MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) K →ₐ[K]
      MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
  aeval (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K) ^
      symLev p C0 CE1 CE2 X j v)

theorem ioBlock_eq (K : Type) [CommRing K] (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (u : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) K) :
    ioBlock K p C0 CE1 CE2 X j b u =
      digitMon K C0 CE1 CE2 X j b * sTopMon K p C0 CE1 CE2 X j b * ioA K p C0 CE1 CE2 X j u := rfl

abbrev BDk (C0 CE1 CE2 mu : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) : BlockData (2 * segS X.TT j + 1) :=
  blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mu (β j)

def ioD (O : Type) [CommRing O] [IsDomain O] (C0 CE1 CE2 mu : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) :
    MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) (KK O) →ₐ[KK O] RHH O X :=
  ioA (KK O) X.p C0 CE1 CE2 X j

structure LvDat (C0 CE1 CE2 mu : ℝ) (X : Loc) (β : GlobalTheory X) where
  lv : ∀ j, Fin (BDk C0 CE1 CE2 mu X β j).T.t → ℕ
  jp : Fin (numSeg X.TT) → ℕ
  ok : ∀ j, (BDk C0 CE1 CE2 mu X β j).LevelOK (lv j) (jp j)
  γ : Fin (numSeg X.TT) → Fin X.m → ℕ
  hγ : ∀ j, ∑ c, γ j c = (BDk C0 CE1 CE2 mu X β j).B - jp j

section

variable (O : Type) [CommRing O] [IsDomain O] {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X}

abbrev LvDat.LL (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT)) : ChainLetters (2 * segS X.TT j + 1) :=
  (BDk C0 CE1 CE2 mu X β j).lettersAt (L.lv j) (L.jp j)

def LvDat.stdPoly (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT)) : RHH O X :=
  digitMon (KK O) C0 CE1 CE2 X j (β j) * sTopMon (KK O) X.p C0 CE1 CE2 X j (β j) *
    ioD O C0 CE1 CE2 mu X β j
      ((∏ i, MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t (Fin.castSucc i)) ^
          (BDk C0 CE1 CE2 mu X β j).T.z i) *
        MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t
          (Fin.last (BDk C0 CE1 CE2 mu X β j).T.t)) ^ (BDk C0 CE1 CE2 mu X β j).zPlus *
        ∏ c, MvPolynomial.X (xiVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t c) ^ L.γ j c)

def LvDat.head (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT))
    (ju : Fin (BDk C0 CE1 CE2 mu X β j).T.t → ℕ) (G : MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) : RHH O X :=
  ioD O C0 CE1 CE2 mu X β j
    ((∏ i, (BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) i ^ ju i) * (BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m) ^ L.jp j *
      rename (chainEmb (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) G)

def LvDat.word (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT))
    (G : MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) :
    MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) (KK O) :=
  (∏ i, (BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) i ^ L.lv j i) * (BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m) ^ L.jp j *
      (∏ i, MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t (Fin.castSucc i)) ^
          (BDk C0 CE1 CE2 mu X β j).T.z i) *
      MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t
          (Fin.last (BDk C0 CE1 CE2 mu X β j).T.t)) ^ (BDk C0 CE1 CE2 mu X β j).zPlus *
      rename (chainEmb (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) G *
      ∏ c, MvPolynomial.X (xiVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t c) ^ L.γ j c

theorem LvDat.ioBlock_word (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT))
    (G : MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) :
    ioBlock (KK O) X.p C0 CE1 CE2 X j (β j) (L.word O j G) = L.head O j (L.lv j) G * L.stdPoly O j := by
  change digitMon (KK O) C0 CE1 CE2 X j (β j) * sTopMon (KK O) X.p C0 CE1 CE2 X j (β j) *
    ioA (KK O) X.p C0 CE1 CE2 X j (L.word O j G) = _
  simp only [LvDat.word, LvDat.head, LvDat.stdPoly, ioD]
  conv_rhs => rw [mul_comm, mul_assoc]
  erw [← map_mul]
  refine congrArg (fun w => digitMon (KK O) C0 CE1 CE2 X j (β j) * sTopMon (KK O) X.p C0 CE1 CE2 X j (β j) *
    ioA (KK O) X.p C0 CE1 CE2 X j w) ?_
  have hcomm : ∀ (e ep z zp r xi : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m
      (X.seg C0 CE1 CE2 j).t) (KK O)), e * ep * z * zp * r * xi = z * zp * xi * (e * ep * r) :=
    fun e ep z zp r xi => by ring
  exact hcomm _ _ _ _ _ _

end

def TCoreAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ n : ℕ, 1 ≤ n → n ≤ X.c →
    ∀ β : GlobalTheory X, (∀ j, BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j (β j)) →
    ∀ (L : LvDat C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β) (Std : MonH X),
      (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j →
    ∀ e : ℕ, 1 ≤ e → e < n →
    ∀ (ju : ∀ j, Fin (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.t → ℕ), (∀ j i, ju j i ≤ L.lv j i) →
    ∀ (Gu : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O))
      (du : ∀ j, Fin (2 * segS X.TT j + 1) → ℕ),
      (∀ j, Gu j ∈ IntPol O (Fin (2 * segS X.TT j + 1) × Fin X.m)) →
      (∀ j, Gu j ∈ Pol (KK O) X.m (du j)) → (∀ j a, du j a ≤ (L.LL j).deg a) →
      (∀ j k, Gu j ∈ YCond (KK O) (r := X.m) (L.LL j) ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.J k)
        ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr k + (((X.N1 * e : ℕ) : ℤ) : WithTop ℤ))) →
    ∀ A : MonH X,
      (∀ l, ∑ c, (Std (l, c) - A (l, c)) ≤ X.p ^ X.G' * e) → (∀ l, ∑ c, (A (l, c) - Std (l, c)) ≤ X.p ^ X.G' * e) →
      (∀ j c, A ((topEnd X j, false), c) = Std ((topEnd X j, false), c)) →
      (∏ j, L.head O j (ju j) (Gu j)) * monomial A 1 ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT) →
      (∀ m ∈ ((∏ j, L.head O j (ju j) (Gu j)) * monomial A 1).support, ndM X m ≤ ordFam C0 CE1 CE2 X β + e) →
      (∏ j, L.head O j (ju j) (Gu j)) * monomial A 1 ∈ SSe C0 Cde CE1 CE2 X O mm n (ordFam C0 CE1 CE2 X β) e

def RestTCore : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => TCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf
end
end

