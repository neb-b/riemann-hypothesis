module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0015
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.FockRAddRight

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.FtFockZeroLeft
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory MvPolynomial

theorem ft_fock_zero_left {K : Type} [CommSemiring K] {σ : Type} (G : MvPolynomial σ K) :
    fock (0 : MvPolynomial σ K) G = 0 := by
  simp [fock]

theorem fock_add_left {K : Type} [Field K] {σ : Type} (F F' G : MvPolynomial σ K) :
    fock (F + F') G = fock F G + fock F' G := by
  classical
  have key : ∀ (H : MvPolynomial σ K) (s : Finset (σ →₀ ℕ)), H.support ⊆ s →
      fock H G = ∑ m ∈ s, H.coeff m * G.coeff m * (expFact m : K) := by
    intro H s hs
    unfold fock
    refine Finset.sum_subset hs fun m _ hm => ?_
    rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul, zero_mul]
  have hsub : (F + F').support ⊆ F.support ∪ F'.support := MvPolynomial.support_add
  rw [key _ _ hsub, key F (F.support ∪ F'.support) Finset.subset_union_left,
    key F' (F.support ∪ F'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem prod_add_mul {O ι : Type} [CommRing O] (s : Finset ι) (a x : ι → O) (t : O) :
    ∃ Y : O, ∏ i ∈ s, (a i + t * x i) = ∏ i ∈ s, a i + t * Y := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert j s hj ih =>
    obtain ⟨Y, hY⟩ := ih
    refine ⟨x j * ∏ i ∈ s, a i + a j * Y + t * x j * Y, ?_⟩
    rw [Finset.prod_insert hj, Finset.prod_insert hj, hY]
    ring

theorem segForm_single {O : Type} [CommRing O] [IsDomain O] (p r : ℕ) {s : ℕ} (S : SegData s)
    (u u' : SegVs O r s S.t) (b0 : SegBlock s r) (h : ∀ b, b ≠ b0 → u b = 0) :
    segForm O p r S u u' = ((specConst p S b0 : ℕ) : KK O) * fock (u b0) (u' b0) := by
  unfold segForm
  rw [finsum_eq_single _ b0]
  intro b hb
  rw [h b hb, ft_fock_zero_left, mul_zero]

theorem vLEO_mono {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} {x : O} {D D' : ℝ}
    (h : vLEO p x D) (hD : D ≤ D') : vLEO p x D' := by
  obtain ⟨q, hq, hqD⟩ := h
  exact ⟨q, hq, hqD.trans hD⟩

theorem vLEO_one {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} {w : O} (hw : Irreducible w)
    (h2 : w ^ 2 = (p : O)) {D : ℝ} (hD : 0 ≤ D) : vLEO p (1 : O) D := by
  refine ⟨0, ?_, by simpa using hD⟩
  unfold vO vK ordW
  rw [map_one, if_neg one_ne_zero]
  have hspec := Classical.choose_spec (IsLocalization.surj (nonZeroDivisors O) (1 : KK O))
  rw [one_mul] at hspec
  have heq : ((Classical.choose (IsLocalization.surj (nonZeroDivisors O) (1 : KK O))).2 : O) =
      (Classical.choose (IsLocalization.surj (nonZeroDivisors O) (1 : KK O))).1 :=
    IsFractionRing.injective O (KK O) hspec
  dsimp only
  rw [heq, sub_self]
  simp

theorem famOK_mem {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {C0 CE1 CE2 Cm : ℝ} {X : Loc}
    [NeZero X.m] {β : GlobalTheory X} {u : Vecs O C0 CE1 CE2 X} (hβ : KeptAll C0 CE1 CE2 X β) (hu : FamOK O C0 CE1 CE2 Cm X β u)
    (j : Fin (numSeg X.TT)) :
    u j (β j) ∈ blockLat O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 Cm) (β j) := by
  have h := (Submodule.mem_pi.1 (hu j).1) (β j) (Set.mem_univ _)
  rwa [if_pos (hβ j)] at h

theorem formAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ}
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X)
    (hB : BlockFormAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc) (h1 : OrthAt C0 CE1 CE2) (h2 : ProdAt C0 CE1 CE2)
    (h3 : SymPolAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) (h4 : IntAt) (h5 : NumAt C0 Cde CE1 CE2) (h6 : ZProdAt) :
    FormAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc := by
  classical
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hc hc1
  have hD1 : D1num X := ⟨hS.1.prime, hS.1.five_le, hS.1.two_le, hS.1.even⟩
  have St := hstd X hD1 hH hc
  have hw : Irreducible w := hS.2.1
  have hw2 : w ^ 2 = (X.p : O) := hS.1.w_sq
  have hBX := hB X W Qq O Kf ι σ jO w hS hH hc hc1
  have hex : ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      ∃ (κ : O) (s s' : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O) →
          MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O)),
        κ ≠ 0 ∧ vLEO X.p κ (((X.m + 2) * lgSeg X j : ℕ) : ℝ) ∧
        (Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
        (∀ u ∈ blockLat O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 Cm) b,
          s u ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 13) b).SSZ O
            (r := X.m) ∧
          s' u ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 13) b).SSZ O
            (r := X.m)) ∧
        ∀ u ∈ blockLat O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 Cm) b,
        ∀ u' ∈ blockLat O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 Cm) b,
        ∀ a : O, ((specConst X.p (X.seg C0 CE1 CE2 j) b : ℕ) : KK O) * fock u u' = algebraMap O (KK O) a →
          ∃ x : O, zSeg (KK O) X j * fock (ioBlock (KK O) X.p C0 CE1 CE2 X j b (s u))
              (ioBlock (KK O) X.p C0 CE1 CE2 X j b (s' u')) = algebraMap O (KK O) (κ * (a + w ^ X.c * x))) := by
    intro j b
    by_cases hk : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b
    · obtain ⟨κ, s, s', a1, a2, a3, a4⟩ := hBX j b hk
      exact ⟨κ, s, s', a1, a2, fun _ => ⟨a3, a4⟩⟩
    · exact ⟨1, id, id, one_ne_zero, vLEO_one hw hw2 (Nat.cast_nonneg _), fun h => absurd h hk⟩
  choose κb sb sb' hκ0 hκv hK using hex
  refine ⟨fun β => ∏ j, κb j (β j), fun β u j => sb j (β j) (u j (β j)), fun β u j => sb' j (β j) (u j (β j)),
    ?_, ?_, ?_⟩
  · intro β
    have hp := vLEO_prod hw hw2 Finset.univ (fun j => κb j (β j)) (fun j => (((X.m + 2) * lgSeg X j : ℕ) : ℝ))
      fun j _ => ⟨hκ0 j (β j), hκv j (β j)⟩
    exact ⟨hp.1, vLEO_mono hp.2 (h5 X St)⟩
  · intro β u hβ hu
    exact ⟨fun j => ((hK j (β j) (hβ j)).1 _ (famOK_mem hβ hu j)).1,
      fun j => ((hK j (β j) (hβ j)).1 _ (famOK_mem hβ hu j)).2⟩
  · intro β u β' u' hβ hβ' hu hu' a ha P hP Q hQ hPc hQc
    have hs1 : InSSZ O C0 CE1 CE2 (X.m0 13) X β (fun j => sb j (β j) (u j (β j))) :=
      fun j => ((hK j (β j) (hβ j)).1 _ (famOK_mem hβ hu j)).1
    have hs2 : InSSZ O C0 CE1 CE2 (X.m0 13) X β' (fun j => sb' j (β' j) (u' j (β' j))) :=
      fun j => ((hK j (β' j) (hβ' j)).1 _ (famOK_mem hβ' hu' j)).2
    set σ₁ := symFam (KK O) X.p C0 CE1 CE2 X β (fun j => sb j (β j) (u j (β j))) with hσ₁
    set σ₂ := symFam (KK O) X.p C0 CE1 CE2 X β' (fun j => sb' j (β' j) (u' j (β' j))) with hσ₂
    have hσ1P := h3 X O hD1 hH hc _ β hβ _ hs1
    have hσ2P := h3 X O hD1 hH hc _ β' hβ' _ hs2
    have hσ1I : InA (O := O) σ₁ := symIntAt C0 CE1 CE2 X O _ β _ hs1
    have hσ2I : InA (O := O) σ₂ := symIntAt C0 CE1 CE2 X O _ β' _ hs2
    have hPI : InA (O := O) P := by
      intro mm
      obtain ⟨c1, e1⟩ := hσ1I mm
      obtain ⟨c2, e2⟩ := hPc mm
      refine ⟨c1 + w ^ X.c * c2, ?_⟩
      rw [map_add (f := _), ← e1, ← e2, coeff_sub]
      ring
    obtain ⟨y1, hy1⟩ := h4 X.p O hS.1.prime (dvrOfStd hS) w X.n' X.m X.TT X.aT X.bT (P - σ₁)
      (Submodule.sub_mem _ hP hσ1P) σ₂ X.c hPc hσ2I
    obtain ⟨y2, hy2⟩ := h4 X.p O hS.1.prime (dvrOfStd hS) w X.n' X.m X.TT X.aT X.bT (Q - σ₂)
      (Submodule.sub_mem _ hQ hσ2P) P X.c hQc hPI
    have hdec : fock P Q = fock σ₁ σ₂ + fock (P - σ₁) σ₂ + fock (Q - σ₂) P := by
      have e1 : fock P Q = fock P σ₂ + fock P (Q - σ₂) := by
        rw [← fock_form_add_right]
        congr 1
        ring
      have e2 : fock P σ₂ = fock σ₁ σ₂ + fock (P - σ₁) σ₂ := by
        rw [← fock_add_left]
        congr 1
        ring
      rw [e1, e2, fock_form_symm P (Q - σ₂)]
    have hmain : ∃ ν0 : O, zTen (KK O) X.p X.m X.TT X.aT X.bT * fock σ₁ σ₂ =
        algebraMap O (KK O) ((if β = β' then (∏ j, κb j (β j)) * ∏ j, a j else 0) + w ^ X.c * ν0) := by
      rw [hσ₁, hσ₂, h2 X (KK O) St.seg2 β β' _ _, h6 X (KK O) St.seg2, ← Finset.prod_mul_distrib]
      by_cases hββ : β = β'
      · subst hββ
        have hx : ∀ j, ∃ x : O, zSeg (KK O) X j * fock (ioBlock (KK O) X.p C0 CE1 CE2 X j (β j) (sb j (β j) (u j (β j))))
            (ioBlock (KK O) X.p C0 CE1 CE2 X j (β j) (sb' j (β j) (u' j (β j)))) =
            algebraMap O (KK O) (κb j (β j) * (a j + w ^ X.c * x)) := fun j =>
          (hK j (β j) (hβ j)).2 _ (famOK_mem hβ hu j) _ (famOK_mem hβ hu' j) (a j) (by
            rw [← ha j, segForm_single X.p X.m (X.seg C0 CE1 CE2 j) (u j) (u' j) (β j) (hu j).2])
        choose x hx using hx
        obtain ⟨Y, hY⟩ := prod_add_mul Finset.univ a x (w ^ X.c)
        refine ⟨(∏ j, κb j (β j)) * Y, ?_⟩
        rw [Finset.prod_congr rfl (fun j _ => hx j), ← map_prod, Finset.prod_mul_distrib, hY, if_pos rfl]
        congr 1
        ring
      · obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hββ
        refine ⟨0, ?_⟩
        rw [Finset.prod_eq_zero (Finset.mem_univ j0) (by
          rw [h1 X O _ hD1 j0 _ _ (hβ j0) (hβ' j0) hj0 _ (hs1 j0) _ (hs2 j0), mul_zero]), if_neg hββ]
        simp
    obtain ⟨ν0, h0⟩ := hmain
    refine ⟨ν0 + y1 + y2, ?_⟩
    rw [hdec, mul_add, mul_add, h0, hy1, hy2, ← map_add (f := _), ← map_add (f := _)]
    congr 1
    ring

def RestSymPol : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => SymPolAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem restForm_of' (hB : RestBlockForm) (h1 : ∀ C0 CE1 CE2, OrthAt C0 CE1 CE2) (h2 : ∀ C0 CE1 CE2, ProdAt C0 CE1 CE2)
    (h3 : RestSymPol) (h4 : IntAt) (h5 : ∀ C0 Cde CE1 CE2, NumAt C0 Cde CE1 CE2) (h6 : ZProdAt) : RestForm := by
  intro Cc hCc
  obtain ⟨A0, hA0, hA⟩ := thr_std Cc hCc
  obtain ⟨B0, hB0, hBB⟩ := hB Cc hCc
  obtain ⟨S0, hS0, hS⟩ := h3 Cc hCc
  refine ⟨max A0 (max B0 S0), lt_max_of_lt_left hA0, fun C0 hC0 => ?_⟩
  obtain ⟨A1, hA1, hA'⟩ := hA C0 ((le_max_left _ _).trans hC0)
  obtain ⟨B1, hB1, hBB'⟩ := hBB C0 (((le_max_left _ _).trans (le_max_right _ _)).trans hC0)
  obtain ⟨S1, hS1, hS'⟩ := hS C0 (((le_max_right _ _).trans (le_max_right _ _)).trans hC0)
  refine ⟨max A1 (max B1 S1), lt_max_of_lt_left hA1, fun CE1 CE2 Cm hE1 hE2 hm => ?_⟩
  have l1 : A1 ≤ max A1 (max B1 S1) := le_max_left _ _
  have l2 : B1 ≤ max A1 (max B1 S1) := (le_max_left _ _).trans (le_max_right _ _)
  have l3 : S1 ≤ max A1 (max B1 S1) := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨A2, hA2, hA''⟩ := hA' CE1 CE2 Cm (l1.trans hE1) (l1.trans hE2) (l1.trans hm)
  obtain ⟨B2, hB2, hBB''⟩ := hBB' CE1 CE2 Cm (l2.trans hE1) (l2.trans hE2) (l2.trans hm)
  obtain ⟨S2, hS2, hS''⟩ := hS' CE1 CE2 Cm (l3.trans hE1) (l3.trans hE2) (l3.trans hm)
  refine ⟨max A2 (max B2 S2), lt_max_of_lt_left hA2, fun CYb Cde Ck CD Cb h₁ h₂ h₃ h₄ h₅ => ?_⟩
  have m1 : A2 ≤ max A2 (max B2 S2) := le_max_left _ _
  have m2 : B2 ≤ max A2 (max B2 S2) := (le_max_left _ _).trans (le_max_right _ _)
  have m3 : S2 ≤ max A2 (max B2 S2) := (le_max_right _ _).trans (le_max_right _ _)
  have hstd := (hA'' CYb Cde Ck CD Cb (m1.trans h₁) (m1.trans h₂) (m1.trans h₃) (m1.trans h₄) (m1.trans h₅)).2
  have hblk := hBB'' CYb Cde Ck CD Cb (m2.trans h₁) (m2.trans h₂) (m2.trans h₃) (m2.trans h₄) (m2.trans h₅)
  have hsym := hS'' CYb Cde Ck CD Cb (m3.trans h₁) (m3.trans h₂) (m3.trans h₃) (m3.trans h₄) (m3.trans h₅)
  exact formAt_of hstd hblk (h1 C0 CE1 CE2) (h2 C0 CE1 CE2) hsym h4 (h5 C0 Cde CE1 CE2) h6

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.LaTwInvT
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.ColumnSystems.Pf.TF

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det H0_eq_twisted_nabla la_indep)
open Formalism.L2.G.Model (Lin Th0 Aa Lin_comp Lin_one Lin_Pol Lin_smul Th0_inj mem_tens_nabla mem_tens_dw map_Pol mem_Pol VS
  letterWt_anti tensor_lattice_twist_eq edgeLat_of la_tw_mul la_tw_transpose la_tw_inv dE invT_mul_D dual_edgeBasis w_ne p_eq
  pQ_ne kapR kapR_alg lift_eq Bm Bm_eq Mx Mx_det Avec pol_iff thF)
open Formalism.L2.G.Model.TS

section

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ} {TT : Finset (Fin n')} {aT bT : Fin n' → ℕ}

abbrev vecH (TT : Finset (Fin n')) : TT × Bool → Bool := fun x => x.2

theorem HHL_iff (hS : HidaSetting p n' W Qq O Kf ι σ j w) (ℓ : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hℓ : IsUnit ℓ.det)
    (u : ↥(VHH (m := m) Kf TT aT bT)) :
    u ∈ HHL (O := O) ι σ TT aT bT (colSpan W ℓ) ↔
      (u : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
        LatM O (vecH TT) (hhDegs TT aT bT) (fun x => la_tw ι σ x.1.val.val ℓ) := by
  have e := tensor_lattice_twist_eq hS m (vecH TT) (hhDegs TT aT bT) (fun x => x.1.val) ℓ hℓ
  unfold LatM
  rw [← e]
  rfl

theorem HHLe_iff (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ) (e : Edge W Qq (m + 1))
    (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hb : IsEdgeBasis p r e b) (u : ↥(VHH (m := m) Kf TT aT bT)) :
    u ∈ HHLe p ι σ w TT aT bT e ↔
      (u : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
        LatM O (vecH TT) (hhDegs TT aT bT) (fun x => la_tw ι σ x.1.val.val b * lb_D (m + 1) r (algebraMap O Kf w)) := by
  have := hS.frac_O
  have e1 : (fun x : TT × Bool => H0 O m (letterWt m (hhDegs TT aT bT x) (vecH TT x)) (LeAt p ι σ w x.1.val.val e)) =
      fun x => nablaLTw O Kf m (letterWt m (hhDegs TT aT bT x) (vecH TT x))
        (la_tw ι σ x.1.val.val b * lb_D (m + 1) r (algebraMap O Kf w)) := by
    funext x
    rw [(edgeLat_of hS m r e b hb).2.1, H0_eq_twisted_nabla (la_indep (IsFractionRing.injective O Kf)) _ _ (letterWt_anti _ _ _) _
      (by rw [Matrix.det_mul]; exact (la_tw_det _ _ _ _ hb.1).mul (lb_D_det _ _ _ (w_ne hS)))]
  unfold LatM
  rw [← e1]
  rfl

theorem la_tw_invT (s : ℕ) (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hb : IsUnit b.det) :
    la_tw ι σ s ((b⁻¹).transpose) = ((la_tw ι σ s b)⁻¹).transpose := by
  rw [la_tw_transpose, la_tw_inv _ _ hb]

theorem la_tw_dE (s r : ℕ) : la_tw ι σ s (dE (m + 1) r ((p : ℕ) : Qq)) = dE (m + 1) r ((p : ℕ) : Kf) := by
  ext a c
  simp only [la_tw, dE, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem dualM (hS : HidaSetting p n' W Qq O Kf ι σ j w) (s r : ℕ) (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (hb : IsUnit b.det) :
    la_tw ι σ s ((b⁻¹).transpose * dE (m + 1) r ((p : ℕ) : Qq)) * lb_D (m + 1) r (algebraMap O Kf w) =
      ((la_tw ι σ s b * lb_D (m + 1) r (algebraMap O Kf w))⁻¹).transpose := by
  have hω := w_ne hS
  have hp : ((p : ℕ) : Kf) = (algebraMap O Kf w) ^ 2 := by rw [← map_pow, hS.w_sq, map_natCast]
  rw [la_tw_mul, la_tw_invT s b hb, la_tw_dE, Matrix.mul_inv_rev, Matrix.transpose_mul, mul_assoc]
  congr 1
  simp only [dE, lb_D, Matrix.diagonal_mul_diagonal, Matrix.inv_diagonal, Matrix.diagonal_transpose]
  congr 1
  funext a
  have hu : IsUnit (fun a : Fin (m + 1) => if a.val < r then (algebraMap O Kf w)⁻¹ else (1 : Kf)) := by
    rw [Pi.isUnit_iff]
    intro a
    split_ifs
    · exact isUnit_iff_ne_zero.mpr (inv_ne_zero hω)
    · exact isUnit_one
  have hinv := congrFun (Ring.inverse_mul_cancel _ hu) a
  rw [Pi.mul_apply, Pi.one_apply] at hinv
  rw [eq_inv_of_mul_eq_one_left hinv]
  split_ifs with h
  · rw [inv_inv, hp]; field_simp
  · simp

variable (thK : ↥(Pol Kf (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)) ≃ₗ[Kf] ↥(VHH (m := m) Kf TT aT bT))

def XiH (c : Kf) : ↥(VHH (m := m) Kf TT aT bT) →ₗ[Kf] Module.Dual Kf ↥(VHH (m := m) Kf TT aT bT) :=
  TY (vec := vecH TT) (d := hhDegs TT aT bT) thK c

theorem XiH_apply (c : Kf) (P Q : ↥(Pol Kf (ι := TT × Bool) (m + 1) (hhDegs TT aT bT))) :
    XiH thK c (thK Q) (thK P) = c * fockR (P : MvPolynomial ((TT × Bool) × Fin (m + 1)) Kf)
      (Q : MvPolynomial ((TT × Bool) × Fin (m + 1)) Kf) :=
  TY_apply (vec := vecH TT) (d := hhDegs TT aT bT) thK c P Q

abbrev zK (Kf : Type) [Field Kf] (p κ : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) : Kf :=
  (p : Kf) ^ κ / (((∏ x : TT × Bool, (hhDegs TT aT bT x).factorial : ℕ) : ℕ) : Kf)

theorem FD_edge (hS : HidaSetting p n' W Qq O Kf ι σ j w) (hm : 1 ≤ m)
    (hthK : ∀ P, ((thK P : ↥(VHH (m := m) Kf TT aT bT)) : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m (vecH TT) (P : MvPolynomial ((TT × Bool) × Fin (m + 1)) Kf))
    (κ : ℕ) (hMD : MultDiv O p κ (k := m + 1) (hhDegs TT aT bT)) (r : ℕ) (e : Edge W Qq (m + 1))
    (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hb : IsEdgeBasis p r e b) (c : Kf)
    (y : ↥(VHH (m := m) Kf TT aT bT))
    (hy : y ∈ scale c (ReHH p ι σ w TT aT bT e.dual)) :
    XiH thK (zK Kf p κ TT aT bT) y ∈ scale c (ReHH' p ι σ w TT aT bT e) := by
  obtain ⟨y1, hy1, rfl⟩ := mem_scale.1 hy
  obtain ⟨y0, hy0, rfl⟩ := mem_scale.1 hy1
  refine mem_scale.2 ⟨_, mem_scale.2 ⟨XiH thK (zK Kf p κ TT aT bT) y0, ?_, rfl⟩, ?_⟩
  · intro u hu
    refine sandwich (vec := vecH TT) (d := hhDegs TT aT bT) thK hm hthK p κ hMD
      (fun x => la_tw ι σ x.1.val.val b * lb_D (m + 1) r (algebraMap O Kf w))
      (fun x => by rw [Matrix.det_mul]; exact (la_tw_det _ _ _ _ hb.1).mul (lb_D_det _ _ _ (w_ne hS))) u y0
      ((HHLe_iff hS r e b hb u).1 hu) ?_
    have h1 := (HHLe_iff hS r e.dual _ (dual_edgeBasis p r (pQ_ne hS) e b hb) y0).1 hy0
    have e1 : (fun x : TT × Bool => la_tw ι σ x.1.val.val ((b⁻¹).transpose * dE (m + 1) r ((p : ℕ) : Qq)) *
        lb_D (m + 1) r (algebraMap O Kf w)) =
        fun x => ((la_tw ι σ x.1.val.val b * lb_D (m + 1) r (algebraMap O Kf w))⁻¹).transpose :=
      funext fun x => dualM hS x.1.val.val r b hb.1
    rw [e1] at h1
    exact h1
  · rw [map_smul, map_smul]

theorem FD_HL (hS : HidaSetting p n' W Qq O Kf ι σ j w) (hm : 1 ≤ m)
    (hthK : ∀ P, ((thK P : ↥(VHH (m := m) Kf TT aT bT)) : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m (vecH TT) (P : MvPolynomial ((TT × Bool) × Fin (m + 1)) Kf))
    (κ : ℕ) (hMD : MultDiv O p κ (k := m + 1) (hhDegs TT aT bT))
    (ℓ : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hℓ : IsUnit ℓ.det) (c : Kf)
    (y : ↥(VHH (m := m) Kf TT aT bT))
    (hy : y ∈ scale c (HHL (O := O) ι σ TT aT bT (colSpan W ((ℓ⁻¹).transpose)))) :
    XiH thK (zK Kf p κ TT aT bT) y ∈ scale c (dualLat O Kf (HHL (O := O) ι σ TT aT bT (colSpan W ℓ))) := by
  obtain ⟨y0, hy0, rfl⟩ := mem_scale.1 hy
  refine mem_scale.2 ⟨XiH thK (zK Kf p κ TT aT bT) y0, ?_, by rw [map_smul]⟩
  intro u hu
  refine sandwich (vec := vecH TT) (d := hhDegs TT aT bT) thK hm hthK p κ hMD (fun x => la_tw ι σ x.1.val.val ℓ)
    (fun x => la_tw_det _ _ _ _ hℓ) u y0 ((HHL_iff hS ℓ hℓ u).1 hu) ?_
  have hℓt : IsUnit ((ℓ⁻¹).transpose).det := Formalism.L2.G.Model.det_invT ℓ hℓ
  have h1 := (HHL_iff hS _ hℓt y0).1 hy0
  have e1 : (fun x : TT × Bool => la_tw ι σ x.1.val.val ((ℓ⁻¹).transpose)) =
      fun x => ((la_tw ι σ x.1.val.val ℓ)⁻¹).transpose :=
    funext fun x => la_tw_invT x.1.val.val ℓ hℓ
  rw [e1] at h1
  exact h1

end

end Formalism.MainNotions.ColumnSystems.Pf.TF
end
end

