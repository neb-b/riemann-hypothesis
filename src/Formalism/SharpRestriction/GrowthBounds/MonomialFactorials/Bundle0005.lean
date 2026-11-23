module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0003
public import Formalism.PolynomialDimension.MultinomialDepth.PartnerM

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestRankLProved
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset

section Gen

variable {p : ℕ} [Fact p.Prime]

theorem finrank_zp_le {V : Type} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]
    (M : Submodule ℤ_[p] V) (W : Submodule ℚ_[p] V) [FiniteDimensional ℚ_[p] W] (hMW : ∀ x ∈ M, x ∈ W) :
    Module.finrank ℤ_[p] M ≤ Module.finrank ℚ_[p] W := by
  have hr : Module.rank ℤ_[p] M ≤ (Module.finrank ℚ_[p] W : Cardinal) := by
    apply _root_.rank_le
    intro s hs
    have h1 : LinearIndependent ℤ_[p] (fun i : s => ((i : M) : V)) :=
      hs.map' M.subtype (Submodule.ker_subtype M)
    have h2 : LinearIndependent ℚ_[p] (fun i : s => ((i : M) : V)) :=
      (LinearIndependent.iff_fractionRing ℤ_[p] ℚ_[p]).mp h1
    have h3 : LinearIndependent ℚ_[p] (fun i : s => (⟨((i : M) : V), hMW _ (i : M).2⟩ : W)) := by
      refine LinearIndependent.of_comp W.subtype ?_
      exact h2
    have := h3.fintype_card_le_finrank
    simpa using this
  exact Module.finrank_le_of_rank_le hr

end Gen

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)


open Classical in
def xiMons (n : ℕ) : Finset (Formalism.GM.M.BVar N r G.T.t →₀ ℕ) :=
  (CountingStatementReduction.Ev r n).image (fun e => ∑ c : Fin r, Finsupp.single (Formalism.GM.M.xiVar N r G.T.t c) (e c))

theorem card_xiMons (n : ℕ) : (xiMons (r := r) G n).card ≤ dXi r n := by
  classical
  unfold xiMons
  refine (Finset.card_image_le).trans ?_
  rw [CountingStatementReduction.card_Ev]
  unfold dXi
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.2 (NeZero.ne r)
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have e1 : r' + 1 + n - 1 = n + r' := by omega
  have e2 : n + (r' + 1) - 1 = n + r' := by omega
  rw [e1, e2, Nat.add_sub_cancel, Nat.choose_symm_add]

theorem xiVar_inj : Function.Injective (Formalism.GM.M.xiVar N r G.T.t) := by
  intro c d h
  simp only [Formalism.GM.M.xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
  exact h.2

theorem xi_mem_span (n : ℕ) (g : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])
    (hg : g ∈ Formalism.GM.M.XiPolZ p N r G.T.t n) :
    g ∈ Submodule.span ℚ_[p] ((fun m => (monomial m (1 : ℚ_[p]))) '' (xiMons (r := r) G n : Set _)) := by
  classical
  have hs := (Submodule.mem_inf.1 hg).1
  rw [Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff] at hs
  rw [g.as_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hm' := hs hm
  obtain ⟨hsupp, hsum⟩ := hm'
  have hmono : monomial m (AddMonoidAlgebra.coeff g m) = AddMonoidAlgebra.coeff g m • monomial m (1 : ℚ_[p]) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmono]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, ?_, rfl⟩)
  unfold xiMons
  rw [Finset.mem_coe, Finset.mem_image]
  refine ⟨fun c => m (Formalism.GM.M.xiVar N r G.T.t c), (CountingStatementReduction.mem_Ev _).2 hsum, ?_⟩
  ext v
  rw [Finsupp.finsetSum_apply]
  by_cases hv : ∃ c, v = Formalism.GM.M.xiVar N r G.T.t c
  · obtain ⟨c, rfl⟩ := hv
    rw [Finset.sum_eq_single c]
    · simp
    · intro d _ hd
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hd (xiVar_inj G h)
    · intro h; exact absurd (Finset.mem_univ c) h
  · have h0 : m v = 0 := by
      by_contra hne
      exact hv (hsupp v (Finsupp.mem_support_iff.2 hne))
    rw [h0]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hv ⟨c, h.symm⟩

theorem finrank_Ljj_le (j : Fin G.T.t → ℕ) (jp : ℕ) :
    Module.finrank ℤ_[p] (Ljj p (r := r) G j jp) ≤ dimY p (r := r) G j jp * dXi r (G.B - jp) := by
  classical
  set Yq := Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr with hYq
  haveI : FiniteDimensional ℚ_[p] (Formalism.GM.M.Pol p r (G.lettersAt j jp)) := Formalism.CountingSumsFrames.pol_finiteDimensional _
  haveI : FiniteDimensional ℚ_[p] Yq := Submodule.finiteDimensional_of_le inf_le_left
  let bY := Module.finBasis ℚ_[p] Yq
  let Ms := xiMons (r := r) G (G.B - jp)
  let fam : Fin (Module.finrank ℚ_[p] Yq) × Ms → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p] :=
    fun ab => rename (Formalism.GM.M.chainEmb N r G.T.t) ((bY ab.1 : Yq) : _) * monomial (ab.2 : _ →₀ ℕ) 1
  let W := Submodule.span ℚ_[p] (Set.range fam)
  have hsub : ∀ x ∈ Ljj p (r := r) G j jp, x ∈ W := by
    intro x hx
    have hle : Ljj p (r := r) G j jp ≤ W.restrictScalars ℤ_[p] := by
      unfold Ljj
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, g, hg, rfl⟩
      have hyY : y ∈ Yq := (Submodule.mem_inf.1 hy).1
      have hy2 : y ∈ Submodule.span ℚ_[p] (Set.range fun a => ((bY a : Yq) : MvPolynomial _ ℚ_[p])) := by
        have h3 : (⟨y, hyY⟩ : Yq) ∈ (⊤ : Submodule ℚ_[p] Yq) := Submodule.mem_top
        rw [← bY.span_eq] at h3
        have h4 := Submodule.mem_map_of_mem (f := Yq.subtype) h3
        rw [Submodule.map_span, ← Set.range_comp] at h4
        exact h4
      have hg2 := xi_mem_span p G (G.B - jp) g hg
      show rename (Formalism.GM.M.chainEmb N r G.T.t) y * g ∈ W
      have hy3 : rename (Formalism.GM.M.chainEmb N r G.T.t) y ∈ Submodule.span ℚ_[p]
          (Set.range fun a => rename (Formalism.GM.M.chainEmb N r G.T.t) ((bY a : Yq) : MvPolynomial _ ℚ_[p])) := by
        have := Submodule.mem_map_of_mem (f := (rename (Formalism.GM.M.chainEmb N r G.T.t) :
          MvPolynomial _ ℚ_[p] →ₐ[ℚ_[p]] MvPolynomial _ ℚ_[p]).toLinearMap) hy2
        rw [Submodule.map_span, ← Set.range_comp] at this
        exact this
      have hmul := Submodule.mul_mem_mul hy3 hg2
      rw [Submodule.span_mul_span] at hmul
      refine Submodule.span_mono ?_ hmul
      rintro _ ⟨u, ⟨a, rfl⟩, v, ⟨m, hm, rfl⟩, rfl⟩
      exact ⟨(a, ⟨m, hm⟩), rfl⟩
    exact hle hx
  haveI : FiniteDimensional ℚ_[p] W := FiniteDimensional.span_of_finite ℚ_[p] (Set.finite_range fam)
  have h1 := finrank_zp_le (Ljj p (r := r) G j jp) W hsub
  have h2 : Module.finrank ℚ_[p] W ≤ Fintype.card (Fin (Module.finrank ℚ_[p] Yq) × Ms) := finrank_range_le_card fam
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] at h2
  have h3 := card_xiMons (r := r) G (G.B - jp)
  calc Module.finrank ℤ_[p] (Ljj p (r := r) G j jp) ≤ Module.finrank ℚ_[p] Yq * Ms.card := h1.trans h2
    _ ≤ dimY p (r := r) G j jp * dXi r (G.B - jp) := Nat.mul_le_mul le_rfl h3

end Level

theorem restRankL_proved (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) : RestRankL C0 CE1 CE2 X := by
  intro dl _ aTop _ x _
  exact finrank_Ljj_le X.p (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.StructureSheafH2BaseChange
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory

section Map

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (ι : ℚ_[p] →+* KK O)

theorem map_glAct {N r : ℕ} (LL : ChainLetters N) (j : ℕ) (c d : Fin r) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct (KK O) (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d (map ι F) =
      map ι (Formalism.GM.M.glAct p (gmL LL) j c d F) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [glAct, Formalism.GM.M.glAct, gmL, LinearMap.sum_apply, map_sum, Set.mem_setOf_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : (i : ℕ) < j <;> by_cases h2 : LL.vec i = true <;> simp [h1, h2, pderiv_map]

theorem gm_ycond_stable {N r : ℕ} [NeZero r] (LL : Formalism.GM.M.Letters N) (j : ℕ) (Mt : WithTop ℤ) (c d : Fin r) :
    ∀ x ∈ Formalism.GM.M.YCond p (r := r) LL j Mt, Formalism.GM.M.glAct p LL j c d x ∈ Formalism.GM.M.YCond p (r := r) LL j Mt := by
  intro x hx
  have key : Formalism.GM.M.YCond p (r := r) LL j Mt ≤
      (Formalism.GM.M.YCond p (r := r) LL j Mt).comap (Formalism.GM.M.glAct p LL j c d) := by
    conv_lhs => unfold Formalism.GM.M.YCond
    refine sSup_le fun S hS y hy => ?_
    rw [Submodule.mem_comap]
    unfold Formalism.GM.M.YCond
    exact le_sSup hS (hS.2 c d y hy)
  exact key hx

theorem gm_ycond_supp {N r : ℕ} [NeZero r] (LL : Formalism.GM.M.Letters N) (j : ℕ) (Mt : WithTop ℤ) :
    Formalism.GM.M.YCond p (r := r) LL j Mt ≤
      restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((Formalism.GM.M.wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} :=
  sSup_le fun _ hS => hS.1

theorem map_mem_restrictSupport {σ : Type} {s : Set (σ →₀ ℕ)} (F : MvPolynomial σ ℚ_[p])
    (hF : F ∈ restrictSupport ℚ_[p] s) : map ι F ∈ restrictSupport (KK O) s := by
  rw [mem_restrictSupport_iff] at hF ⊢
  exact (Finset.coe_subset.2 (support_map_subset ι F)).trans hF

theorem map_ycond {N r : ℕ} [NeZero r] (LL : ChainLetters N) (j : ℕ) (Mt : WithTop ℤ)
    (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hy : y ∈ Formalism.GM.M.YCond p (r := r) (gmL LL) j Mt) :
    map ι y ∈ Formalism.MainNotions.G.YCond (KK O) (r := r) LL j Mt := by
  have hsupp : Submodule.span (KK O) (map ι '' ((Formalism.GM.M.YCond p (r := r) (gmL LL) j Mt : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) : Set (MvPolynomial (Fin N × Fin r) ℚ_[p]))) ≤
      restrictSupport (KK O) {m : Fin N × Fin r →₀ ℕ | ((chWt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
    rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    exact map_mem_restrictSupport ι z (gm_ycond_supp (gmL LL) j Mt hz)
  have hstab : chStable (KK O) (r := r) LL j
      (Submodule.span (KK O) (map ι '' ((Formalism.GM.M.YCond p (r := r) (gmL LL) j Mt : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) : Set (MvPolynomial (Fin N × Fin r) ℚ_[p])))) := by
    intro c d x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      apply Submodule.subset_span
      exact ⟨_, gm_ycond_stable (gmL LL) j Mt c d z hz, (map_glAct ι LL j c d z).symm⟩
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add (f := _)]
      exact add_mem ha hb
    | smul k a _ ha =>
      rw [map_smul]
      exact Submodule.smul_mem _ k ha
  have hy' : map ι y ∈ Submodule.span (KK O) (map ι '' ((Formalism.GM.M.YCond p (r := r) (gmL LL) j Mt : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) : Set (MvPolynomial (Fin N × Fin r) ℚ_[p]))) :=
    Submodule.subset_span ⟨y, hy, rfl⟩
  unfold Formalism.MainNotions.G.YCond
  exact le_sSup (show _ ∈ {S : Submodule (KK O) (MvPolynomial (Fin N × Fin r) (KK O)) |
      S ≤ restrictSupport (KK O) {m : Fin N × Fin r →₀ ℕ | ((chWt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} ∧
        chStable (KK O) LL j S} from ⟨hsupp, hstab⟩) hy'

theorem map_Y {N r : ℕ} [NeZero r] (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hy : y ∈ Formalism.GM.M.Y p (r := r) (gmL LL) J M) :
    map ι y ∈ Yjt (KK O) (r := r) LL J M := by
  rw [Formalism.GM.M.Y, Submodule.mem_inf, Submodule.mem_iInf] at hy
  rw [Yjt, Submodule.mem_inf, Submodule.mem_iInf]
  refine ⟨?_, fun k => map_ycond ι LL (J k) (M k) y (hy.2 k)⟩
  exact map_mem_restrictSupport ι y hy.1

variable {ι}

theorem map_int {σ : Type} (hint : ∀ x : ℤ_[p], ∃ y : O, ι (x : ℚ_[p]) = algebraMap O (KK O) y)
    (F : MvPolynomial σ ℚ_[p]) (hF : F ∈ Formalism.GM.M.IntPol p σ) : map ι F ∈ IntPol O σ := by
  obtain ⟨G, rfl⟩ := hF
  induction G using MvPolynomial.induction_on' with
  | monomial m a =>
    obtain ⟨y, hy⟩ := hint a
    refine ⟨monomial m y, ?_⟩
    simp [hy]
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _)]
    exact add_mem ha hb

theorem map_YZ {N r : ℕ} [NeZero r] (hint : ∀ x : ℤ_[p], ∃ y : O, ι (x : ℚ_[p]) = algebraMap O (KK O) y)
    (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hy : y ∈ Formalism.GM.M.YZ p (r := r) (gmL LL) J M) :
    map ι y ∈ YjtZ O (r := r) LL J M := by
  rw [Formalism.GM.M.YZ, Submodule.mem_inf] at hy
  have h2 : y ∈ Submodule.restrictScalars ℤ_[p] (Formalism.GM.M.Pol p r (gmL LL)) ⊓ Formalism.GM.M.IntPol p (Fin N × Fin r) := hy.2
  exact Submodule.mem_inf.2 ⟨map_Y ι LL J M y hy.1, map_int hint y (Submodule.mem_inf.1 h2).2⟩

theorem map_XiPolZ {N r t b : ℕ} (hint : ∀ x : ℤ_[p], ∃ y : O, ι (x : ℚ_[p]) = algebraMap O (KK O) y)
    (g : MvPolynomial (Formalism.GM.M.BVar N r t) ℚ_[p]) (hg : g ∈ Formalism.GM.M.XiPolZ p N r t b) :
    map ι g ∈ XiPolZ O N r t b := by
  have hg' := Submodule.mem_inf.1 hg
  exact Submodule.mem_inf.2 ⟨map_mem_restrictSupport ι g hg'.1, map_int hint g hg'.2⟩

end Map

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

