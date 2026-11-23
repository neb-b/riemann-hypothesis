module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.OddWeightCycles.WOneOdd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBStarOdd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.Weights

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.OddWeightCycles.AevApply
section
noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.BlockEvaluationBounds

open BlockInvariants

variable {L : Type} [Field L] [NumberField L]

def Aev (m : ℕ) {q : ℕ} (x : Pat L q) : Chn (Gm L m) q →ₗ[ℝ] ℝ :=
  evL (emb L m) (intP (ext (AT (N := m) x))) (one L m)

theorem Aev_apply (m : ℕ) {q : ℕ} (x : Pat L q) (z : Chn (Gm L m) q) :
    Aev m x z = ev (emb L m) (intP (ext (AT (N := m) x))) (one L m) z := evL_apply _ _ _ _

theorem Aev_bd (hE : SEv) (hS : SStokes) (hG : AGood) (hWI : WInv) {m k : ℕ} (x : Pat L (k + 1))
    (z : Chn (Gm L m) (k + 1)) (hz : IsBd z) : Aev m x z = 0 := by
  have hI : ∀ g, FInv (ext (AT (N := m) x)) g := fInv_ext (hWI L m _ x)
  rw [Aev_apply]
  exact (hE (Gm L m) (Gp L m) (Pos L m) (emb L m) k _ (fun g y => intP_inv hI (emb L m g) y)
    (hG hS L m _ _ hI).2).1 _ z hz

theorem Aev_stab (hWP : WPad) (hWI : WInv) (hTS : TStab) (hPS : PStab) {n n' q : ℕ} (h : n ≤ n') (x : Pat L q)
    (z : Chn (Gm L n) q) : Aev n' x (cmap (stab (𝓞 L) n n' h) q z) = Aev n x z := by
  rw [Aev_apply, Aev_apply, ev_stab hTS]
  congr 1
  refine intP_congr fun p hp => ?_
  rw [ext_uniq (hPS L n n' _ h _ (fInv_ext (hWI L n' _ x))) hp]
  congr 1
  simp only [pullF]
  rw [padL_one, ext_one (hWI L n' _ x), hWP L n n' _ h x]

theorem Aev_blk (hWB : WBlk) (hWI : WInv) (hTB : TBlk) (hPB : PBlk) (d n : ℕ) {q : ℕ} (x : Pat L q)
    (z : Chn (Gm L n) q) : Aev (d * n) x (cmap (psi (𝓞 L) d n) q z) = (d : ℝ) ^ ncyc x.1 * Aev n x z := by
  rw [Aev_apply, Aev_apply, ev_blk hTB, ← ev_mul]
  congr 1
  rw [← intP_smul]
  refine intP_congr fun p hp => ?_
  rw [ext_uniq (hPB L d n _ _ (fInv_ext (hWI L (d * n) _ x))) hp]
  simp only [pullF, add_zero]
  rw [blkL_one, ext_one (hWI L (d * n) _ x), hWB L d n _ x, ext_smul]

theorem Aev_comb (hS : SStokes) (hG : AGood) (hWI : WInv) {m q : ℕ} (x y y' : Pat L q) (r : ℝ)
    (he : AT (N := m) x = r • (AT (N := m) y + AT (N := m) y')) (z : Chn (Gm L m) q) :
    Aev m x z = r * (Aev m y z + Aev m y' z) := by
  have hc : ∀ i : Fin 2, ContinuousOn (ext (![AT (N := m) y, AT (N := m) y'] i)) (Pos L m) := by
    intro i
    fin_cases i
    · exact (hG hS L m q _ (fInv_ext (hWI L m q y))).1
    · exact (hG hS L m q _ (fInv_ext (hWI L m q y'))).1
  have hsum : r • (AT (N := m) y + AT (N := m) y') =
      ∑ i : Fin 2, (fun _ => r) i • ![AT (N := m) y, AT (N := m) y'] i := by
    simp [Fin.sum_univ_two]
  have h1 : ext (AT (N := m) x) =
      fun h => ∑ i : Fin 2, (fun _ => r) i • ext (![AT (N := m) y, AT (N := m) y'] i) h := by
    funext h
    rw [he, hsum, ext_sum]
  have h2 := intP_sum (fun _ : Fin 2 => r) _ hc
  rw [Aev_apply, Aev_apply, Aev_apply, h1, h2, ev_sum]
  simp [Fin.sum_univ_two, mul_add]

theorem swtOdd (hE : SEv) (hS : SStokes) (hF : FFT) (hG : AGood) (hWP : WPad) (hWB : WBlk) (hWI : WInv)
    (hWC : WCyc) (hTS : TStab) (hTB : TBlk) (hPS : PStab) (hPB : PBlk) (hWO : WOneOdd) (hR : WRot) :
    SWtOdd := by
  intro L _ _ k hk
  classical
  have hodd : Odd (k + 1) := hk.add_one
  have hpos : 0 < k + 1 := Nat.succ_pos k
  have hrot : ncyc (finRotate (k + 1)) = 1 := hR (k + 1) hpos
  refine ⟨fun w n => Aev n ((finRotate (k + 1), fun _ => w, false) : Pat L (k + 1)) +
    Aev n ((finRotate (k + 1), fun _ => w, true) : Pat L (k + 1)), ?_, ?_⟩
  · intro w
    refine ⟨?_, ?_, ?_⟩
    · intro n z hz
      simp only [LinearMap.add_apply]
      rw [Aev_bd hE hS hG hWI _ z hz, Aev_bd hE hS hG hWI _ z hz, add_zero]
    · intro n n' h z _
      simp only [LinearMap.add_apply]
      rw [Aev_stab hWP hWI hTS hPS h, Aev_stab hWP hWI hTS hPS h]
    · intro d n z _ _
      simp only [LinearMap.add_apply]
      rw [Aev_blk hWB hWI hTB hPB, Aev_blk hWB hWI hTB hPB]
      simp only [hrot, pow_one]
      ring
  · intro N ω hω
    obtain ⟨c, hc⟩ := hF L N (k + 1) _ (uInv_of hω)
    have hone : ∀ x : Pat L (k + 1), ncyc x.1 = 1 → ∃ (r : ℝ) (w : InfinitePlace L),
        AT (N := N) x = r • (AT (N := N) ((finRotate (k + 1), fun _ => w, false) : Pat L (k + 1)) +
          AT (N := N) ((finRotate (k + 1), fun _ => w, true) : Pat L (k + 1))) :=
      fun x hx => hWO L N (k + 1) x hodd hx
    choose! rx wx hrw using hone
    refine ⟨fun w => ∑ x, if ncyc x.1 = 1 ∧ wx x = w then c x * rx x else 0,
      fun j n => ∑ x, (if ncyc x.1 = j then c x else 0) • Aev n x, ?_, ?_⟩
    · intro j _
      refine ⟨?_, ?_, ?_⟩
      · intro n z hz
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
        exact Finset.sum_eq_zero fun x _ => by rw [Aev_bd hE hS hG hWI x z hz, mul_zero]
      · intro n n' h z _
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl fun x _ => by rw [Aev_stab hWP hWI hTS hPS h]
      · intro d n z _ _
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Aev_blk hWB hWI hTB hPB]
        split_ifs with hj
        · rw [hj]
          ring
        · simp
    · intro z _
      have hcont : ∀ x : Pat L (k + 1), ContinuousOn (ext (AT (N := N) x)) (Pos L N) :=
        fun x => (hG hS L N (k + 1) _ (fInv_ext (hWI L N (k + 1) x))).1
      have h1 : intP ω = fun p => ∑ x, c x * intP (ext (AT (N := N) x)) p := by
        rw [← intP_sum c _ hcont]
        apply intP_congr
        intro p hp
        rw [ext_uniq hω hp, hc, ext_sum]
      have e1 : ∀ x : Pat L (k + 1), (∑ w, (if ncyc x.1 = 1 ∧ wx x = w then c x * rx x else 0) *
          (Aev N ((finRotate (k + 1), fun _ => w, false) : Pat L (k + 1)) z +
            Aev N ((finRotate (k + 1), fun _ => w, true) : Pat L (k + 1)) z)) =
          if ncyc x.1 = 1 then c x * Aev N x z else 0 := by
        intro x
        by_cases h : ncyc x.1 = 1
        · simp only [h, true_and, if_true, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ]
          rw [Aev_comb hS hG hWI _ _ _ _ (hrw x h) z]
          ring
        · simp [h]
      have e2 : ∀ x : Pat L (k + 1), (∑ j ∈ Finset.Icc 2 (k + 1),
          (if ncyc x.1 = j then c x else 0) * Aev N x z) =
          if ncyc x.1 = 1 then 0 else c x * Aev N x z := by
        intro x
        have hb := hWC (k + 1) x.1 hpos
        simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_Icc]
        split_ifs with h1 h2 h2
        · omega
        · rfl
        · rfl
        · omega
      rw [h1, ev_sum]
      simp only [← Aev_apply, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm (s := (Finset.univ : Finset (InfinitePlace L))),
        Finset.sum_comm (s := Finset.Icc 2 (k + 1)), ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [e1 x, e2 x]
      split_ifs <;> ring

end PositivityTheory.KB.BlockEvaluationBounds

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.OddWeightCycles.Weights
section
noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.BlockEvaluationBounds

open BlockInvariants BlockInvariants.AlternatingWeights

namespace AlternatingWeights

variable {L : Type} [Field L] [NumberField L]

theorem tmC_relabel {N q : ℕ} (ρ c : Equiv.Perm (Fin q)) (w0 : InfinitePlace L) (Y : Fin q → HS L N) :
    tmC (c⁻¹ * ρ * c) (fun _ => w0) Y = tmC ρ (fun _ => w0) (Y ∘ ⇑c⁻¹) := by
  unfold tmC
  rw [if_pos (fun _ => rfl), if_pos (fun _ => rfl)]
  simp only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply, LinearMap.coe_toContinuousLinearMap', Function.comp_apply]
  refine Fintype.sum_equiv (Equiv.arrowCongr c (Equiv.refl _)) _ _ (fun a => ?_)
  refine Fintype.prod_equiv c _ _ (fun i => ?_)
  simp [Equiv.arrowCongr_apply, Equiv.Perm.mul_apply]

theorem tmC_inv_star {N q : ℕ} (ρ : Equiv.Perm (Fin q)) (w0 : InfinitePlace L) (Y : Fin q → HS L N) :
    tmC ρ⁻¹ (fun _ => w0) Y = star (tmC ρ (fun _ => w0) Y) := by
  unfold tmC
  rw [if_pos (fun _ => rfl), if_pos (fun _ => rfl)]
  simp only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply, LinearMap.coe_toContinuousLinearMap', star_sum, star_prod]
  refine Fintype.sum_equiv (Equiv.arrowCongr ρ (Equiv.refl _)) _ _ (fun b => ?_)
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [ent, mat, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_id, Function.comp_apply,
    LinearMap.coe_mk, AddHom.coe_mk]
  have hh := ((Y i).2 w0).apply (b i) (b (ρ⁻¹ i))
  simp only [Matrix.of_apply] at hh ⊢
  simp only [id, Equiv.symm_apply_apply, ← Equiv.Perm.inv_def]
  have e : ρ⁻¹ (ρ i) = i := by simp
  rw [e]
  exact hh.symm

theorem rot_rev (q : ℕ) :
    (Fin.revPerm : Equiv.Perm (Fin q))⁻¹ * finRotate q * Fin.revPerm = (finRotate q)⁻¹ := by
  rcases q with _ | n
  · exact Subsingleton.elim _ _
  · rw [eq_inv_iff_mul_eq_one]
    ext i
    simp [Equiv.Perm.inv_def, finRotate_apply, Fin.revPerm_apply, Fin.rev_add]

theorem alt_relabel {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : ℕ}
    (f g : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) ℝ) (τ : Equiv.Perm (Fin q))
    (h : ∀ v, f v = g (v ∘ τ)) :
    ContinuousMultilinearMap.alternatization f =
      ((Equiv.Perm.sign τ : ℤ) : ℝ) • ContinuousMultilinearMap.alternatization g := by
  ext v
  rw [ContinuousAlternatingMap.smul_apply, ContinuousMultilinearMap.alternatization_apply_apply,
    ContinuousMultilinearMap.alternatization_apply_apply, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight τ) _ _ (fun σ => ?_)
  simp only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, h, Equiv.Perm.coe_mul, Function.comp_assoc]
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with hs | hs <;> simp [hs]

theorem alt_zero' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) ℝ) (σ : Equiv.Perm (Fin q))
    (hf : ∀ v, f (v ∘ σ) = -f v) (hs : Equiv.Perm.sign σ = 1) :
    ContinuousMultilinearMap.alternatization f = 0 := by
  have h2 := alt_relabel f (-f) σ (fun v => by
    rw [ContinuousMultilinearMap.neg_apply, hf, neg_neg])
  rw [hs, map_neg] at h2
  ext v
  have h3 := congrArg (fun F => F v) h2
  simp at h3
  simp
  linarith

theorem const_of_cycle {q : ℕ} {α : Type} (σ : Equiv.Perm (Fin q)) (w : Fin q → α)
    (hw : ∀ i, w (σ i) = w i) (a b : Fin q) (hab : σ.SameCycle a b) : w a = w b := by
  obtain ⟨k, rfl⟩ := hab
  have key : ∀ n : ℕ, ∀ x, w ((σ ^ n) x) = w x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [pow_succ', Equiv.Perm.mul_apply, hw, ih]
  rcases k with n | n
  · simp only [Int.ofNat_eq_coe, zpow_natCast]
    exact (key n a).symm
  · have e : (σ ^ (n + 1)) ((σ ^ (n + 1))⁻¹ a) = a := by simp
    rw [zpow_negSucc, ← key (n + 1) ((σ ^ (n + 1))⁻¹ a), e]

theorem sameCycle_of_ncyc {q : ℕ} (σ : Equiv.Perm (Fin q)) (h : ncyc σ = 1) (x y : Fin q) : σ.SameCycle x y := by
  have h1 := (Nat.card_eq_one_iff_unique.mp h).1
  exact Quotient.exact (Subsingleton.elim (Quotient.mk (Equiv.Perm.SameCycle.setoid σ) x) (Quotient.mk _ y))

theorem conj_rot {q : ℕ} (σ : Equiv.Perm (Fin q)) (h : ncyc σ = 1) :
    ∃ c : Equiv.Perm (Fin q), σ = c⁻¹ * finRotate q * c := by
  rcases q with _ | _ | n
  · exact ⟨1, Subsingleton.elim _ _⟩
  · refine ⟨1, ?_⟩
    apply Equiv.ext
    intro i
    apply Fin.ext
    have h1 := (σ i).2
    have h2 := ((1⁻¹ * finRotate (0 + 1) * 1 : Equiv.Perm (Fin (0 + 1))) i).2
    omega
  · have hsc := sameCycle_of_ncyc σ h
    have hne : σ ≠ 1 := by
      intro h1
      have h01 := hsc 0 1
      rw [h1] at h01
      simp at h01
    obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
      by_contra hc
      push_neg at hc
      exact hne (Equiv.ext hc)
    have hall : ∀ y, σ y ≠ y := fun y hy => hx (((hsc x y).apply_eq_self_iff).mpr hy)
    have hcyc : σ.IsCycle := ⟨x, hx, fun y _ => hsc x y⟩
    have hsupp : σ.support = Finset.univ := by
      ext y
      simp [Equiv.Perm.mem_support, hall y]
    have hct : σ.cycleType = (finRotate (n + 2)).cycleType := by
      rw [hcyc.cycleType, isCycle_finRotate.cycleType, hsupp, support_finRotate]
    obtain ⟨c, hc⟩ := isConj_iff.mp (Equiv.Perm.isConj_iff_cycleType_eq.mpr hct)
    exact ⟨c, by rw [← hc]; group⟩

end AlternatingWeights

open AlternatingWeights

theorem wRot : WRot := by
  intro q hq
  have hs : ∀ x y : Fin q, (finRotate q).SameCycle x y := by
    intro x y
    rcases q with _ | _ | n
    · exact x.elim0
    · obtain rfl : x = y := Fin.ext (by have := x.2; have := y.2; omega)
      exact Equiv.Perm.SameCycle.refl _ _
    · exact isCycle_finRotate.sameCycle
        (by rw [← Equiv.Perm.mem_support, support_finRotate]; exact Finset.mem_univ _)
        (by rw [← Equiv.Perm.mem_support, support_finRotate]; exact Finset.mem_univ _)
  rw [ncyc, Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun a b => Quotient.inductionOn₂ a b (fun x y => Quotient.sound (hs x y))⟩,
    ⟨Quotient.mk _ ⟨0, hq⟩⟩⟩

theorem wOneOdd : WOneOdd := by
  intro L _ _ N q x hodd hx
  obtain ⟨σ, w, ε⟩ := x
  have hq : 0 < q := hodd.pos
  have hx' : ncyc σ = 1 := hx
  by_cases hw : ∀ i, w (σ i) = w i
  · obtain ⟨w0, rfl⟩ : ∃ w0, w = fun _ => w0 :=
      ⟨w ⟨0, hq⟩, funext fun i => const_of_cycle σ w hw i ⟨0, hq⟩ (sameCycle_of_ncyc σ hx' i ⟨0, hq⟩)⟩
    obtain ⟨c, rfl⟩ := conj_rot σ hx'
    have hrel : AT (N := N) ((c⁻¹ * finRotate q * c, fun _ => w0, ε) : Pat L q) =
        ((Equiv.Perm.sign c⁻¹ : ℤ) : ℝ) • AT (N := N) ((finRotate q, fun _ => w0, ε) : Pat L q) := by
      simp only [AT]
      apply alt_relabel
      intro v
      simp only [tmR, ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, tmC_relabel]
    have hrev : ∀ Y : Fin q → HS L N, tmC (finRotate q) (fun _ => w0) (Y ∘ ⇑(Fin.revPerm : Equiv.Perm (Fin q))⁻¹)
        = star (tmC (finRotate q) (fun _ => w0) Y) := by
      intro Y
      rw [← tmC_relabel, rot_rev, tmC_inv_star]
    have hrev' : ∀ Y : Fin q → HS L N, tmC (finRotate q) (fun _ => w0) (Y ∘ ⇑(Fin.revPerm : Equiv.Perm (Fin q)))
        = star (tmC (finRotate q) (fun _ => w0) Y) := by
      intro Y
      simpa using hrev Y
    have hvan : AT (N := N) ((finRotate q, fun _ => w0, true) : Pat L q) = 0 ∨
        AT (N := N) ((finRotate q, fun _ => w0, false) : Pat L q) = 0 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign ((Fin.revPerm : Equiv.Perm (Fin q))⁻¹)) with hs | hs
      · left
        simp only [AT]
        apply alt_zero' _ ((Fin.revPerm : Equiv.Perm (Fin q))⁻¹) _ hs
        intro v
        simp [tmR, hrev']
      · right
        have h2 := alt_relabel (tmR (N := N) (finRotate q) (fun _ => w0) false)
          (tmR (finRotate q) (fun _ => w0) false) ((Fin.revPerm : Equiv.Perm (Fin q))⁻¹)
          (fun v => by simp [tmR, hrev'])
        rw [hs] at h2
        simp only [AT]
        ext v
        have h3 := congrArg (fun F => F v) h2
        simp at h3
        simp
        linarith
    rcases hvan with h0 | h0 <;> cases ε
    · exact ⟨((Equiv.Perm.sign c⁻¹ : ℤ) : ℝ), w0, by rw [hrel, h0, add_zero]⟩
    · exact ⟨0, w0, by rw [hrel, h0, smul_zero, zero_smul]⟩
    · exact ⟨0, w0, by rw [hrel, h0, smul_zero, zero_smul]⟩
    · exact ⟨((Equiv.Perm.sign c⁻¹ : ℤ) : ℝ), w0, by rw [hrel, h0, zero_add]⟩
  · refine ⟨0, w ⟨0, hq⟩, ?_⟩
    rw [zero_smul]
    have h0 : tmR (N := N) σ w ε = 0 := by
      ext v
      simp only [tmR, tmC, if_neg hw, ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
        ContinuousMultilinearMap.zero_apply, map_zero]
    simp only [AT]
    rw [h0, map_zero]

end PositivityTheory.KB.BlockEvaluationBounds

end
end

