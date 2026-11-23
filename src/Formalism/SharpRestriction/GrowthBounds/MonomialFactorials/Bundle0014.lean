module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0013
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.WindowEntryLeTwoMulA

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BePhiAddLeft
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM.ProjS

def OrthLat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])) (D : ℤ),
    p ≠ 2 → FiniteDimensional ℚ_[p] W → (∀ x ∈ L, x ∈ W) → L.FG →
    (∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) → (∀ u u' v, B (u + u') v = B u v + B u' v) →
    (∀ u ∈ L, ∀ v ∈ L, B u v = B v u) →
    ∃ (n₁ : ℕ) (e : Fin n₁ → MvPolynomial σ ℚ_[p]), (∀ a, e a ∈ L) ∧ LinearIndependent ℤ_[p] e ∧
      (∀ a b, a ≠ b → B (e a) (e b) = 0) ∧ (∀ a, B (e a) (e a) ≠ 0 ∧ (B (e a) (e a)).valuation ≤ D) ∧
      n₁ ≤ Module.finrank ℤ_[p] L ∧ Module.finrank ℤ_[p] L ≤ n₁ + Formalism.GM.M.bad p B L D

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestSymm : Prop :=
  ∀ dl ∈ CountingStatementReduction.clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    ∀ u ∈ Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2,
      ∀ v ∈ Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2,
        bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 u v =
          bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 v u

def RestLjjFin : Prop :=
  ∀ dl ∈ CountingStatementReduction.clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2).FG ∧
    ∃ W : Submodule ℚ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop 0 x.1).T.t) ℚ_[X.p]),
      FiniteDimensional ℚ_[X.p] W ∧ ∀ u ∈ Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2, u ∈ W

section Lin

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem bePhi_add_left (j : Fin G.T.t → ℕ) (jp : ℕ) (u u' v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    bePhi p (r := r) G j jp (u + u') v = bePhi p (r := r) G j jp u v + bePhi p (r := r) G j jp u' v := by
  have hs := bePhi_sum_left p (r := r) G j jp (Finset.univ : Finset (Fin 2)) ![u, u'] v
  simpa [Fin.sum_univ_two] using hs

end Lin

variable {C0 CE1 CE2 X}

theorem restOrth_of (CM : ℝ) (hp2 : X.p ≠ 2) (hO : OrthLat) (hS : RestSymm C0 CE1 CE2 X)
    (hF : RestLjjFin C0 CE1 CE2 X) : RestOrth C0 CE1 CE2 X CM := by
  intro dl hdl aTop ha x hx
  obtain ⟨hfg, W, hW, hLW⟩ := hF dl hdl aTop ha x hx
  exact hO X.p _ _ _ W _ hp2 hW hLW hfg
    (fun c u v => bePhi_smul_left _ _ _ _ c u v)
    (fun u u' v => bePhi_add_left _ _ _ _ u u' v)
    (hS dl hdl aTop ha x hx)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.FockKSmulRight
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

end Formalism.MainNotions.G.SymmetricFormBlocks

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem winA_sum (X : flipOneThree.Inst) (f : ℕ → ℝ) :
    ∑ aPlus ∈ X.winA, f aPlus = ∑ j ∈ Finset.range X.winA.card, f (X.L.a + j) := by
  unfold flipOneThree.Inst.winA
  rw [Nat.card_Icc, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ProdProdIte
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open Finset Formalism.GM Formalism.GM.M
open scoped Nat

theorem prod_prod_ite {α ι : Type} [Fintype α] [DecidableEq α] [Fintype ι] (x : ι → α) (n : ι → ℕ) :
    ∏ a : α, ∏ i : ι, (if x i = a then n i else 0)! = ∏ i, (n i)! := by
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_eq_single (x i)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem smul_ite_one (n : ℕ) (c : Prop) [Decidable c] : n • (if c then 1 else 0 : ℕ) = if c then n else 0 := by
  split_ifs <;> simp

section Block

variable (p : ℕ) [hp : Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

def fL (j : Fin G.T.t → ℕ) (jp : ℕ) (a : Fin (N + 1)) : ℕ :=
  (∏ i, ((if M.finPos N (G.T.pos i) = a then j i else 0)! * (if M.finPos N (G.T.pos i + 1) = a then j i else 0)!)) *
    ((if Fin.castSucc G.uPos = a then jp else 0)! * (if Fin.last N = a then jp else 0)!) *
    (∏ i, (if M.finPos N (G.T.pos i) = a then G.T.z i else 0)!) *
    (if Fin.castSucc G.uPos = a then G.zPlus else 0)! *
    (∏ a0 : Fin N, (if Fin.castSucc a0 = a then (G.lettersAt j jp).deg a0 else 0)!) *
    (if Fin.last N = a then G.B - jp else 0)!

theorem fL_dvd (j : Fin G.T.t → ℕ) (jp : ℕ) (a : Fin (N + 1)) : fL G j jp a ∣ (dLvl G j jp a)! := by
  have hfac : ∀ {x y X Y : ℕ}, x ∣ X ! → y ∣ Y ! → x * y ∣ (X + Y)! := fun hx hy =>
    (mul_dvd_mul hx hy).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
  unfold fL dLvl chDeg
  simp only [smul_add, smul_ite_one]
  refine hfac (hfac (hfac (hfac (hfac ?_ ?_) ?_) dvd_rfl) ?_) dvd_rfl
  · exact (Finset.prod_dvd_prod_of_dvd _ _ fun i _ =>
      Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans (Nat.prod_factorial_dvd_factorial_sum _ _)
  · exact Nat.factorial_mul_factorial_dvd_factorial_add _ _
  · exact Nat.prod_factorial_dvd_factorial_sum _ _
  · exact Nat.prod_factorial_dvd_factorial_sum _ _

theorem prod_fL (j : Fin G.T.t → ℕ) (jp : ℕ) :
    ∏ a, fL G j jp a = (∏ i, (j i)!) * (∏ i, (j i)!) * (jp ! * jp !) * (∏ i, (G.T.z i)!) * G.zPlus ! *
      (∏ a0, ((G.lettersAt j jp).deg a0)!) * (G.B - jp)! := by
  have hsingle : ∀ (b : Fin (N + 1)) (n : ℕ), ∏ a, (if b = a then n else 0)! = n ! := by
    intro b n
    rw [Finset.prod_eq_single b]
    · simp
    · intro a _ ha
      simp [Ne.symm ha]
    · simp
  unfold fL
  simp only [Finset.prod_mul_distrib, prod_prod_ite, hsingle]

def binT (j : Fin G.T.t → ℕ) (jp : ℕ) (i : Fin G.T.t) : ℕ :=
  ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i)) +
    (G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)) + r + G.T.z i + 1 + j i - 1).choose (j i)

def binP (jp : ℕ) : ℕ := ((G.LL.deg G.uPos - jp) + (G.B - jp) + r + G.zPlus + 1 + jp - 1).choose jp

theorem lvC_eq (j : Fin G.T.t → ℕ) (jp : ℕ) :
    lvC (r := r) G j jp * degFact G j jp = (∏ a, fL G j jp a) * ((∏ i, binT (r := r) G j jp i) * binP (r := r) G jp) := by
  rw [prod_fL]
  unfold lvC degFact binT binP
  rw [Finset.prod_mul_distrib]
  ring

theorem val_lvC_le (j : Fin G.T.t → ℕ) (jp : ℕ) (L : ℕ)
    (h1 : ∀ i, Nat.log p ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i)) +
      (G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)) + r + G.T.z i + 1 + j i - 1) ≤ L)
    (h2 : Nat.log p ((G.LL.deg G.uPos - jp) + (G.B - jp) + r + G.zPlus + 1 + jp - 1) ≤ L) :
    padicValNat p (lvC (r := r) G j jp * degFact G j jp) ≤
      padicValNat p (∏ a, (dLvl G j jp a)!) + (G.T.t + 1) * L := by
  have hp' := hp.out
  rw [lvC_eq]
  by_cases h0 : (∏ a, fL G j jp a) * ((∏ i, binT (r := r) G j jp i) * binP (r := r) G jp) = 0
  · simp [h0, Nat.padicValNat_def]
  obtain ⟨hA, hB⟩ := mul_ne_zero_iff.mp h0
  obtain ⟨hBt, hBp⟩ := mul_ne_zero_iff.mp hB
  have hD : (∏ a, (dLvl G j jp a)!) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => Nat.factorial_ne_zero _
  rw [Nat.padicValNat_def, Nat.padicValNat_def,
    ← Nat.factorization_def _ hp', ← Nat.factorization_def _ hp', Nat.factorization_mul hA hB,
    Nat.factorization_mul hBt hBp]
  simp only [Finsupp.add_apply]
  have h1' : (∏ a, fL G j jp a).factorization p ≤ (∏ a, (dLvl G j jp a)!).factorization p :=
    (Nat.factorization_le_iff_dvd hA hD).mpr
      (Finset.prod_dvd_prod_of_dvd _ _ fun a _ => fL_dvd G j jp a) p
  have h2' : (∏ i, binT (r := r) G j jp i).factorization p ≤ G.T.t * L := by
    rw [Nat.factorization_prod (fun i _ => Finset.prod_ne_zero_iff.mp hBt i (Finset.mem_univ _))]
    rw [Finset.sum_apply']
    calc ∑ i, (binT (r := r) G j jp i).factorization p ≤ ∑ _i : Fin G.T.t, L :=
          Finset.sum_le_sum fun i _ => le_trans Nat.factorization_choose_le_log (h1 i)
      _ = G.T.t * L := by simp
  have h3' : (binP (r := r) G jp).factorization p ≤ L := le_trans Nat.factorization_choose_le_log h2
  rw [add_mul, one_mul]
  linarith

end Block

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestBCdimOfYbc
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.CountingStatementReduction

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

private theorem finrank_span_blockData_gens {p : ℕ} [Fact (Nat.Prime p)] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (ι : ℚ_[p] →+* KK O) {N r : ℕ} [NeZero r] (hY : RestYbc)
    (D : BlockData N) (j : Fin D.T.t → ℕ) (jp : ℕ) :
    Module.finrank (KK O) (Submodule.span (KK O) (BlockData.gens (r := r) O D j jp)) ≤
      Module.finrank ℤ_[p] (Ljj (r := r) p (gmB D) j jp) := by
  classical
  let W : Submodule ℚ_[p] (MvPolynomial (GM.M.BVar N r D.T.t) ℚ_[p]) :=
    Submodule.span ℚ_[p] (SetLike.coe (Ljj (r := r) p (gmB D) j jp))
  haveI hWfd : FiniteDimensional ℚ_[p] W := Ljj_span_fd (p := p) (r := r) (gmB D) j jp
  let Pk : MvPolynomial (BVar N r D.T.t) (KK O) :=
    ((∏ i : Fin D.T.t, BlockData.Ehat (r := r) O D i ^ j i) * BlockData.Eplus (r := r) O D ^ jp *
      ∏ i : Fin D.T.t, MvPolynomial.X (scalZ N r D.T.t i.castSucc) ^ D.T.z i) *
      MvPolynomial.X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus
  let mι : MvPolynomial (GM.M.BVar N r D.T.t) ℚ_[p] →+* MvPolynomial (BVar N r D.T.t) (KK O) :=
    MvPolynomial.map ι
  let fA : MvPolynomial (GM.M.BVar N r D.T.t) ℚ_[p] →+ MvPolynomial (BVar N r D.T.t) (KK O) :=
    (AddMonoidHom.mulLeft Pk).comp mι.toAddMonoidHom
  have hfA : ∀ u, fA u = Pk * mι u := fun u => rfl
  have hadd : ∀ u v, fA (u + v) = fA u + fA v := fun u v => map_add fA u v
  have hsmul : ∀ (c : ℚ_[p]) u, fA (c • u) = ι c • fA u := by
    intro c u
    rw [hfA, hfA, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul]
    simp only [mι, MvPolynomial.map_C]
    ring
  let T : Submodule (KK O) (MvPolynomial (BVar N r D.T.t) (KK O)) :=
    Submodule.span (KK O) (fA '' (W : Set _))
  have hT : Module.finrank (KK O) T ≤ Module.finrank ℚ_[p] W :=
    finrank_span_image_le ι fA hadd hsmul W
  let bW := Module.finBasis ℚ_[p] W
  have hTle : T ≤ Submodule.span (KK O) (Set.range fun i => fA (bW i : MvPolynomial _ ℚ_[p])) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w = ∑ i, (bW.repr ⟨w, hw⟩ i) • (bW i : MvPolynomial _ ℚ_[p]) := by
      have h1 : ((∑ i, (bW.repr ⟨w, hw⟩ i) • bW i : W) : MvPolynomial _ ℚ_[p]) = w := by
        rw [bW.sum_repr]
      refine h1.symm.trans ?_
      simp only [Submodule.coe_sum, Submodule.coe_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hw', map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : FiniteDimensional (KK O)
      (Submodule.span (KK O) (Set.range fun i => fA (bW i : MvPolynomial _ ℚ_[p]))) :=
    FiniteDimensional.span_of_finite (KK O) (Set.finite_range _)
  haveI : FiniteDimensional (KK O) T :=
    Submodule.finiteDimensional_of_le hTle
  have hbase : ∀ y0 ∈ GM.M.YZ (r := r) p ((gmB D).lettersAt j jp) D.T.J D.T.thr,
      ∀ g0 ∈ GM.M.XiPolZ p N r D.T.t (D.B - jp),
      Pk * rename (chainEmb N r D.T.t) (MvPolynomial.map ι y0) * MvPolynomial.map ι g0 ∈ T := by
    intro y0 hy0 g0 hg0
    have h1 : rename (GM.M.chainEmb N r D.T.t) y0 * g0 ∈ Ljj (r := r) p (gmB D) j jp := by
      unfold Ljj
      exact Submodule.subset_span ⟨y0, hy0, g0, hg0, rfl⟩
    have hmem : rename (GM.M.chainEmb N r D.T.t) y0 * g0 ∈ W := Submodule.subset_span h1
    have := Submodule.subset_span (R := KK O) (Set.mem_image_of_mem fA hmem)
    rw [hfA] at this
    simp only [mι, map_mul, MvPolynomial.map_rename] at this
    rw [← mul_assoc] at this
    exact this
  have hstep : ∀ a ∈ Submodule.span (KK O)
        (MvPolynomial.map ι '' (GM.M.YZ (r := r) p ((gmB D).lettersAt j jp) D.T.J D.T.thr : Set _)),
      ∀ c ∈ Submodule.span (KK O)
        (MvPolynomial.map ι '' (GM.M.XiPolZ p N r D.T.t (D.B - jp) : Set _)),
      Pk * rename (chainEmb N r D.T.t) a * c ∈ T := by
    intro a ha c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨g0, hg0, rfl⟩ := hc
      induction ha using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨y0, hy0, rfl⟩ := ha
        exact hbase y0 hy0 g0 hg0
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add (f := _), mul_add, add_mul]
        exact T.add_mem hx hy
      | smul k x _ hx =>
        rw [map_smul, mul_smul_comm, smul_mul_assoc]
        exact T.smul_mem k hx
    | zero => simp
    | add x y _ _ hx hy =>
      rw [mul_add]
      exact T.add_mem hx hy
    | smul k x _ hx =>
      rw [mul_smul_comm]
      exact T.smul_mem k hx
  have hgens : Submodule.span (KK O) (BlockData.gens (r := r) O D j jp) ≤ T := by
    rw [Submodule.span_le]
    rintro x ⟨y, hy, g, hg, rfl⟩
    exact hstep _ (hY O p ι N r (D.lettersAt j jp) D.T.q D.T.J D.T.thr y hy) g (xi_span ι g hg)
  calc Module.finrank (KK O) (Submodule.span (KK O) (BlockData.gens (r := r) O D j jp))
      ≤ Module.finrank (KK O) T :=
        LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hgens)
          (Submodule.inclusion_injective hgens)
    _ ≤ Module.finrank ℚ_[p] W := hT
    _ = Module.finrank ℤ_[p] (Ljj (r := r) p (gmB D) j jp) := (finrank_Ljj_span (gmB D) j jp).symm

theorem restBClvl_of (hY : RestYbc) : RestBClvl C0 CE1 CE2 X := by
  intro aTop _ aPlus _ b _ l _
  exact finrank_span_blockData_gens (O := X.O) (r := X.r) (iotaX X) hY
    (blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b) l.1 l.2

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestTMSizeOf
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}


variable (C0 CE1 CE2 X) in
def aTopPt (dl : DCl X) (a : Fin X.s → ℕ) : Fin X.s → ℕ :=
  ovr (uTop (X.S C0 CE1 CE2)) a (fun i => topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i))

theorem digits_of_idx {dl : DCl X} {a : Fin X.s → ℕ} {x : Σ _ : SegBlock X.s X.r, Lv C0 CE1 CE2 X}
    (hx : x ∈ idx C0 CE1 CE2 X dl a) :
    Kept X.p X.r (X.S C0 CE1 CE2) a x.1 ∧ (x.1.rz, x.1.ry) = dl ∧ x.2 ∈ lv C0 CE1 CE2 X a x.1 := by
  classical
  unfold idx at hx
  simp only [Finset.mem_sigma, Finset.mem_filter, mem_keptSet] at hx
  exact ⟨hx.1.1, hx.1.2, hx.2⟩

theorem Wl_ne {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl) (l : Fin X.s) :
    (Wl C0 CE1 CE2 X dl l).Nonempty := by
  have hbox := cbox_eq C0 CE1 CE2 X dl a ha
  have hW : a ∈ Fintype.piFinset (Wl C0 CE1 CE2 X dl) := hbox ▸ ha
  exact ⟨a l, Fintype.mem_piFinset.1 hW l⟩

theorem topA_mem_Wl {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl) (l : Fin X.s) :
    topA C0 CE1 CE2 X dl l ∈ Wl C0 CE1 CE2 X dl l := by
  obtain ⟨M, hM, hMe⟩ := Finset.exists_mem_eq_sup _ (Wl_ne ha l) (id : ℕ → ℕ)
  rw [topA_eq, hMe]
  exact hM

theorem aTopPt_mem {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl) :
    aTopPt C0 CE1 CE2 X dl a ∈ cbox C0 CE1 CE2 X dl := by
  have hbox := cbox_eq C0 CE1 CE2 X dl a ha
  have hW : a ∈ Fintype.piFinset (Wl C0 CE1 CE2 X dl) := hbox ▸ ha
  rw [hbox]
  exact ovr_mem _ (uTop_inj C0 CE1 CE2 X) _ a _ hW (Fintype.mem_piFinset.2 fun i => topA_mem_Wl ha _)

theorem setTies_top {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl)
    {x : Σ _ : SegBlock X.s X.r, Lv C0 CE1 CE2 X} (hx : x ∈ idx C0 CE1 CE2 X dl a) :
    (XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies (XMof C0 CE1 CE2 X dl a x.1 x.2).T
        (XMof C0 CE1 CE2 X dl a x.1 x.2).top = lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2 := by
  have hb : x.1.ry = dl.2 := congrArg Prod.snd (digits_of_idx hx).2.1
  have e1 := lLL_ovr C0 CE1 CE2 X a (fun i => topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)) x.1 x.2
  show (lLL C0 CE1 CE2 X a x.1 x.2).setTies (gT C0 CE1 CE2 X x.1) (XMof C0 CE1 CE2 X dl a x.1 x.2).top = _
  unfold aTopPt
  rw [e1]
  congr 1
  funext i
  rw [top_eq (dl := dl) a x.1 (x := x.2) (fun i => Wl_ne ha _) i]
  unfold cm
  rw [hb]

def RestSI : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ a ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl a,
    ∀ i, (XMof C0 CE1 CE2 X dl a x.1 x.2).T.S ((XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies
        (XMof C0 CE1 CE2 X dl a x.1 x.2).T (XMof C0 CE1 CE2 X dl a x.1 x.2).top) i ≤
      (XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i

theorem restTMSize_of (hS : SegFacts C0 CE1 CE2 X) (hFree : RestFree C0 CE1 CE2 X) (hSI : RestSI (C0 := C0) (CE1 := CE1)
    (CE2 := CE2) (X := X)) : RestTMSize C0 CE1 CE2 X := by
  intro dl hdl a ha x hx
  have ha' := aTopPt_mem ha
  have hx' : x ∈ idx C0 CE1 CE2 X dl (aTopPt C0 CE1 CE2 X dl a) := by
    rw [← hFree dl hdl a ha _ ha']; exact hx
  obtain ⟨hK', -, -⟩ := digits_of_idx hx'
  classical
  have hT' : aTopPt C0 CE1 CE2 X dl a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA) := by
    exact (Finset.mem_filter.mp ha').1
  have e := setTies_top ha hx
  refine ⟨hSI dl hdl a ha x hx, ?_, ?_, ?_, ?_⟩
  · intro y
    rw [e]
    exact lLL_deg_le hS _ hT' x.1 hK' x.2 y
  · intro i
    show coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) - x.1.o (uTop (X.S C0 CE1 CE2) i) ≤ 2 * X.L.a
    have h1 := coarseA_upper hS x.1 (uTop (X.S C0 CE1 CE2) i)
    have h2 := b_small hS
    have hP : (1 : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by exact_mod_cast hS.P1 _
    have h0 : (0 : ℝ) ≤ (coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) : ℝ) := Nat.cast_nonneg _
    have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
    have h3 : (coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤ 2 * X.L.a := by nlinarith
    have h4 : coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) ≤ 2 * X.L.a := by exact_mod_cast h3
    omega
  ·
    rw [e, Fin.sum_univ_castSucc]
    have hs : 2 * X.s + 2 ≤ X.r := hS.hF.s_le
    have hp : ((X.r : ℝ) + 1) ^ 2 ≤ (X.p : ℝ) := hS.hF.p_ge
    have hr5 := r5 hS
    have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
    have hp0 : (0 : ℝ) < (X.p : ℝ) := by nlinarith
    have hlast := lLL_deg_le hS _ hT' x.1 hK' x.2 (Fin.last (2 * X.s))
    have hone : ∀ q : Fin (2 * X.s),
        ((lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℝ) * X.p ≤ 2 * X.L.a := by
      intro q
      have hq : ((q.castSucc : Fin (2 * X.s + 1)) : ℕ) ≠ 2 * X.s := by
        have := q.2
        simp only [Fin.val_castSucc]
        omega
      have h1 := chain_wt hS _ hT' x.1 hK' q.castSucc hq
      have h2 : ((lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℝ) ≤
          ((segChain X.p (X.S C0 CE1 CE2) (aTopPt C0 CE1 CE2 X dl a) x.1).deg q.castSucc : ℝ) := by
        exact_mod_cast lLL_deg_le_chain hS _ x.1 x.2 q.castSucc
      have h3 : (X.p : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (topOf q.castSucc hq) : ℝ) := by
        exact_mod_cast p_le_P (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X) (topOf q.castSucc hq)
      calc ((lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℝ) * X.p
          ≤ ((segChain X.p (X.S C0 CE1 CE2) (aTopPt C0 CE1 CE2 X dl a) x.1).deg q.castSucc : ℝ) *
            ((X.S C0 CE1 CE2).P X.p (topOf q.castSucc hq) : ℝ) :=
            mul_le_mul h2 h3 hp0.le (Nat.cast_nonneg _)
        _ ≤ 2 * X.L.a := h1
    have hsum : ((∑ q : Fin (2 * X.s), (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℕ) : ℝ) *
        X.p ≤ (2 * X.s : ℕ) * (2 * X.L.a) := by
      rw [Nat.cast_sum, Finset.sum_mul]
      calc ∑ q : Fin (2 * X.s), ((lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℝ) * X.p
          ≤ ∑ _q : Fin (2 * X.s), 2 * (X.L.a : ℝ) := Finset.sum_le_sum fun q _ => hone q
        _ = (2 * X.s : ℕ) * (2 * X.L.a) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsp : ((2 * X.s : ℕ) : ℝ) ≤ X.p := by
      have h1 : ((2 * X.s : ℕ) : ℝ) ≤ (X.r : ℝ) := by exact_mod_cast (by omega : 2 * X.s ≤ X.r)
      nlinarith
    have hsum2 : ((∑ q : Fin (2 * X.s), (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℕ) : ℝ) ≤
        2 * X.L.a := by
      have h1 : ((2 * X.s : ℕ) : ℝ) * (2 * X.L.a) ≤ (2 * X.L.a) * X.p := by nlinarith
      exact le_of_mul_le_mul_right (hsum.trans h1) hp0
    have hsum3 : (∑ q : Fin (2 * X.s), (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc) ≤
        2 * X.L.a := by exact_mod_cast hsum2
    exact (Nat.add_le_add hsum3 hlast).trans (by omega)
  · exact_mod_cast hS.hF.a1

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

