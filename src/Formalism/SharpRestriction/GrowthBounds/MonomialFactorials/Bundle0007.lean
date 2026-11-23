module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0004
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0005
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0002

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.DimYOvr
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Fibre

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)


open Classical in
def Wl (dl : DCl X) (l : Fin X.s) : Finset ℕ :=
  X.winA.filter fun x => ∑ c, dl.2 l c ≤ x ∧ (X.S C0 CE1 CE2).P X.p l ∣ x - ∑ c, dl.2 l c

theorem topA_eq (dl : DCl X) (l : Fin X.s) : topA C0 CE1 CE2 X dl l = (Wl C0 CE1 CE2 X dl l).sup id := rfl

private theorem mem_Wl_iff_mem_winA_and_dvd_sub (dl : DCl X) (l : Fin X.s) (v : ℕ) :
    v ∈ Wl C0 CE1 CE2 X dl l ↔
      v ∈ X.winA ∧ (∑ c, dl.2 l c ≤ v ∧ (X.S C0 CE1 CE2).P X.p l ∣ v - ∑ c, dl.2 l c) := by
  unfold Wl
  rw [Finset.mem_filter]

private theorem mem_cbox_iff_mem_piFinset_and_compat (dl : DCl X) (a : Fin X.s → ℕ) :
    a ∈ cbox C0 CE1 CE2 X dl ↔ a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA) ∧ Compat C0 CE1 CE2 X dl a := by
  classical
  unfold cbox
  simp only [Finset.mem_filter]

theorem cbox_eq (dl : DCl X) (a0 : Fin X.s → ℕ) (h0 : a0 ∈ cbox C0 CE1 CE2 X dl) :
    cbox C0 CE1 CE2 X dl = Fintype.piFinset (Wl C0 CE1 CE2 X dl) := by
  have h0' := ((mem_cbox_iff_mem_piFinset_and_compat C0 CE1 CE2 X dl a0).1 h0).2
  simp only [Compat, DigitsOK, ColumnSystems.digitBlock] at h0'
  ext a
  rw [mem_cbox_iff_mem_piFinset_and_compat, Fintype.mem_piFinset, Fintype.mem_piFinset]
  simp only [Compat, DigitsOK, ColumnSystems.digitBlock, mem_Wl_iff_mem_winA_and_dvd_sub]
  constructor
  · rintro ⟨ha, -, -, h3⟩ i
    exact ⟨ha i, h3 i⟩
  · intro h
    exact ⟨fun i => (h i).1, h0'.1, h0'.2.1, fun i => (h i).2⟩

def cm (dl : DCl X) (x : Lv C0 CE1 CE2 X) (i : Fin (X.S C0 CE1 CE2).t) (v : ℕ) : ℕ :=
  (v - ∑ c, dl.2 (uTop (X.S C0 CE1 CE2) i) c) / (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) - x.1 i

def Nl (dl : DCl X) (x : Lv C0 CE1 CE2 X) (i : Fin (X.S C0 CE1 CE2).t) : Finset ℕ :=
  (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).image (cm C0 CE1 CE2 X dl x i)

theorem twoPow_pos (l : Fin X.s) : 0 < (X.S C0 CE1 CE2).P X.p l := by
  unfold SegData.P
  exact pow_pos X.std.1.prime.pos _

def LvlRoom (dl : DCl X) (x : Lv C0 CE1 CE2 X) : Prop :=
  ∀ i, ∀ v ∈ Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i),
    x.1 i ≤ (v - ∑ c, dl.2 (uTop (X.S C0 CE1 CE2) i) c) / (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i)

variable {C0 CE1 CE2 X}

theorem cm_inj {dl : DCl X} {x : Lv C0 CE1 CE2 X} (hr : LvlRoom C0 CE1 CE2 X dl x) (i : Fin (X.S C0 CE1 CE2).t) :
    Set.InjOn (cm C0 CE1 CE2 X dl x i) (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)) := by
  intro v hv v' hv' he
  have r1 := hr i v hv
  have r2 := hr i v' hv'
  simp only [Finset.mem_coe, mem_Wl_iff_mem_winA_and_dvd_sub] at hv hv'
  simp only [cm] at he
  have hPp := twoPow_pos C0 CE1 CE2 X (uTop (X.S C0 CE1 CE2) i)
  obtain ⟨k, hk⟩ := hv.2.2
  obtain ⟨k', hk'⟩ := hv'.2.2
  rw [hk, Nat.mul_div_cancel_left _ hPp] at r1
  rw [hk, Nat.mul_div_cancel_left _ hPp] at he
  rw [hk', Nat.mul_div_cancel_left _ hPp] at r2
  rw [hk', Nat.mul_div_cancel_left _ hPp] at he
  have hkk : k = k' := by omega
  subst hkk
  omega

theorem cm_mono (dl : DCl X) (x : Lv C0 CE1 CE2 X) (i : Fin (X.S C0 CE1 CE2).t) {v v' : ℕ} (h : v ≤ v') :
    cm C0 CE1 CE2 X dl x i v ≤ cm C0 CE1 CE2 X dl x i v' := by
  unfold cm
  exact Nat.sub_le_sub_right (Nat.div_le_div_right (Nat.sub_le_sub_right h _)) _

theorem Nl_conv {dl : DCl X} {x : Lv C0 CE1 CE2 X} (hr : LvlRoom C0 CE1 CE2 X dl x) (i : Fin (X.S C0 CE1 CE2).t) :
    ∀ y ∈ Nl C0 CE1 CE2 X dl x i, ∀ y' ∈ Nl C0 CE1 CE2 X dl x i, ∀ z, y ≤ z → z ≤ y' → z ∈ Nl C0 CE1 CE2 X dl x i := by
  intro y hy y' hy' z hyz hzy'
  simp only [Nl, Finset.mem_image] at hy hy' ⊢
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨v', hv', rfl⟩ := hy'
  have r1 := hr i v hv
  have r2 := hr i v' hv'
  simp only [mem_Wl_iff_mem_winA_and_dvd_sub, Formalism.MainNotions.flipOneThree.Inst.winA, Finset.mem_Icc] at hv hv' ⊢
  simp only [cm] at hyz hzy' ⊢
  have hPp := twoPow_pos C0 CE1 CE2 X (uTop (X.S C0 CE1 CE2) i)
  obtain ⟨k, hk⟩ := hv.2.2
  obtain ⟨k', hk'⟩ := hv'.2.2
  rw [hk, Nat.mul_div_cancel_left _ hPp] at r1
  rw [hk, Nat.mul_div_cancel_left _ hPp] at hyz
  rw [hk', Nat.mul_div_cancel_left _ hPp] at r2
  rw [hk', Nat.mul_div_cancel_left _ hPp] at hzy'
  have hle1 : k ≤ z + x.1 i := by omega
  have hle2 : z + x.1 i ≤ k' := by omega
  have m1 := Nat.mul_le_mul_left ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i)) hle1
  have m2 := Nat.mul_le_mul_left ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i)) hle2
  refine ⟨(∑ c, dl.2 (uTop (X.S C0 CE1 CE2) i) c) + (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) * (z + x.1 i), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · omega
  · omega
  · omega
  · exact ⟨z + x.1 i, by omega⟩
  · rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hPp, Nat.add_sub_cancel]

theorem cm_top {dl : DCl X} (x : Lv C0 CE1 CE2 X) (i : Fin (X.S C0 CE1 CE2).t)
    (hne : (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).Nonempty) :
    cm C0 CE1 CE2 X dl x i (topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)) = (Nl C0 CE1 CE2 X dl x i).sup id := by
  rw [topA_eq]
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image _ id hne
  have hsup : (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).sup id = m :=
    le_antisymm (Finset.sup_le fun v hv => hmax v hv) (Finset.le_sup (f := id) hm)
  rw [hsup]
  apply le_antisymm
  · exact Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hm)
  · apply Finset.sup_le
    intro y hy
    simp only [Nl, Finset.mem_image] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    exact cm_mono dl x i (hmax v hv)

variable (C0 CE1 CE2 X)

def XMof (dl : DCl X) (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) : flipOneThree.InstM where
  p := X.p
  hp := X.std.1.prime
  s := X.s
  r := X.r
  hr := X.hm
  LL := lLL C0 CE1 CE2 X a b x
  T := gT C0 CE1 CE2 X b
  a := X.L.a
  E := X.L.Y * kapS X
  Yl := fun i => (Nl C0 CE1 CE2 X dl x i).sup id - sInf ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ) + 1
  n₀ := fun i => sInf ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ)
  dd := fun _ => 1
  ρ := ⟨X.r - 1, Nat.sub_lt (Nat.pos_of_ne_zero X.hm) one_pos⟩

def BADf (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) (D : ℤ) (n : Fin (X.S C0 CE1 CE2).t → ℕ) : ℕ :=
  Formalism.GM.M.bad X.p (fun F G => Formalism.GM.M.fockN X.p ((lLL C0 CE1 CE2 X a b x).setTies (gT C0 CE1 CE2 X b) n)
            ((gT C0 CE1 CE2 X b).phis X.p (r := X.r) ((lLL C0 CE1 CE2 X a b x).setTies (gT C0 CE1 CE2 X b) n) F) G)
    (Formalism.GM.M.YZ X.p (r := X.r) ((lLL C0 CE1 CE2 X a b x).setTies (gT C0 CE1 CE2 X b) n) (gT C0 CE1 CE2 X b).J
      (gT C0 CE1 CE2 X b).thr) D

def FRf (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) (n : Fin (X.S C0 CE1 CE2).t → ℕ) : ℕ :=
  Module.finrank ℚ_[X.p] (Formalism.GM.M.Y X.p (r := X.r) ((lLL C0 CE1 CE2 X a b x).setTies (gT C0 CE1 CE2 X b) n)
    (gT C0 CE1 CE2 X b).J (gT C0 CE1 CE2 X b).thr)

theorem bY_ovr (dl : DCl X) (a : Fin X.s → ℕ) (n : Fin (X.S C0 CE1 CE2).t → ℕ) (b : SegBlock X.s X.r)
    (hb : b.ry = dl.2) (x : Lv C0 CE1 CE2 X) (D : ℤ) :
    bY C0 CE1 CE2 X (ovr (uTop (X.S C0 CE1 CE2)) a n) b x D =
      BADf C0 CE1 CE2 X a b x D (fun i => cm C0 CE1 CE2 X dl x i (n i)) := by
  have h := lLL_ovr C0 CE1 CE2 X a n b x
  have hf : (fun i => cm C0 CE1 CE2 X dl x i (n i)) = (fun i : Fin (X.S C0 CE1 CE2).t =>
      (n i - ∑ c, b.ry (uTop (X.S C0 CE1 CE2) i) c) / (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) - x.1 i) := by
    funext i
    simp only [cm, hb]
  unfold BADf bY badY
  rw [hf, ← h]
  rfl

theorem dimY_ovr (dl : DCl X) (a : Fin X.s → ℕ) (n : Fin (X.S C0 CE1 CE2).t → ℕ) (b : SegBlock X.s X.r)
    (hb : b.ry = dl.2) (x : Lv C0 CE1 CE2 X) :
    dimY X.p (r := X.r) (gB C0 CE1 CE2 X (ovr (uTop (X.S C0 CE1 CE2)) a n) 0 b) x.1 x.2 =
      FRf C0 CE1 CE2 X a b x (fun i => cm C0 CE1 CE2 X dl x i (n i)) := by
  have h := lLL_ovr C0 CE1 CE2 X a n b x
  have hf : (fun i => cm C0 CE1 CE2 X dl x i (n i)) = (fun i : Fin (X.S C0 CE1 CE2).t =>
      (n i - ∑ c, b.ry (uTop (X.S C0 CE1 CE2) i) c) / (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) - x.1 i) := by
    funext i
    simp only [cm, hb]
  unfold FRf dimY
  rw [hf, ← h]
  rfl

end Fibre

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.MemIntPolIff
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.CountingStatementReduction

section Gens

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {ι : ℚ_[p] →+* KK O} {N r : ℕ} [NeZero r]

theorem map_Ehat (D : BlockData N) (i : Fin (gmB D).T.t) :
    map ι ((gmB D).Ehat p (r := r) i) = D.Ehat O (r := r) i := by
  unfold Formalism.GM.M.BlockData.Ehat Formalism.MainNotions.G.BlockData.Ehat
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_mul, map_X, map_sum]
  rfl

theorem map_Eplus (D : BlockData N) :
    map ι ((gmB D).Eplus p (r := r)) = D.Eplus O (r := r) := by
  unfold Formalism.GM.M.BlockData.Eplus Formalism.MainNotions.G.BlockData.Eplus
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_mul, map_X, map_sum]
  rfl

theorem map_gens (hint : ∀ x : ℤ_[p], ∃ y : O, ι (x : ℚ_[p]) = algebraMap O (KK O) y) (D : BlockData N)
    (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (Formalism.GM.M.BVar N r (gmB D).T.t) ℚ_[p])
    (hx : x ∈ (gmB D).gens p (r := r) j jp) : map ι x ∈ D.gens O (r := r) j jp := by
  obtain ⟨y, hy, g, hg, rfl⟩ := hx
  refine ⟨map ι y, map_YZ hint (D.lettersAt j jp) D.T.J D.T.thr y hy, map ι g, map_XiPolZ hint g hg, ?_⟩
  simp only [map_mul, map_prod, map_pow, map_X, map_Ehat, map_Eplus, map_rename]
  rfl

theorem map_smul_Q {σ : Type} (c : ℚ_[p]) (x : MvPolynomial σ ℚ_[p]) : map ι (c • x) = ι c • map ι x := by
  rw [smul_eq_C_mul, map_mul, map_C, smul_eq_C_mul]

theorem map_SSZ (hint : ∀ x : ℤ_[p], ∃ y : O, ι (x : ℚ_[p]) = algebraMap O (KK O) y) (D : BlockData N)
    (x : MvPolynomial (Formalism.GM.M.BVar N r (gmB D).T.t) ℚ_[p]) (hx : x ∈ (gmB D).SSZ p (r := r)) :
    map ι x ∈ Submodule.span (KK O) (D.SSZ O (r := r) : Set (MvPolynomial (BVar N r D.T.t) (KK O))) := by
  unfold Formalism.GM.M.BlockData.SSZ at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    simp only [Set.mem_iUnion] at hx
    obtain ⟨j, jp, hok, hx⟩ := hx
    have hm : MvPolynomial.map ι x ∈ D.gens O (r := r) j jp := map_gens hint D j jp x hx
    exact Submodule.subset_span (Submodule.subset_span
      (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨jp, Set.mem_iUnion.2 ⟨hok, hm⟩⟩⟩))
  | zero =>
    rw [map_zero]
    exact zero_mem _
  | add a b _ _ ha hb =>
    rw [map_add (f := _)]
    exact add_mem ha hb
  | smul a x _ hx =>
    rw [← algebraMap_smul ℚ_[p] a x, map_smul_Q]
    exact Submodule.smul_mem _ _ hx

abbrev intMap (σ : Type) : MvPolynomial σ ℤ_[p] →ₐ[ℤ_[p]] MvPolynomial σ ℚ_[p] :=
  MvPolynomial.mapAlgHom (Algebra.ofId ℤ_[p] ℚ_[p])

theorem mem_intPol_iff {σ : Type} (F : MvPolynomial σ ℚ_[p]) :
    F ∈ Formalism.GM.M.IntPol p σ ↔ F ∈ (intMap (p := p) σ).range := Iff.rfl

private theorem X_mem_intMap {σ : Type} (v : σ) :
    (X v : MvPolynomial σ ℚ_[p]) ∈ (intMap (p := p) σ).range :=
  ⟨X v, by simp⟩

theorem gens_int (D : Formalism.GM.M.BlockData N) (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (Formalism.GM.M.BVar N r D.T.t) ℚ_[p])
    (hx : x ∈ D.gens p (r := r) j jp) : x ∈ Formalism.GM.M.IntPol p (Formalism.GM.M.BVar N r D.T.t) := by
  obtain ⟨y, hy, g, hg, rfl⟩ := hx
  rw [mem_intPol_iff]
  rw [Formalism.GM.M.YZ] at hy
  rw [Formalism.GM.M.XiPolZ] at hg
  have h1 : y ∈ Formalism.GM.M.PolZ p r (D.lettersAt j jp) := (Submodule.mem_inf.1 hy).2
  rw [Formalism.GM.M.PolZ] at h1
  have h2 : y ∈ Formalism.GM.M.IntPol p (Fin N × Fin r) := (Submodule.mem_inf.1 h1).2
  have hE : ∀ i, D.Ehat p (r := r) i ∈ (intMap (p := p) (Formalism.GM.M.BVar N r D.T.t)).range := by
    intro i
    unfold Formalism.GM.M.BlockData.Ehat
    exact add_mem (mul_mem (X_mem_intMap _) (X_mem_intMap _))
      (sum_mem fun c _ => mul_mem (X_mem_intMap _) (X_mem_intMap _))
  have hP : D.Eplus p (r := r) ∈ (intMap (p := p) (Formalism.GM.M.BVar N r D.T.t)).range := by
    unfold Formalism.GM.M.BlockData.Eplus
    exact add_mem (mul_mem (X_mem_intMap _) (X_mem_intMap _))
      (sum_mem fun c _ => mul_mem (X_mem_intMap _) (X_mem_intMap _))
  have hy' : rename (Formalism.GM.M.chainEmb N r D.T.t) y ∈ (intMap (p := p) (Formalism.GM.M.BVar N r D.T.t)).range := by
    obtain ⟨G, rfl⟩ := (mem_intPol_iff y).1 h2
    exact ⟨rename (Formalism.GM.M.chainEmb N r D.T.t) G, by simp [map_rename]⟩
  have hg' : g ∈ (intMap (p := p) (Formalism.GM.M.BVar N r D.T.t)).range :=
    (mem_intPol_iff g).1 (Submodule.mem_inf.1 hg).2
  refine mul_mem (mul_mem (mul_mem ?_ (pow_mem (X_mem_intMap _) _)) hy') hg'
  exact mul_mem (mul_mem (prod_mem fun i _ => pow_mem (hE i) _) (pow_mem hP _))
    (prod_mem fun i _ => pow_mem (X_mem_intMap _) _)

theorem SSZ_int (D : Formalism.GM.M.BlockData N) (x : MvPolynomial (Formalism.GM.M.BVar N r D.T.t) ℚ_[p])
    (hx : x ∈ D.SSZ p (r := r)) : x ∈ Formalism.GM.M.IntPol p (Formalism.GM.M.BVar N r D.T.t) := by
  unfold Formalism.GM.M.BlockData.SSZ at hx
  refine (Submodule.span_le.2 ?_) hx
  intro z hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨j, jp, -, hz⟩ := hz
  exact gens_int D j jp z hz

end Gens

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

