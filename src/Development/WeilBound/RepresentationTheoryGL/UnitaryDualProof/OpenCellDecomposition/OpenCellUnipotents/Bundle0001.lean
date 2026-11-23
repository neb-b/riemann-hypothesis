module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.LevZZero

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.BlockIndexOfWeylShuffle
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.Rodier

namespace PositivityTheory.RgUd.CellA

variable {r m : ℕ}

theorem blk_two (i : Fin (r + m)) :
    blk (stdBlocks (dd r m) (hdd r m)) i = if (i : ℕ) < r then 0 else 1 := by
  obtain ⟨⟨a, j⟩, rfl⟩ := (stdBlocks (dd r m) (hdd r m)).surjective i
  rw [blk_apply, stdBlocks_val]
  have hj := j.2
  fin_cases a
  · simp at hj ⊢
    simp [hj]
  · simp at hj ⊢


variable (r m) in
def w2 : Equiv.Perm (Fin (r + m)) := (finCongr (add_comm r m)).trans finAddFlip

theorem weyl_shuffle_val (j : Fin (r + m)) : (w2 r m j : ℕ) = if (j : ℕ) < m then r + j else j - m := by
  obtain ⟨j, hj⟩ := j
  unfold w2
  rw [Equiv.trans_apply]
  simp only [Fin.val_mk]
  split_ifs with h
  · rw [show (finCongr (add_comm r m) ⟨j, hj⟩ : Fin (m + r)) = ⟨j, by omega⟩ from rfl,
      finAddFlip_apply_mk_left h]
  · rw [show (finCongr (add_comm r m) ⟨j, hj⟩ : Fin (m + r)) = ⟨j, by omega⟩ from rfl,
      finAddFlip_apply_mk_right (by omega) (by omega)]

theorem block_index_of_weyl_shuffle (j : Fin (r + m)) :
    blk (stdBlocks (dd r m) (hdd r m)) (w2 r m j) = if (j : ℕ) < m then 1 else 0 := by
  rw [blk_two, weyl_shuffle_val]
  have := j.2
  split_ifs <;> omega

theorem wOpen_two : wOpen (dd r m) (hdd r m) = w2 r m := by
  symm
  rw [wOpen, Tuple.eq_sort_iff]
  refine ⟨fun i j hij => ?_, fun i j hij he => ?_⟩
  · simp only [Function.comp_apply, wKey]
    rw [Prod.Lex.toLex_le_toLex]
    simp only [block_index_of_weyl_shuffle, OrderDual.toDual_lt_toDual, Fin.le_iff_val_le_val, weyl_shuffle_val]
    have hij' : (i : ℕ) ≤ j := hij
    by_cases hi : (i : ℕ) < m <;> by_cases hj : (j : ℕ) < m
    · simp [hi, hj, hij']
    · left; simp [hi, hj]
    · omega
    · simp [hi, hj]; omega
  · have h2 := congrArg (fun p => (ofLex p).2) he
    simp only [wKey, ofLex_toLex] at h2
    exact le_of_eq h2

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem weyl_shuffle_symm_lt_iff (i : Fin (r + m)) :
    ((w2 r m).symm i : ℕ) < m ↔ blk (stdBlocks (dd r m) (hdd r m)) i = 1 := by
  have h := block_index_of_weyl_shuffle ((w2 r m).symm i)
  rw [Equiv.apply_symm_apply] at h
  rw [h]
  split_ifs with hh <;> simp [hh]

theorem aDiag_inv (N n : ℕ) (z : kˣ) : (aDiag k N n z)⁻¹ = aDiag k N n z⁻¹ :=
  Units.ext rfl

theorem aDiag_conj_apply (N n : ℕ) (z : kˣ) (u : GL (Fin N) k) (i j : Fin N) :
    ((aDiag k N n z * u * (aDiag k N n z)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
      (if (i : ℕ) < n then (z : k) else 1) * (u : Matrix (Fin N) (Fin N) k) i j *
        (if (j : ℕ) < n then ((z⁻¹ : kˣ) : k) else 1) := by
  rw [aDiag_inv, Units.val_mul, Units.val_mul]
  show (diagonal (fun i : Fin N => if (i : ℕ) < n then (z : k) else 1) * (u : Matrix (Fin N) (Fin N) k) *
    diagonal (fun i : Fin N => if (i : ℕ) < n then ((z⁻¹ : kˣ) : k) else 1)) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem aDiag_conj_mem_unipB (N n : ℕ) (z : kˣ) {u : GL (Fin N) k} (hu : u ∈ unipB k (Fin N)) :
    aDiag k N n z * u * (aDiag k N n z)⁻¹ ∈ unipB k (Fin N) := by
  obtain ⟨h1, h2⟩ := (mem_unipB k).1 hu
  refine (mem_unipB k).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [aDiag_conj_apply, h1 i j hij, mul_zero, zero_mul]
  · rw [aDiag_conj_apply, h2 i, mul_one]
    split_ifs
    · exact Units.mul_inv z
    · exact one_mul 1


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem levZ_apply (z : kˣ) (a : Fin 2) (i j : Fin (dd r m a)) :
    ((levZ k r m z a : GL (Fin (dd r m a)) k) : Matrix (Fin (dd r m a)) (Fin (dd r m a)) k) i j =
      if i = j then (if a = 0 then 1 else (z : k)) else 0 := by
  unfold levZ
  split_ifs <;> simp_all [Matrix.one_apply, Matrix.scalar_apply, Matrix.diagonal_apply]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem conj_aDiag (z : kˣ) :
    pm k (wOpen (dd r m) (hdd r m)) * aDiag k (r + m) m z * (pm k (wOpen (dd r m) (hdd r m)))⁻¹ =
      leviEmb k (stdBlocks (dd r m) (hdd r m)) (levZ k r m z) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [wOpen_two, ← map_inv, Units.val_mul, Units.val_mul, GroundTheory.Automorphic.mul_permGL_apply,
    GroundTheory.Automorphic.permGL_mul_apply]
  show diagonal (fun i : Fin (r + m) => if (i : ℕ) < m then (z : k) else 1) _ _ = _
  rw [Matrix.diagonal_apply]
  obtain ⟨⟨a, i'⟩, rfl⟩ := (stdBlocks (dd r m) (hdd r m)).surjective i
  obtain ⟨⟨b, j'⟩, rfl⟩ := (stdBlocks (dd r m) (hdd r m)).surjective j
  have key := weyl_shuffle_symm_lt_iff (r := r) (m := m) ((stdBlocks (dd r m) (hdd r m)) ⟨a, i'⟩)
  rw [blk_apply] at key
  rw [show (w2 r m)⁻¹ = (w2 r m).symm from rfl]
  by_cases hab : a = b
  · subst hab
    have he : ((leviEmb k (stdBlocks (dd r m) (hdd r m)) (levZ k r m z) : GL (Fin (r + m)) k) : Matrix _ _ k)
        ((stdBlocks (dd r m) (hdd r m)) ⟨a, i'⟩) ((stdBlocks (dd r m) (hdd r m)) ⟨a, j'⟩) =
        ((levZ k r m z a : GL _ k) : Matrix _ _ k) i' j' := by
      simp [leviEmb, Matrix.blockDiagonal'_apply_eq]
    rw [he, levZ_apply]
    by_cases hij : i' = j'
    · subst hij
      rw [if_pos rfl, if_pos rfl]
      have h01 : a = 0 ∨ a = 1 := by fin_cases a <;> simp
      rcases h01 with rfl | rfl
      · rw [if_neg (fun h => absurd (key.1 h) (by decide)), if_pos rfl]
      · rw [if_pos (key.2 rfl), if_neg (by decide)]
    · rw [if_neg (fun h => hij (by simpa using (w2 r m).symm.injective h)), if_neg hij]
  · have he : ((leviEmb k (stdBlocks (dd r m) (hdd r m)) (levZ k r m z) : GL (Fin (r + m)) k) : Matrix _ _ k)
        ((stdBlocks (dd r m) (hdd r m)) ⟨a, i'⟩) ((stdBlocks (dd r m) (hdd r m)) ⟨b, j'⟩) = 0 := by
      simp [leviEmb, Matrix.blockDiagonal'_apply, hab]
    rw [he, if_neg]
    intro h
    have := (stdBlocks (dd r m) (hdd r m)).injective ((w2 r m).symm.injective h)
    exact hab (congrArg Sigma.fst this)

theorem aDiag_conj_mem_unipU (z : kˣ) {u : GL (Fin (r + m)) k} (hu : u ∈ unipU k (dd r m) (hdd r m)) :
    aDiag k (r + m) m z * u * (aDiag k (r + m) m z)⁻¹ ∈ unipU k (dd r m) (hdd r m) := by
  refine ⟨aDiag_conj_mem_unipB k _ _ z hu.1, ?_⟩
  have h2 : pm k (wOpen (dd r m) (hdd r m)) * u * (pm k (wOpen (dd r m) (hdd r m)))⁻¹ ∈
      unipRadLower k (stdBlocks (dd r m) (hdd r m)) := hu.2
  have hN : leviEmb k (stdBlocks (dd r m) (hdd r m)) (levZ k r m z) ∈
      Subgroup.normalizer (unipRadLower k (stdBlocks (dd r m) (hdd r m)) : Set _) := by
    apply parab_le_normalizer k (opp (stdBlocks (dd r m) (hdd r m)))
    apply (mem_parabLower_iff k).2
    intro a b i j hab
    simp [leviEmb, Matrix.blockDiagonal'_apply, hab.ne]
  have h3 := (Subgroup.mem_normalizer_iff.1 hN _).1 h2
  rw [← conj_aDiag] at h3
  show pm k (wOpen (dd r m) (hdd r m)) * (aDiag k (r + m) m z * u * (aDiag k (r + m) m z)⁻¹) *
    (pm k (wOpen (dd r m) (hdd r m)))⁻¹ ∈ unipRadLower k (stdBlocks (dd r m) (hdd r m))
  convert h3 using 1
  group


open ValuativeRel GroundTheory.Automorphic.GLnLocal in
theorem aDiag_conj_apply_unipB (N n : ℕ) (z : kˣ) {u : GL (Fin N) k} (hu : u ∈ unipB k (Fin N)) (i j : Fin N) :
    ((aDiag k N n z * u * (aDiag k N n z)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
      (if (i : ℕ) < n ∧ ¬ (j : ℕ) < n then (z : k) else 1) * (u : Matrix (Fin N) (Fin N) k) i j := by
  rw [aDiag_conj_apply]
  have hz : (z : k) * ((z⁻¹ : kˣ) : k) = 1 := Units.mul_inv z
  by_cases hi : (i : ℕ) < n <;> by_cases hj : (j : ℕ) < n
  · simp only [hi, hj, if_true, not_true, and_false, if_false, one_mul]
    rw [mul_comm, ← mul_assoc, mul_comm _ (z : k), hz, one_mul]
  · simp [hi, hj]
  · have hji : j < i := by rw [Fin.lt_iff_val_lt_val]; omega
    rw [((mem_unipB k).1 hu).1 i j hji]
    simp
  · simp [hi, hj]


open ValuativeRel GroundTheory.Automorphic.GLnLocal in
theorem aDiag_conj_mem_congr (N n : ℕ) (z : kˣ) (hz : valuation k (z : k) ≤ 1) (c : ℕ) {u : GL (Fin N) k}
    (hu : u ∈ unipB k (Fin N)) (hK : u ∈ congruenceSubgroup k N c) :
    aDiag k N n z * u * (aDiag k N n z)⁻¹ ∈ congruenceSubgroup k N c := by
  have hc : ∀ i j : Fin N, valuation k (if (i : ℕ) < n ∧ ¬ (j : ℕ) < n then (z : k) else 1) ≤ 1 := by
    intro i j
    split_ifs
    · exact hz
    · simp
  have hc1 : ∀ i : Fin N, (if (i : ℕ) < n ∧ ¬ (i : ℕ) < n then (z : k) else 1) = 1 := fun i => by simp
  obtain ⟨hI, hcong⟩ := (mem_congruenceSubgroup_iff k N).1 hK
  obtain ⟨hI1, hI2⟩ := (mem_integralGL_iff k N).1 hI
  have hu' : u⁻¹ ∈ unipB k (Fin N) := inv_mem hu
  refine (mem_congruenceSubgroup_iff k N).2 ⟨(mem_integralGL_iff k N).2 ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · rw [aDiag_conj_apply_unipB k N n z hu]
    have := hI1 i j
    rw [Valuation.mem_integer_iff] at this ⊢
    rw [map_mul]
    exact mul_le_one' (hc i j) this
  · have e : (aDiag k N n z * u * (aDiag k N n z)⁻¹)⁻¹ = aDiag k N n z * u⁻¹ * (aDiag k N n z)⁻¹ := by group
    rw [e, aDiag_conj_apply_unipB k N n z hu']
    have := hI2 i j
    rw [Valuation.mem_integer_iff] at this ⊢
    rw [map_mul]
    exact mul_le_one' (hc i j) this
  · rw [aDiag_conj_apply_unipB k N n z hu]
    have e : (if (i : ℕ) < n ∧ ¬ (j : ℕ) < n then (z : k) else 1) * (u : Matrix (Fin N) (Fin N) k) i j -
        (1 : Matrix (Fin N) (Fin N) k) i j = (if (i : ℕ) < n ∧ ¬ (j : ℕ) < n then (z : k) else 1) *
        ((u : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) := by
      by_cases hij : i = j
      · subst hij
        rw [hc1, one_mul, one_mul]
      · rw [Matrix.one_apply_ne hij, sub_zero, sub_zero]
    rw [e, map_mul]
    first
      | exact (mul_le_of_le_one_left' (hc i j)).trans (hcong i j)
      | exact (mul_le_of_le_one_left₀ (zero_le _) (hc i j)).trans (hcong i j)

end PositivityTheory.RgUd.CellA
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.Translate
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.Rodier GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.CellA

section General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W)

theorem translate_apply (a : GL (Fin N) k) (l : Levi k fun a => Fin (d a))
    (hl : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) l)
    (f : IndSp (stdBlocks d hd) ρ) (u : GL (Fin N) k) :
    (parInd (stdBlocks d hd) ρ a f).1.1 (pm k (wOpen d hd) * u) =
      (deltaHalf k (fun a => Fin (d a)) l : ℂ) • ρ l (f.1.1 (pm k (wOpen d hd) * (a⁻¹ * u * a))) := by
  letI : DecidableEq (Fin h) := Classical.typeDecidableEq _
  have hx : pm k (wOpen d hd) * u * a =
      leviEmb k (stdBlocks d hd) l * (pm k (wOpen d hd) * (a⁻¹ * u * a)) := by
    rw [← hl]
    group
  have hm : leviEmb k (stdBlocks d hd) l ∈ parab k (stdBlocks d hd) :=
    mem_parab_iff.2 fun _ _ i j hab => by
      simp [leviEmb]
      exact Matrix.blockDiagonal'_apply_ne _ _ _ hab.ne'
  have hp : leviProj k (stdBlocks d hd) ⟨leviEmb k (stdBlocks d hd) l, hm⟩ = l := by
    funext a
    ext i j
    simp [leviProj_apply, leviEmb, Matrix.blockDiagonal'_apply_eq]
  have hf := f.1.2 ⟨leviEmb k (stdBlocks d hd) l, hm⟩ (pm k (wOpen d hd) * (a⁻¹ * u * a))
  change f.1.1 (pm k (wOpen d hd) * u * a) = _
  rw [hx]
  refine hf.trans ?_
  rw [MonoidHom.comp_apply, hp]
  rfl

theorem translate_mem_openFns (a : GL (Fin N) k) (l : Levi k fun a => Fin (d a))
    (hl : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) l)
    (haB : ∀ u ∈ unipB k (Fin N), a * u * a⁻¹ ∈ unipB k (Fin N))
    {f : IndSp (stdBlocks d hd) ρ} (hf : f ∈ openFns d hd ρ) :
    parInd (stdBlocks d hd) ρ a f ∈ openFns d hd ρ := by
  letI : DecidableEq (Fin h) := Classical.typeDecidableEq _
  have hf' : ∀ g : GL (Fin N) k, f.1.1 g ≠ 0 → g ∈ cell k d hd (wOpen d hd) := hf
  show ∀ g : GL (Fin N) k, (parInd (stdBlocks d hd) ρ a f).1.1 g ≠ 0 → g ∈ cell k d hd (wOpen d hd)
  intro g hg
  obtain ⟨p, hp, n, hn, hpn⟩ := hf' (g * a) hg
  have hm : leviEmb k (stdBlocks d hd) l ∈ parab k (stdBlocks d hd) :=
    mem_parab_iff.2 fun _ _ i j hab => by
      simp [leviEmb]
      exact Matrix.blockDiagonal'_apply_ne _ _ _ hab.ne'
  refine ⟨p * (leviEmb k (stdBlocks d hd) l)⁻¹,
    (parab k _).mul_mem hp ((parab k _).inv_mem hm), a * n * a⁻¹, haB n hn, ?_⟩
  have hg' : g = p * pm k (wOpen d hd) * n * a⁻¹ := by
    rw [← hpn]
    group
  rw [hg', ← hl]
  group

end General

section Two

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem modExp_two_one (r m : ℕ) : modExp (fun a => Fin (dd r m a)) 1 = -(r : ℤ) := by
  simp [modExp, Finset.sum_filter, Fin.sum_univ_two, dd]

theorem nabs_pow (z : kˣ) (n : ℕ) : nabs k (z ^ n) = nabs k z ^ n := by
  simp [nabs, map_pow]

theorem deltaHalf_levZ (r m : ℕ) (z : kˣ) :
    (deltaHalf k (fun a => Fin (dd r m a)) (levZ k r m z) : ℂ) =
      ((nabs k z ^ (-((m * r : ℕ) : ℝ) / 2) : ℝ) : ℂ) := by
  have h0 : levZ k r m z 0 = 1 := by simp [levZ] <;> rfl
  have h1 : levZ k r m z 1 = GeneralLinearGroup.scalar (Fin (dd r m 1)) z := by simp [levZ]
  have hdet : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin (dd r m 1)) z) = z ^ m := by
    rw [GeneralLinearGroup.det_scalar]
    simp [dd]
  have key : (deltaHalf k (fun a => Fin (dd r m a)) (levZ k r m z) : ℂ) =
      ((nabs k (GeneralLinearGroup.det (levZ k r m z 0)) : ℂ) ^ ((modExp (fun a => Fin (dd r m a)) 0 : ℂ) / 2)) *
      ((nabs k (GeneralLinearGroup.det (levZ k r m z 1)) : ℂ) ^ ((modExp (fun a => Fin (dd r m a)) 1 : ℂ) / 2)) := by
    simp only [deltaHalf, Fin.prod_univ_two]
    rfl
  rw [key, h0, h1, hdet, map_one, modExp_two_one, nabs_pow]
  have hx : 0 ≤ nabs k z := by simp [nabs]
  have hn1 : nabs k 1 = 1 := by simp [nabs]
  rw [hn1]
  simp only [Complex.ofReal_one, Complex.one_cpow, one_mul]
  have hexp : (((-(r : ℤ) : ℤ) : ℂ) / 2) = (((-(r : ℝ)) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hexp, ← Complex.ofReal_cpow (pow_nonneg hx m), ← Real.rpow_natCast_mul hx]
  congr 2
  push_cast
  ring

end Two

end PositivityTheory.RgUd.CellA
end
end

