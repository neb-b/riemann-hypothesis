module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.JTranslate
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.Rodier GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.CellA

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {h N : ℕ} {d : Fin h → ℕ} {hd : ∑ a, d a = N} {W : Type} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (Levi k fun a => Fin (d a)) W}

theorem J_translate (ψ : AddChar k Circle) (J : openFns d hd ρ →ₗ[ℂ] W) (vol : Subgroup (GL (Fin N) k) → ℝ)
    (hV : ∀ L₀ : Subgroup (GL (Fin N) k), L₀ ≤ unipU k d hd → IsCompact (L₀ : Set (GL (Fin N) k)) →
      (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀) →
      0 < vol L₀ ∧ ∀ (f : openFns d hd ρ) (v : W),
        (∀ (u : GL (Fin N) k) (hb : u ∈ unipB k (Fin N)), u ∈ L₀ →
          f.1.1.1 (pm k (wOpen d hd) * u) = (whitChar ψ N ⟨u, hb⟩ : ℂ) • v) →
        (∀ u ∈ unipU k d hd, u ∉ L₀ → f.1.1.1 (pm k (wOpen d hd) * u) = 0) → J f = (vol L₀ : ℂ) • v)
    (L₀ : Subgroup (GL (Fin N) k)) (hL₀U : L₀ ≤ unipU k d hd) (hc : IsCompact (L₀ : Set (GL (Fin N) k)))
    (hO : ∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀)
    (hθ : ∀ (l : GL (Fin N) k) (hl : l ∈ unipB k (Fin N)), l ∈ L₀ → whitChar ψ N ⟨l, hl⟩ = 1)
    (F : IndSp (stdBlocks d hd) ρ) (hF : F ∈ openFns d hd ρ) (v : W)
    (hF1 : ∀ u ∈ L₀, F.1.1 (pm k (wOpen d hd) * u) = v)
    (hF0 : ∀ u ∈ unipU k d hd, u ∉ L₀ → F.1.1 (pm k (wOpen d hd) * u) = 0)
    (a : GL (Fin N) k) (l : Levi k fun a => Fin (d a))
    (hl : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) l)
    (haB : ∀ u ∈ unipB k (Fin N), a * u * a⁻¹ ∈ unipB k (Fin N))
    (haU : ∀ u ∈ unipU k d hd, a * u * a⁻¹ ∈ unipU k d hd)
    (haU' : ∀ u ∈ unipU k d hd, a⁻¹ * u * a ∈ unipU k d hd)
    (hstab : ∀ u ∈ L₀, a * u * a⁻¹ ∈ L₀) :
    (J ⟨F, hF⟩ = (vol L₀ : ℂ) • v) ∧
    ∃ hm : parInd (stdBlocks d hd) ρ a F ∈ openFns d hd ρ,
      J ⟨parInd (stdBlocks d hd) ρ a F, hm⟩ = (vol (L₀.map (MulAut.conj a).toMonoidHom) : ℂ) •
        ((deltaHalf k (fun a => Fin (d a)) l : ℂ) • ρ l v) := by
  have hcont : Continuous fun g : GL (Fin N) k => a * g * a⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hmem1 : ∀ x : GL (Fin N) k, x ∈ L₀.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ L₀ := by
    intro x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : a⁻¹ * ((MulAut.conj a).toMonoidHom y) * a = y := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [hy']
      exact hy
    · intro hx
      refine ⟨_, hx, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hback : ∀ x : GL (Fin N) k, x = a * (a⁻¹ * x * a) * a⁻¹ := fun x => by group
  refine ⟨?_, PositivityTheory.RgUd.CellA.translate_mem_openFns d hd ρ a l hl haB hF, ?_⟩
  · refine (hV L₀ hL₀U hc hO).2 ⟨F, hF⟩ v ?_ hF0
    intro u hb hu
    rw [hθ u hb hu]
    simpa using hF1 u hu
  · have hL₁U : L₀.map (MulAut.conj a).toMonoidHom ≤ unipU k d hd := by
      intro x hx
      rw [hmem1] at hx
      rw [hback x]
      exact haU _ (hL₀U hx)
    have hL₁c : IsCompact ((L₀.map (MulAut.conj a).toMonoidHom : Subgroup (GL (Fin N) k)) :
        Set (GL (Fin N) k)) := by
      rw [Subgroup.coe_map]
      exact hc.image hcont
    have hL₁O : ∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) =
        (L₀.map (MulAut.conj a).toMonoidHom : Subgroup (GL (Fin N) k)) := by
      obtain ⟨O, hOo, hOeq⟩ := hO
      have hc2 : Continuous fun g : GL (Fin N) k => a⁻¹ * g * a :=
        (continuous_const.mul continuous_id).mul continuous_const
      refine ⟨(fun g : GL (Fin N) k => a⁻¹ * g * a) ⁻¹' O, hOo.preimage hc2, ?_⟩
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
      rw [hmem1]
      constructor
      · rintro ⟨hxO, hxU⟩
        have : a⁻¹ * x * a ∈ O ∩ (unipU k d hd : Set (GL (Fin N) k)) := ⟨hxO, haU' x hxU⟩
        rw [hOeq] at this
        exact this
      · intro hx
        have hx' : a⁻¹ * x * a ∈ O ∩ (unipU k d hd : Set (GL (Fin N) k)) := by
          rw [hOeq]
          exact hx
        refine ⟨hx'.1, ?_⟩
        rw [hback x]
        exact haU _ hx'.2
    refine (hV _ hL₁U hL₁c hL₁O).2 _ _ ?_ ?_
    · intro u hb hu
      have hu0 : a⁻¹ * u * a ∈ L₀ := (hmem1 u).1 hu
      have huL₀ : u ∈ L₀ := by
        rw [hback u]
        exact hstab _ hu0
      have key : ((parInd (stdBlocks d hd) ρ a) F).1.1 (pm k (wOpen d hd) * u) =
          (deltaHalf k (fun a => Fin (d a)) l : ℂ) • ρ l v := by
        rw [PositivityTheory.RgUd.CellA.translate_apply d hd ρ a l hl F u, hF1 _ hu0]
      rw [hθ u hb huL₀]
      simpa using key
    · intro u hu hnot
      show ((parInd (stdBlocks d hd) ρ a) F).1.1 (pm k (wOpen d hd) * u) = 0
      rw [PositivityTheory.RgUd.CellA.translate_apply d hd ρ a l hl F u]
      have hn : a⁻¹ * u * a ∉ L₀ := fun h => hnot ((hmem1 u).2 h)
      rw [hF0 _ (haU' u hu) hn, map_zero, smul_zero]

end PositivityTheory.RgUd.CellA
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.MemUnipUTwo
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.Rodier

namespace PositivityTheory.RgUd.CellA

variable {r m : ℕ}

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem wConj_apply (u : GL (Fin (r + m)) k) (i j : Fin (r + m)) :
    ((pm k (wOpen (dd r m) (hdd r m)) * u * (pm k (wOpen (dd r m) (hdd r m)))⁻¹ : GL (Fin (r + m)) k) :
      Matrix (Fin (r + m)) (Fin (r + m)) k) i j =
      (u : Matrix (Fin (r + m)) (Fin (r + m)) k) ((w2 r m).symm i) ((w2 r m).symm j) := by
  rw [wOpen_two, ← map_inv, Units.val_mul, Units.val_mul, GroundTheory.Automorphic.mul_permGL_apply,
    GroundTheory.Automorphic.permGL_mul_apply]
  rfl


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mem_unipU_two {u : GL (Fin (r + m)) k} :
    u ∈ unipU k (dd r m) (hdd r m) ↔ u ∈ unipB k (Fin (r + m)) ∧ ∀ i j : Fin (r + m),
      (u : Matrix (Fin (r + m)) (Fin (r + m)) k) i j ≠ (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) i j →
        (i : ℕ) < m ∧ m ≤ (j : ℕ) := by
  set e := stdBlocks (dd r m) (hdd r m) with he
  have hblk : ∀ (a : Fin 2) (i' : Fin (dd r m a)), ((w2 r m).symm (e ⟨a, i'⟩) : ℕ) < m ↔ a = 1 := by
    intro a i'
    have := weyl_shuffle_symm_lt_iff (r := r) (m := m) (e ⟨a, i'⟩)
    rwa [blk_apply] at this
  have hone : ∀ (a b : Fin 2) (i' : Fin (dd r m a)) (j' : Fin (dd r m b)),
      (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) ((w2 r m).symm (e ⟨a, i'⟩)) ((w2 r m).symm (e ⟨b, j'⟩)) =
        if (⟨a, i'⟩ : Σ c, Fin (dd r m c)) = ⟨b, j'⟩ then 1 else 0 := by
    intro a b i' j'
    rw [Matrix.one_apply]
    by_cases h : (⟨a, i'⟩ : Σ c, Fin (dd r m c)) = ⟨b, j'⟩
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun h' => h (e.injective ((w2 r m).symm.injective h')))]
  constructor
  · intro hu
    refine ⟨hu.1, fun p q hpq => ?_⟩
    have h2 : pm k (wOpen (dd r m) (hdd r m)) * u * (pm k (wOpen (dd r m) (hdd r m)))⁻¹ ∈
        unipRadLower k e := hu.2
    obtain ⟨hP, hD⟩ := (mem_unipRadLower k).1 h2
    obtain ⟨⟨a, i'⟩, hi⟩ := e.surjective (w2 r m p)
    obtain ⟨⟨b, j'⟩, hj⟩ := e.surjective (w2 r m q)
    have hp : p = (w2 r m).symm (e ⟨a, i'⟩) := by rw [hi, Equiv.symm_apply_apply]
    have hq : q = (w2 r m).symm (e ⟨b, j'⟩) := by rw [hj, Equiv.symm_apply_apply]
    have hpa := hblk a i'
    have hqb := hblk b j'
    rw [← hp] at hpa
    rw [← hq] at hqb
    rcases lt_trichotomy a b with hab | rfl | hab
    · exfalso
      have h3 := (mem_parabLower_iff k).1 hP a b i' j' hab
      rw [wConj_apply, ← hp, ← hq] at h3
      apply hpq
      rw [h3, hp, hq, hone, if_neg (fun h => hab.ne (congrArg Sigma.fst h))]
    · exfalso
      have h3 := hD a i' j'
      rw [wConj_apply, ← hp, ← hq] at h3
      apply hpq
      rw [h3, hp, hq, hone, Matrix.one_apply]
      by_cases h : i' = j'
      · rw [if_pos h, if_pos (by rw [h])]
      · rw [if_neg h, if_neg (fun h' => h (by simpa using h'))]
    · have ha : a = 1 := by fin_cases a <;> fin_cases b <;> simp_all
      have hb : b = 0 := by fin_cases a <;> fin_cases b <;> simp_all
      refine ⟨hpa.2 ha, ?_⟩
      by_contra hq'
      push_neg at hq'
      exact absurd (hqb.1 hq') (by rw [hb]; decide)
  · rintro ⟨hB, hc⟩
    refine ⟨hB, ?_⟩
    show pm k (wOpen (dd r m) (hdd r m)) * u * (pm k (wOpen (dd r m) (hdd r m)))⁻¹ ∈ unipRadLower k e
    refine (mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 fun a b i' j' hab => ?_, fun a i' j' => ?_⟩
    · rw [wConj_apply]
      have ha : a = 0 := by fin_cases a <;> fin_cases b <;> simp_all
      have hb : b = 1 := by fin_cases a <;> fin_cases b <;> simp_all
      by_contra hne
      have h1 := hc _ _ (by
        rw [hone, if_neg (fun h => hab.ne (congrArg Sigma.fst h))]
        exact hne)
      have h2 := (hblk a i').1 h1.1
      rw [ha] at h2
      exact absurd h2 (by decide)
    · rw [wConj_apply]
      have hpq : (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) ((w2 r m).symm (e ⟨a, i'⟩)) ((w2 r m).symm (e ⟨a, j'⟩)) =
          (1 : Matrix (Fin (dd r m a)) (Fin (dd r m a)) k) i' j' := by
        rw [hone, Matrix.one_apply]
        by_cases h' : i' = j'
        · subst h'
          simp
        · rw [if_neg (fun h => h' (by simpa using h)), if_neg h']
      rw [← hpq]
      by_contra hne
      obtain ⟨h1, h2⟩ := hc _ _ hne
      exact absurd ((hblk a j').2 ((hblk a i').1 h1)) (not_lt.2 h2)

end PositivityTheory.RgUd.CellA
end
end

