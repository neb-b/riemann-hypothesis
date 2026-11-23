module

public import Mathlib
public import Formalism.MirabolicMackeyTheory.Bundle0001

@[expose] public section

-- bundled from Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Mirabolic
section
open Matrix

namespace Formalism.EigenvalueLevelCeiling

variable {k : Type} [Field k] {n : ℕ}

theorem exists_gl_of_isUniU (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hM : IsUniU M) :
    ∃ g : GL (Fin (n + 1)) k, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = M := by
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_upperTriangular (by intro i j hij; exact hM.2 i j hij)]
    simp [hM.1]
  exact ⟨Matrix.nonsingInvUnit M (by rw [hdet]; exact isUnit_one), rfl⟩

def pairU (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  1 + t • vecMulVec (fun a => h a l.castSucc) (Pi.single s.succ 1)

def pairV (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  1 + t • vecMulVec (Pi.single l.castSucc 1) (fun b => h s.succ b)

theorem pairU_apply (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) (a b) :
    pairU h s l t a b = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b +
      t * (h a l.castSucc * if b = s.succ then 1 else 0) := by
  simp [pairU, Matrix.vecMulVec_apply, Pi.single_apply]

theorem pairV_apply (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) (a b) :
    pairV h s l t a b = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b +
      t * ((if a = l.castSucc then 1 else 0) * h s.succ b) := by
  simp [pairV, Matrix.vecMulVec_apply, Pi.single_apply]

theorem pair_comm (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) :
    pairU h s l t * h = h * pairV h s l t := by
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [pairU_apply, pairV_apply, add_mul, mul_add, Finset.sum_add_distrib]
  have e1 : ∑ c, (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a c * h c b = h a b := by
    simp [Matrix.one_apply]
  have e2 : ∑ c, h a c * (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) c b = h a b := by
    simp [Matrix.one_apply]
  rw [e1, e2]
  simp [mul_ite, ite_mul]
  ring

theorem pairU_isUniU (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (hl : l ≤ s)
    (hg : ∀ j, s.castSucc < j → ∀ b, b < j → h j b = 0) (t : k) : IsUniU (pairU h s l t) := by
  have hls : l.castSucc < s.succ :=
    lt_of_le_of_lt (Fin.castSucc_le_castSucc_iff.2 hl) ((Fin.castSucc_lt_succ : s.castSucc < s.succ))
  have hsl : h s.succ l.castSucc = 0 := hg s.succ ((Fin.castSucc_lt_succ : s.castSucc < s.succ)) l.castSucc hls
  refine ⟨fun i => ?_, fun i j hji => ?_⟩
  · rw [pairU_apply, Matrix.one_apply_eq]
    by_cases hi : i = s.succ
    · subst hi
      rw [hsl]
      ring
    · rw [if_neg hi]
      ring
  · rw [pairU_apply, Matrix.one_apply_ne hji.ne']
    by_cases hj : j = s.succ
    · subst hj
      rw [hg i (lt_trans ((Fin.castSucc_lt_succ : s.castSucc < s.succ)) hji) l.castSucc (lt_trans hls hji)]
      ring
    · rw [if_neg hj]
      ring

theorem pairV_isUniU (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (hl : l ≤ s)
    (hg : ∀ j, s.castSucc < j → ∀ b, b < j → h j b = 0) (t : k) : IsUniU (pairV h s l t) := by
  have hls : l.castSucc < s.succ :=
    lt_of_le_of_lt (Fin.castSucc_le_castSucc_iff.2 hl) ((Fin.castSucc_lt_succ : s.castSucc < s.succ))
  have hsl : h s.succ l.castSucc = 0 := hg s.succ ((Fin.castSucc_lt_succ : s.castSucc < s.succ)) l.castSucc hls
  refine ⟨fun i => ?_, fun i j hji => ?_⟩
  · rw [pairV_apply, Matrix.one_apply_eq]
    by_cases hi : i = l.castSucc
    · subst hi
      rw [hsl]
      ring
    · rw [if_neg hi]
      ring
  · rw [pairV_apply, Matrix.one_apply_ne hji.ne']
    by_cases hi : i = l.castSucc
    · subst hi
      rw [hg s.succ ((Fin.castSucc_lt_succ : s.castSucc < s.succ)) j (lt_trans hji hls)]
      ring
    · rw [if_neg hi]
      ring

theorem one_castSucc_succ (a : Fin n) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a.castSucc a.succ = 0 :=
  Matrix.one_apply_ne ((Fin.castSucc_lt_succ : a.castSucc < a.succ)).ne

theorem supd_pairU (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) :
    supd (pairU h s l t) = t * h s.castSucc l.castSucc := by
  simp [supd, pairU_apply, one_castSucc_succ, Fin.succ_inj]

theorem supd_pairV (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) :
    supd (pairV h s l t) = t * h s.succ l.succ := by
  simp [supd, pairV_apply, one_castSucc_succ, Fin.castSucc_inj]

theorem exists_bad (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hm : IsMirab h) (hu : ¬ IsUniU h) :
    ∃ s l : Fin n, l ≤ s ∧ (∀ j, s.castSucc < j → h j j = 1 ∧ ∀ b, b < j → h j b = 0) ∧
      h s.castSucc l.castSucc ≠ if l = s then 1 else 0 := by
  classical
  have hlast : h (Fin.last n) (Fin.last n) = 1 ∧ ∀ b, b < Fin.last n → h (Fin.last n) b = 0 :=
    ⟨by rw [hm]; simp, fun b hb => by rw [hm, if_neg hb.ne]⟩
  have hex : ∃ j, ¬ (h j j = 1 ∧ ∀ b, b < j → h j b = 0) := by
    by_contra hno
    push_neg at hno
    exact hu ⟨fun i => (hno i).1, fun i j hji => (hno i).2 j hji⟩
  obtain ⟨j1, hj1⟩ := hex
  let S := Finset.univ.filter fun j => ¬ (h j j = 1 ∧ ∀ b, b < j → h j b = 0)
  have hSne : S.Nonempty := ⟨j1, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj1⟩⟩
  set j0 := S.max' hSne with hj0def
  have hj0 : ¬ (h j0 j0 = 1 ∧ ∀ b, b < j0 → h j0 b = 0) := (Finset.mem_filter.1 (S.max'_mem hSne)).2
  have hgood : ∀ j, j0 < j → h j j = 1 ∧ ∀ b, b < j → h j b = 0 := by
    intro j hj
    by_contra hb
    exact absurd (S.le_max' j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩)) (not_le.2 hj)
  have hne : j0 ≠ Fin.last n := fun he => hj0 (he ▸ hlast)
  set s := j0.castPred hne with hsdef
  have hs : s.castSucc = j0 := Fin.castSucc_castPred j0 hne
  have hgood' : ∀ j, s.castSucc < j → h j j = 1 ∧ ∀ b, b < j → h j b = 0 := by
    rw [hs]
    exact hgood
  by_cases hd : h j0 j0 = 1
  · have hb : ∃ b, b < j0 ∧ h j0 b ≠ 0 := by
      by_contra hno
      push_neg at hno
      exact hj0 ⟨hd, hno⟩
    obtain ⟨b, hb0, hbne⟩ := hb
    have hbl : b ≠ Fin.last n := (lt_of_lt_of_le hb0 (Fin.le_last _)).ne
    refine ⟨s, b.castPred hbl, ?_, hgood', ?_⟩
    · rw [← Fin.castSucc_le_castSucc_iff, Fin.castSucc_castPred, hs]
      exact hb0.le
    · have hlt : b.castPred hbl ≠ s := by
        intro he
        have := congrArg Fin.castSucc he
        rw [Fin.castSucc_castPred, hs] at this
        exact hb0.ne this
      rw [if_neg hlt]
      simpa [Fin.castSucc_castPred, hs] using hbne
  · refine ⟨s, s, le_rfl, hgood', ?_⟩
    rw [if_pos rfl]
    simpa [hs] using hd

theorem mirabolic_mackey_pair : MirabolicMackey := by
  intro k A _ _ _ n ψ hψ h hm hu
  obtain ⟨s, l, hl, hgood, hbad⟩ := exists_bad (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) hm hu
  have hg : ∀ j, s.castSucc < j → ∀ b, b < j → (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) j b = 0 :=
    fun j hj b hb => (hgood j hj).2 b hb
  have hrow : (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s.succ l.succ = if l = s then 1 else 0 := by
    by_cases hls : l = s
    · subst hls
      rw [if_pos rfl]
      exact (hgood _ (Fin.castSucc_lt_succ : l.castSucc < l.succ)).1
    · rw [if_neg hls]
      exact (hgood _ (Fin.castSucc_lt_succ : s.castSucc < s.succ)).2 _
        (Fin.succ_lt_succ_iff.2 (lt_of_le_of_ne hl hls))
  obtain ⟨c, hc⟩ : ∃ c : k,
      c = (if l = s then 1 else 0) - (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s.castSucc l.castSucc :=
    ⟨_, rfl⟩
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact sub_ne_zero.2 (Ne.symm hbad)
  obtain ⟨x, hx⟩ : ∃ x, ψ x ≠ 1 := by
    by_contra hno
    push_neg at hno
    exact hψ (AddChar.ext ψ 1 fun y => by rw [hno y, AddChar.one_apply])
  obtain ⟨t, ht⟩ : ∃ t : k, t = x / c := ⟨_, rfl⟩
  have htc : t * c = x := by rw [ht]; field_simp
  obtain ⟨g, hgM⟩ := exists_gl_of_isUniU _ (pairU_isUniU (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s l hl hg t)
  have hconj : ((h⁻¹ * g * h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      pairV (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s l t := by
    rw [Units.val_mul, Units.val_mul, hgM, mul_assoc, pair_comm, ← mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, one_mul]
  refine ⟨g, by rw [hgM]; exact pairU_isUniU _ s l hl hg t, by rw [hconj]; exact pairV_isUniU _ s l hl hg t, ?_⟩
  rw [hconj, hgM, supd_pairV, supd_pairU, hrow]
  intro heq
  apply hx
  have e : t * (if l = s then (1 : k) else 0) =
      t * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s.castSucc l.castSucc + x := by
    linear_combination htc - t * hc
  rw [e, AddChar.map_add_eq_mul] at heq
  obtain ⟨v, hv⟩ : IsUnit (ψ (t * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s.castSucc l.castSucc)) :=
    IsUnit.of_mul_eq_one (ψ (-(t * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s.castSucc l.castSucc)))
      (by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one])
  rw [← hv] at heq
  calc ψ x = ↑v⁻¹ * (↑v * ψ x) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = ↑v⁻¹ * ↑v := by rw [heq]
    _ = 1 := Units.inv_mul v

theorem supd_one : supd (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = 0 := by
  simp [supd, one_castSucc_succ]

theorem supd_mul (u u' : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hu : IsUniU u) (hu' : IsUniU u') :
    supd (u * u') = supd u + supd u' := by
  unfold supd
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply, Fintype.sum_eq_add i.castSucc i.succ ((Fin.castSucc_lt_succ : i.castSucc < i.succ)).ne]
  · rw [hu.1, hu'.1]
    ring
  · rintro c ⟨hc1, hc2⟩
    rcases lt_or_gt_of_ne hc1 with h1 | h1
    · rw [hu.2 _ _ h1, zero_mul]
    · have h2 : (c : ℕ) ≠ (i : ℕ) + 1 := fun h3 => hc2 (Fin.ext (by simp [h3]))
      have h4 : i.succ < c := by
        rw [Fin.lt_iff_val_lt_val] at h1 ⊢
        simp only [Fin.coe_castSucc, Fin.val_succ] at h1 ⊢
        omega
      rw [hu'.2 _ _ h4, mul_zero]

theorem isMirab_of_isUniU (u : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hu : IsUniU u) : IsMirab u := by
  intro j
  by_cases hj : j = Fin.last n
  · subst hj
    rw [if_pos rfl]
    exact hu.1 _
  · rw [if_neg hj]
    exact hu.2 _ _ (Fin.lt_last_iff_ne_last.2 hj)

theorem mirabolic_is_mackey : MirabolicIsMackey := by
  intro k A _ _ _ n ψ hψ P U hP hU
  refine ⟨?_, ?_, ?_⟩
  · show ψ (supd ((1 : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) = 1
    rw [Units.val_one, supd_one, AddChar.map_zero_eq_one]
  · intro u hu u' hu'
    show ψ (supd (((u * u' : P) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) =
      ψ (supd ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) *
        ψ (supd ((u' : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
    rw [Subgroup.coe_mul, Units.val_mul, supd_mul _ _ ((hU u).1 hu) ((hU u').1 hu'),
      AddChar.map_add_eq_mul]
  · intro h hh
    have hm : IsMirab ((h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := (hP h).1 h.2
    have hnu : ¬ IsUniU ((h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
      fun hu => hh ((hU h).2 hu)
    obtain ⟨u, hu1, hu2, hne⟩ := mirabolic_mackey_pair k A n ψ hψ (h : GL (Fin (n + 1)) k) hm hnu
    have huP : u ∈ P := (hP u).2 (isMirab_of_isUniU _ hu1)
    refine ⟨⟨u, huP⟩, (hU _).2 hu1, (hU _).2 ?_, ?_⟩
    · simpa using hu2
    · simpa using hne

end Formalism.EigenvalueLevelCeiling
end

-- bundled from Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.OnLocal
section
open Module NumberField IsDedekindDomain

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

theorem onLocal_of (hMono : IdxMono) (hCut : IdxCutLe) (hTr : IdxTransport) (hInt : LatInter)
    (h3 : ThreeForms) (hPG : IdxPsiGood) (hGG : LemmaGG) : OnLocal := by
  unfold OnLocal
  intro K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk V₀ e he hrange M Th ThK Th0 X₃ X₄ hM hTh hThK
    hThM hTh0fg hTh0 hMst hThst σ hσ hThσ hucut a E r ha hE hW hT0 hX3 hX4 hX34 ε hε d φ hφ
    hφr Mj Tj hMj hTj
  have hr : (lix w M (M ⊓ sc a⁻¹ Th) : ℝ) ≤ r :=
    (h3 K Z w M Th hM hTh hThM a E r ha hE).mp hW
  have hNl : IsLatIn ⊤ (M ⊓ sc a⁻¹ Th) := hInt K Z M Th hM hTh a⁻¹ (inv_ne_zero ha)

  have hNst : ∀ g : P, (M ⊓ sc a⁻¹ Th).map ((ρ g).restrictScalars (𝓞 K)) ≤ M ⊓ sc a⁻¹ Th := by
    intro g x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨hyM, hyT⟩ := Submodule.mem_inf.mp hy
    refine Submodule.mem_inf.mpr ⟨hMst g (Submodule.mem_map_of_mem hyM), ?_⟩
    unfold sc at hyT ⊢
    obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.mp hyT
    refine Submodule.mem_map.mpr ⟨(ρ g) t, hThst g (Submodule.mem_map_of_mem ht), ?_⟩
    simp
  have hcard : Nat.card U ≠ 0 := Nat.card_pos.ne'
  have hidx : 0 < U.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hG := hGG K Z w P ρ U ψ hMk M (M ⊓ sc a⁻¹ Th) hM hNl inf_le_left hMst hNst
  obtain ⟨hTl, hbound⟩ := hPG K Z w (eig ρ U ψ) V₀ M Th ThK Th0 hM hTh hThK hThM hTh0fg hTh0
    σ hσ hThσ (Nat.card U) hcard hucut a E r ha hE hr U.index hidx hG
  have hXl : IsLatIn (eig ρ U ψ ⊓ V₀) (cut (eig ρ U ψ ⊓ V₀) M) :=
    (hCut K Z w ⊤ (eig ρ U ψ ⊓ V₀) M M hM hM le_rfl le_top).1

  have hcutle : cut V₀ Th0 ≤ Th0.map (e.restrictScalars (𝓞 K)) := by
    intro x hx
    simp only [cut, Submodule.mem_inf, Submodule.restrictScalars_mem] at hx
    obtain ⟨hx0, hxV⟩ := hx
    rw [← hrange] at hxV
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hxV
    refine Submodule.mem_map.mpr ⟨e y, hx0, ?_⟩
    show e (e y) = e y
    rw [← LinearMap.comp_apply, he]
  have h1 := hMono K Z w (eig ρ U ψ ⊓ V₀) (cut (eig ρ U ψ ⊓ V₀) M) X₃ X₄ hXl hX3 hX4 hX34
  have h2 := hMono K Z w (eig ρ U ψ ⊓ V₀) (cut (eig ρ U ψ ⊓ V₀) M) (cut V₀ Th0)
    (Th0.map (e.restrictScalars (𝓞 K))) hXl hTl hT0 hcutle
  have htr := hTr K Z w d φ hφ Mj Tj
  rw [hMj, hTj] at htr
  have hdim : finrank K (eig ρ U ψ ⊓ V₀ : Submodule K Z) = d := by
    rw [← hφr, LinearMap.finrank_range_of_inj hφ, Module.finrank_fin_fun]
  rw [hdim] at hbound
  rw [← htr]
  have h1' : (lix w (cut (eig ρ U ψ ⊓ V₀) M) X₄ : ℝ) ≤ lix w (cut (eig ρ U ψ ⊓ V₀) M) X₃ := by
    exact_mod_cast h1
  have h2' : (lix w (cut (eig ρ U ψ ⊓ V₀) M) (Th0.map (e.restrictScalars (𝓞 K))) : ℝ) ≤
      lix w (cut (eig ρ U ψ ⊓ V₀) M) (cut V₀ Th0) := by
    exact_mod_cast h2
  linarith

theorem mackey_product : MackeyProd := by
  unfold MackeyProd
  intro ι A _ _ _ P _ U ψ hψ
  unfold IsMackey
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.prod_eq_one fun v _ => (hψ v).1
  · intro u hu u' hu'
    dsimp only
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hu1 : ∀ v ∈ (Set.univ : Set ι), u v ∈ U v := hu
    have hu2 : ∀ v ∈ (Set.univ : Set ι), u' v ∈ U v := hu'
    exact (hψ v).2.1 _ (hu1 v (Set.mem_univ v)) _ (hu2 v (Set.mem_univ v))
  · intro h hh
    have hex : ∃ v0, h v0 ∉ U v0 := by
      by_contra hc
      push_neg at hc
      apply hh
      show ∀ v ∈ (Set.univ : Set ι), h v ∈ U v
      exact fun v _ => hc v
    obtain ⟨v0, hv0⟩ := hex
    obtain ⟨u0, hu0, hc, hne⟩ := (hψ v0).2.2 (h v0) hv0
    refine ⟨Pi.mulSingle v0 u0, ?_, ?_, ?_⟩
    · show ∀ v ∈ (Set.univ : Set ι), Pi.mulSingle v0 u0 v ∈ U v
      intro v _
      by_cases hv : v = v0
      · subst hv
        simpa using hu0
      · simp [Pi.mulSingle_eq_of_ne hv]
    · show ∀ v ∈ (Set.univ : Set ι), (h⁻¹ * Pi.mulSingle v0 u0 * h) v ∈ U v
      intro v _
      by_cases hv : v = v0
      · subst hv
        simpa using hc
      · simp [Pi.mulSingle_eq_of_ne hv]
    · show ∏ v, ψ v ((h⁻¹ * Pi.mulSingle v0 u0 * h) v) ≠ ∏ v, ψ v (Pi.mulSingle v0 u0 v)
      rw [Fintype.prod_eq_single v0 (fun v hv => by simp [Pi.mulSingle_eq_of_ne hv, (hψ v).1]),
        Fintype.prod_eq_single v0 (fun v hv => by simp [Pi.mulSingle_eq_of_ne hv, (hψ v).1])]
      simpa using hne

end Formalism.EigenvalueLevelCeiling
end

-- bundled from Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.OrthogonalityOfMackey
section
open Module NumberField IsDedekindDomain

namespace Formalism.EigenvalueLevelCeiling

theorem orthogonality_of_mackey : OrthOfMackey := by
  unfold OrthOfMackey
  intro K _ _ _ Z _ _ P _ _ ρ U _ ψ hM h hh z hz
  obtain ⟨_, hmul, hex⟩ := hM
  obtain ⟨u0, hu0, hc, hne⟩ := hex h hh
  set S := ∑ u : U, ((ψ ((u : P)⁻¹) : 𝓞 K) : K) • ρ (u : P) (ρ h z) with hS
  have hz' : ∀ u ∈ U, ρ u z = ((ψ u : 𝓞 K) : K) • z := by
    intro u hu
    unfold eig at hz
    have h1 := (Submodule.mem_iInf _).mp hz ⟨u, hu⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at h1
    exact h1
  have hA : ∑ u : U, ((ψ ((u : P)⁻¹) : 𝓞 K) : K) • ρ (u : P) (ρ u0 (ρ h z)) =
      ((ψ u0 : 𝓞 K) : K) • S := by
    rw [hS, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulRight (⟨u0, hu0⟩ : U)) _ _ (fun u => ?_)
    simp only [Equiv.coe_mulRight, Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul]
    congr 1
    have key : ψ ((u : P)⁻¹) = ψ u0 * ψ (((u : P) * u0)⁻¹) := by
      rw [← hmul u0 hu0 _ (U.inv_mem (U.mul_mem u.2 hu0))]
      congr 1
      group
    rw [key]
    norm_cast
  have hB : ∑ u : U, ((ψ ((u : P)⁻¹) : 𝓞 K) : K) • ρ (u : P) (ρ u0 (ρ h z)) =
      ((ψ (h⁻¹ * u0 * h) : 𝓞 K) : K) • S := by
    have e1 : ρ u0 (ρ h z) = ((ψ (h⁻¹ * u0 * h) : 𝓞 K) : K) • ρ h z := by
      have e2 : ρ u0 (ρ h z) = ρ h (ρ (h⁻¹ * u0 * h) z) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [e2, hz' _ hc, map_smul]
    rw [hS, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [e1, map_smul, smul_smul, smul_smul, mul_comm]
  have h3 : (((ψ u0 : 𝓞 K) : K) - ((ψ (h⁻¹ * u0 * h) : 𝓞 K) : K)) • S = 0 := by
    rw [sub_smul, ← hA, ← hB, sub_self]
  rcases smul_eq_zero.mp h3 with h0 | h0
  · exact absurd (by exact_mod_cast (sub_eq_zero.mp h0).symm) hne
  · exact h0

end Formalism.EigenvalueLevelCeiling
end

