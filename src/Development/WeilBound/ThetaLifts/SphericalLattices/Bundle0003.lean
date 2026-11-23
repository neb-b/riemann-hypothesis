module

public import Development.WeilBound.ThetaLifts.SphericalLattices.HoweInert
public import Development.WeilBound.ThetaLifts.SphericalLattices.Bundle0002
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ExistsEigenLift

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.SphericalLattices.BelowIffRows
section
noncomputable section

namespace PositivityTheory.Sph

open ValuativeRel Matrix

section Int

variable {k : Type} [Field k] [ValuativeRel k]

theorem intM_zero {m p : Type} : IntM (0 : Matrix m p k) := fun _ _ => zero_mem _

theorem IntM.add {m p : Type} {Z Z' : Matrix m p k} (h : IntM Z) (h' : IntM Z') : IntM (Z + Z') :=
  fun i j => add_mem (h i j) (h' i j)

theorem IntM.sub {m p : Type} {Z Z' : Matrix m p k} (h : IntM Z) (h' : IntM Z') : IntM (Z - Z') :=
  fun i j => sub_mem (h i j) (h' i j)

theorem IntM.neg {m p : Type} {Z : Matrix m p k} (h : IntM Z) : IntM (-Z) := fun i j => neg_mem (h i j)

theorem IntM.smul {m p : Type} {c : k} (hc : c ∈ 𝒪[k]) {Z : Matrix m p k} (h : IntM Z) : IntM (c • Z) :=
  fun i j => mul_mem hc (h i j)

theorem intM_map {m p : Type} (A : Matrix m p 𝒪[k]) : IntM (A.map (algebraMap 𝒪[k] k)) := fun i j => (A i j).2

theorem IntM.mul {m p q : Type} [Fintype p] {P : Matrix m p k} {Q : Matrix p q k} (hP : IntM P) (hQ : IntM Q) :
    IntM (P * Q) := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hP i l) (hQ l j)

variable {n d : ℕ}

theorem below_refl (t : k) (Y : Matrix (Fin n) (Fin d) k) : Below t Y Y :=
  ⟨1, 0, intM_zero, by simp [Matrix.map_one]⟩

theorem below_trans {t : k} {Y₁ Y₂ Y₃ : Matrix (Fin n) (Fin d) k} (h₁ : Below t Y₁ Y₂) (h₂ : Below t Y₂ Y₃) :
    Below t Y₁ Y₃ := by
  obtain ⟨A, Z, hZ, rfl⟩ := h₁
  obtain ⟨B, Z', hZ', rfl⟩ := h₂
  refine ⟨A * B, A.map (algebraMap 𝒪[k] k) * Z' + Z, (intM_map A).mul hZ' |>.add hZ, ?_⟩
  rw [Matrix.map_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc, smul_add, add_assoc]

theorem below_int {t : k} (ht : t ∈ 𝒪[k]) {Y Y₀ : Matrix (Fin n) (Fin d) k} (h : Below t Y Y₀) (h₀ : IntM (t • Y₀)) :
    IntM (t • Y) := by
  obtain ⟨A, Z, hZ, rfl⟩ := h
  have : t • (A.map (algebraMap 𝒪[k] k) * Y₀ + t • Z) = A.map (algebraMap 𝒪[k] k) * (t • Y₀) + t • (t • Z) := by
    rw [smul_add, Matrix.mul_smul]
  rw [this]
  exact ((intM_map A).mul h₀).add ((hZ.smul ht).smul ht)

theorem below_iff_rows (t : k) (Y Y₀ : Matrix (Fin n) (Fin d) k) : Below t Y Y₀ ↔ ∀ i, Y i ∈ latt t Y₀ := by
  constructor
  · rintro ⟨A, Z, hZ, rfl⟩ i
    have e : (A.map (algebraMap 𝒪[k] k) * Y₀ + t • Z) i =
        ∑ l, A i l • Y₀ l + ∑ j, (⟨Z i j, hZ i j⟩ : 𝒪[k]) • (t • (Pi.single j 1 : Fin d → k)) := by
      funext j'
      simp [Matrix.mul_apply, Finset.sum_apply, Pi.single_apply, Subring.smul_def, mul_comm]
      exact Finset.sum_congr rfl fun _ _ => rfl
    rw [e]
    refine add_mem (sum_mem fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨l, rfl⟩)))
      (sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨j, rfl⟩)))
  · intro h
    have hr : Set.range Y₀ ∪ Set.range (fun j : Fin d => t • (Pi.single j 1 : Fin d → k)) =
        Set.range (Sum.elim Y₀ fun j : Fin d => t • (Pi.single j 1 : Fin d → k)) := (Set.Sum.elim_range _ _).symm
    have h' : ∀ i, ∃ c : Fin n ⊕ Fin d → 𝒪[k],
        ∑ x, c x • Sum.elim Y₀ (fun j : Fin d => t • (Pi.single j 1 : Fin d → k)) x = Y i := by
      intro i
      have := h i
      rw [latt, hr] at this
      exact (Submodule.mem_span_range_iff_exists_fun _).1 this
    choose c hc using h'
    refine ⟨Matrix.of fun i l => c i (Sum.inl l), Matrix.of fun i j => (c i (Sum.inr j) : k),
      fun i j => (c i (Sum.inr j)).2, ?_⟩
    ext i j
    have := congrFun (hc i) j
    rw [Fintype.sum_sum_type] at this
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul] at this
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← this]
    congr 1
    show ∑ x, (c i (Sum.inr x) : k) * (t • (Pi.single x 1 : Fin d → k)) j = _
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, Ne.symm hb]) (by simp)]
    simp [mul_comm]

end Int

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

theorem below_iff {t : k} (ht : t ≠ 0) (Y₀ : Matrix (Fin n) (Fin d) k) :
    ∃ h : GL (Fin d) k, ∀ Y, Below t Y Y₀ ↔ IntM (Y * h.1) := by
  obtain ⟨h, hh⟩ := latt_eq ht Y₀
  refine ⟨h, fun Y => ?_⟩
  rw [below_iff_rows]
  simp only [hh, IntM]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]

def bsetoid (t : k) : Setoid (Matrix (Fin n) (Fin d) k) where
  r Y Y' := Below t Y Y' ∧ Below t Y' Y
  iseqv := ⟨fun Y => ⟨below_refl t Y, below_refl t Y⟩, fun h => ⟨h.2, h.1⟩,
    fun h h' => ⟨below_trans h.1 h'.1, below_trans h'.2 h.2⟩⟩

theorem mk_eq_iff {t : k} {Y Y' : Matrix (Fin n) (Fin d) k} :
    Quotient.mk (bsetoid t) Y = Quotient.mk (bsetoid t) Y' ↔ Below t Y Y' ∧ Below t Y' Y :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem out_rel {t : k} (Y : Matrix (Fin n) (Fin d) k) :
    Below t (Quotient.mk (bsetoid t) Y).out Y ∧ Below t Y (Quotient.mk (bsetoid t) Y).out :=
  mk_eq_iff.1 (Quotient.out_eq _)

def gens (k : Type) [Field k] [ValuativeRel k] (n d : ℕ) : Set (Matrix (Fin n) (Fin d) k → ℂ) :=
  {f | ∃ h : GL (Fin d) k, f = fun Y => Set.indicator {Z : Matrix (Fin n) (Fin d) k | ∀ i j, Z i j ∈ 𝒪[k]}
    (fun _ => (1 : ℂ)) (Y * h.1)}

theorem latSt : LatSt := by
  intro k _ _ _ _ n d Φ hΦ hK
  classical
  obtain ⟨h1, h2⟩ := hΦ
  obtain ⟨t, ht0, htO, hsupp, hinv⟩ := sb_bound h1 h2
  obtain ⟨S, hS⟩ := finite_cover (m := Fin n) (p := Fin d) t ht0

  have key : ∀ Y Y', Below t Y Y' → Below t Y' Y → Φ Y = Φ Y' := by
    intro Y Y' a b
    obtain ⟨U, hU, Z, hZ, rfl⟩ := orbit a b
    rw [hinv _ _ hZ]
    have hu : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).2 hU
    have := hK (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) hu.unit) ⟨hu.unit, rfl⟩ Y'
    have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) hu.unit : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        U.map (algebraMap 𝒪[k] k) := rfl
    rw [← e]
    exact this
  set s := bsetoid (n := n) (d := d) t with hs
  set T : Finset (Quotient s) := (S.filter fun y => IntM (t • y)).image (Quotient.mk s) with hT
  have memT : ∀ Y, IntM (t • Y) → Quotient.mk s Y ∈ T := by
    intro Y hY
    obtain ⟨y, hy, Z, hZ, rfl⟩ := hS Y hY
    have hy' : IntM (t • y) := by
      have e : t • y = t • (y + t • Z) - t • (t • Z) := by rw [smul_add]; abel
      rw [e]; exact hY.sub ((hZ.smul htO).smul htO)
    refine Finset.mem_image.2 ⟨y, Finset.mem_filter.2 ⟨hy, hy'⟩, mk_eq_iff.2 ⟨?_, ?_⟩⟩
    · exact ⟨1, -Z, hZ.neg, by simp [Matrix.map_one]⟩
    · exact ⟨1, Z, hZ, by simp [Matrix.map_one]⟩
  have outT : ∀ c ∈ T, IntM (t • c.out) := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc
    exact below_int htO (out_rel y).1 (Finset.mem_filter.1 hy).2
  let e : Quotient s → Matrix (Fin n) (Fin d) k → ℂ := fun c Y => if Quotient.mk s Y = c then 1 else 0
  let F : Quotient s → Finset (Quotient s) := fun c => T.filter fun c' => Below t c'.out c.out ∧ c' ≠ c
  have hi : ∀ c ∈ T, (fun Y => if Below t Y c.out then (1 : ℂ) else 0) ∈ Submodule.span ℂ (gens k n d) := by
    intro c _
    obtain ⟨h, hh⟩ := below_iff ht0 c.out
    refine Submodule.subset_span ⟨h, funext fun Y => ?_⟩
    by_cases hY : Below t Y c.out
    · rw [if_pos hY, Set.indicator_of_mem ((hh Y).1 hY)]
    · rw [if_neg hY, Set.indicator_of_notMem (fun h' => hY ((hh Y).2 h'))]
  have hdec : ∀ c ∈ T, (fun Y => if Below t Y c.out then (1 : ℂ) else 0) = e c + ∑ c' ∈ F c, e c' := by
    intro c hc
    funext Y
    simp only [Pi.add_apply, Finset.sum_apply]
    by_cases hB : Below t Y c.out
    · rw [if_pos hB]
      have hq : Quotient.mk s Y ∈ T := memT Y (below_int htO hB (outT c hc))
      by_cases hqc : Quotient.mk s Y = c
      · have h0 : ∑ c' ∈ F c, e c' Y = 0 := Finset.sum_eq_zero fun c' hc' => by
          simp only [e]
          rw [if_neg]
          intro h
          exact (Finset.mem_filter.1 hc').2.2 (h.symm.trans hqc)
        rw [h0, add_zero]
        simp only [e]
        rw [if_pos hqc]
      · have h0 : ∑ c' ∈ F c, e c' Y = 1 := by
          simp only [e]
          rw [Finset.sum_ite_eq, if_pos]
          exact Finset.mem_filter.2 ⟨hq, below_trans (out_rel Y).1 hB, hqc⟩
        rw [h0]
        simp only [e]
        rw [if_neg hqc, zero_add]
    · rw [if_neg hB]
      have h1 : e c Y = 0 := by
        simp only [e]
        rw [if_neg]
        intro h
        apply hB
        rw [← h]
        exact (out_rel Y).2
      have h2 : ∑ c' ∈ F c, e c' Y = 0 := Finset.sum_eq_zero fun c' hc' => by
        simp only [e]
        rw [if_neg]
        intro h
        apply hB
        have h3 := (Finset.mem_filter.1 hc').2.1
        rw [← h] at h3
        exact below_trans (out_rel Y).2 h3
      rw [h1, h2, add_zero]
  have he : ∀ m, ∀ c ∈ T, (F c).card = m → e c ∈ Submodule.span ℂ (gens k n d) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro c hc hm
      have hsum : ∑ c' ∈ F c, e c' ∈ Submodule.span ℂ (gens k n d) := by
        refine Submodule.sum_mem _ fun c' hc' => ?_
        have hc'T := (Finset.mem_filter.1 hc').1
        refine ih (F c').card ?_ c' hc'T rfl
        rw [← hm]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨c', hc', fun h => (Finset.mem_filter.1 h).2.2 rfl⟩
        · intro c'' hc''
          obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hc''
          obtain ⟨-, h4, h5⟩ := Finset.mem_filter.1 hc'
          refine Finset.mem_filter.2 ⟨h1, below_trans h2 h4, fun h => h5 ?_⟩
          rw [← Quotient.out_eq c', ← Quotient.out_eq c]
          refine mk_eq_iff.2 ⟨h4, ?_⟩
          rw [← h]
          exact h2
      have := Submodule.sub_mem _ (hi c hc) hsum
      rw [hdec c hc, add_sub_cancel_right] at this
      exact this
  have hΦ : Φ = ∑ c ∈ T, Φ c.out • e c := by
    funext Y
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, e, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    by_cases hY : IntM (t • Y)
    · rw [if_pos (memT Y hY)]
      exact key _ _ (out_rel Y).2 (out_rel Y).1
    · rw [if_neg]
      · by_contra h
        exact hY (hsupp Y h)
      · intro hq
        exact hY (below_int htO (out_rel Y).2 (outT _ hq))
  rw [hΦ]
  exact Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ (he _ c hc rfl)

end PositivityTheory.Sph

end
end

-- bundled from Development.WeilBound.ThetaLifts.SphericalLattices.FinInert
section
noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}


open scoped Classical in
def coef {v : Pl F} (ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)) (l : Fn F n d v →ₗ[ℂ] ℂ) :
    Fn F n d v →ₗ[ℂ] (UA σ W.J → ℂ) where
  toFun φ h := if h ∈ UAt σ W (evFin F v) then l (ω (1, h) φ) else 0
  map_add' φ φ' := by funext h; by_cases hh : h ∈ UAt σ W (evFin F v) <;> simp [hh]
  map_smul' c φ := by funext h; by_cases hh : h ∈ UAt σ W (evFin F v) <;> simp [hh]

section Loc

variable {v : Pl F} {ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)} {l : Fn F n d v →ₗ[ℂ] ℂ}

theorem coef_mem {φ : Fn F n d v} {h : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) : coef ω l φ h = l (ω (1, h) φ) := by
  simp [coef, hh]

theorem coef_not_mem {φ : Fn F n d v} {h : UA σ W.J} (hh : h ∉ UAt σ W (evFin F v)) : coef ω l φ h = 0 := by
  simp [coef, hh]

variable {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (Fn F n d v)}

theorem aug_stable (L : IsLocRep M ψ om v ω ρ) {h : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) :
    augAt om v ≤ (augAt om v).comap (ω (1, h)) := by
  have o1 := one_mem_UAt (σ := σ) X v
  have oW := one_mem_UAt (σ := σ) W v
  conv_lhs => unfold augAt
  rw [Submodule.span_le]
  rintro _ ⟨g, hg, φ, hφ, φ₁, hφ₁, ha, rfl⟩
  rw [(L.acts g hg 1 oW φ hφ φ₁).1 ha]
  have hφh := L.pres 1 o1 h hh φ hφ
  have e1 : ω (1, h) (ω (g, 1) φ) = ω (g, 1) (ω (1, h) φ) := by
    rw [← L.mul 1 o1 h hh g hg 1 oW φ hφ, ← L.mul g hg 1 oW 1 o1 h hh φ hφ]
    simp
  change ω (1, h) (ω (g, 1) φ - φ) ∈ augAt om v
  rw [map_sub, e1]
  exact Submodule.subset_span ⟨g, hg, _, hφh, _, L.pres g hg 1 oW _ hφh, (L.acts g hg 1 oW _ hφh _).2 rfl, rfl⟩

theorem coef_aug (L : IsLocRep M ψ om v ω ρ) (hl : augAt om v ≤ LinearMap.ker l) : augAt om v ≤ LinearMap.ker (coef ω l) := by
  intro z hz
  rw [LinearMap.mem_ker]
  funext h
  by_cases hh : h ∈ UAt σ W (evFin F v)
  · rw [coef_mem hh]; exact hl (aug_stable L hh hz)
  · rw [coef_not_mem hh]; rfl

theorem coef_transl (L : IsLocRep M ψ om v ω ρ) {h : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) {φ : Fn F n d v}
    (hφ : φ ∈ SB _) : coef ω l (ω (1, h) φ) = fun x => coef ω l φ (x * h) := by
  have o1 := one_mem_UAt (σ := σ) X v
  funext x
  by_cases hx : x ∈ UAt σ W (evFin F v)
  · rw [coef_mem hx, coef_mem (mul_mem_UAt hx hh), ← L.mul 1 o1 x hx 1 o1 h hh φ hφ, mul_one]
  · have hxh : x * h ∉ UAt σ W (evFin F v) := fun h' => hx (by
      have := mul_mem_UAt h' (inv_mem_UAt hh); rwa [mul_inv_cancel_right] at this)
    rw [coef_not_mem hx, coef_not_mem hxh]

def transl (Ω : UA σ W.J → ℂ) (v : Pl F) : Submodule ℂ (UA σ W.J → ℂ) :=
  Submodule.span ℂ {f | ∃ h ∈ UAt σ W (evFin F v), f = fun x => Ω (x * h)}

theorem map_coef (L : IsLocRep M ψ om v ω ρ) (V : IsVacSph M om v ω) (hs : M.vac v ∈ SB _) (hl : IsSphForm M om v ω l) :
    (SB _).map (coef ω l) = transl (coef ω l (M.vac v)) v := by
  have o1 := one_mem_UAt (σ := σ) X v
  apply le_antisymm
  · rintro _ ⟨φ, hφ, rfl⟩
    have h1 : augAt om v ≤ (transl (coef ω l (M.vac v)) v).comap (coef ω l) := fun z hz => by
      rw [Submodule.mem_comap, (LinearMap.mem_ker).1 (coef_aug L hl.aug hz)]; exact Submodule.zero_mem _
    have h2 : Submodule.span ℂ {z | ∃ h ∈ UAt σ W (evFin F v), z = ω (1, h) (M.vac v)} ≤
        (transl (coef ω l (M.vac v)) v).comap (coef ω l) := by
      rw [Submodule.span_le]
      rintro _ ⟨h, hh, rfl⟩
      exact Submodule.subset_span ⟨h, hh, coef_transl L hh hs⟩
    exact sup_le h1 h2 (V.gen φ hφ)
  · rw [transl, Submodule.span_le]
    rintro _ ⟨h, hh, rfl⟩
    exact ⟨_, L.pres 1 o1 h hh _ hs, coef_transl L hh hs⟩

theorem coef_vac_one (L : IsLocRep M ψ om v ω ρ) (hs : M.vac v ∈ SB _) (hl : IsSphForm M om v ω l) :
    coef ω l (M.vac v) 1 = 1 := by
  rw [coef_mem (one_mem_UAt W v)]
  have : ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 := rfl
  rw [this, L.one _ hs, hl.one]

theorem reach_vac (L : IsLocRep M ψ om v ω ρ) (V : IsVacSph M om v ω) (hl : IsSphForm M om v ω l) {φ : Fn F n d v}
    (hφ : φ ∈ SB _) (h0 : coef ω l φ ≠ 0) :
    ∃ h ∈ UAt σ W (evFin F v), ∃ (m : ℕ) (k : Fin (m + 1) → UA σ W.J) (c : ℂ), c ≠ 0 ∧
      (∀ i, k i ∈ KAt σ W v) ∧ ∑ i, ω (1, k i) (ω (1, h) φ) - c • M.vac v ∈ augAt om v := by
  have o1 := one_mem_UAt (σ := σ) X v
  obtain ⟨h, hh⟩ : ∃ h, coef ω l φ h ≠ 0 := by
    by_contra hc; exact h0 (funext fun x => by_contra fun hx => hc ⟨x, hx⟩)
  have hU : h ∈ UAt σ W (evFin F v) := by
    by_contra hn; exact hh (coef_not_mem hn)
  rw [coef_mem hU] at hh
  have hψ := L.pres 1 o1 h hU φ hφ
  obtain ⟨m, k, c, hk, hsum⟩ := V.line _ hψ
  refine ⟨h, hU, m, k, c, ?_, hk, hsum⟩
  intro hc0
  have := hl.aug hsum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.mem_ker, map_sub, map_sum, hc0, zero_smul, map_zero, sub_zero] at this
  have e : ∀ i, l (ω (1, k i) (ω (1, h) φ)) = l (ω (1, h) φ) := fun i => hl.inv _ (hk i) _ hψ
  simp only [e, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 (by exact_mod_cast Nat.succ_ne_zero m)
  · exact hh h1

end Loc

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {v : Pl F}

theorem finAt_sph {ω ρ ω' ρ'} (L : IsLocRep G.M B.ψ om v ω ρ) (L' : IsLocRep G.M' B.ψ om' v ω' ρ') (hv : v ∉ X.T)
    (hs : G.M.vac v ∈ SB _) (hs' : G.M'.vac v ∈ SB _) (V1 : IsVacSph G.M om v ω) (V2 : IsVacSph G.M' om' v ω')
    {l l'} (hl : IsSphForm G.M om v ω l) (hl' : IsSphForm G.M' om' v ω' l')
    (hΩ : ∀ h ∈ UAt σ G.W (evFin F v), l (ω (1, h) (G.M.vac v)) = l' (ω' (1, h) (G.M'.vac v))) :
    ∃ R, IsFinAt B G X om om' R v := by
  classical
  have o1 := one_mem_UAt (σ := σ) G.V v
  have o1' := one_mem_UAt (σ := σ) G.V' v
  set c := coef ω l with hc
  set c' := coef ω' l' with hc'
  have eΩ : c (G.M.vac v) = c' (G.M'.vac v) := by
    funext x
    by_cases hx : x ∈ UAt σ G.W (evFin F v)
    · rw [hc, hc', coef_mem hx, coef_mem hx]; exact hΩ x hx
    · rw [hc, hc', coef_not_mem hx, coef_not_mem hx]
  set S := transl (c (G.M.vac v)) v with hS
  have mS : (SB _).map c = S := map_coef L V1 hs hl
  have mS' : (SB _).map c' = S := by rw [hS, eΩ]; exact map_coef L' V2 hs' hl'
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective S.subtype S.ker_subtype
  have hπ' : ∀ x (hx : x ∈ S), π x = ⟨x, hx⟩ := fun x hx => LinearMap.congr_fun hπ ⟨x, hx⟩
  have mc : ∀ φ ∈ SB _, c φ ∈ S := fun φ hφ => mS ▸ Submodule.mem_map_of_mem hφ
  have mc' : ∀ φ ∈ SB _, c' φ ∈ S := fun φ hφ => mS' ▸ Submodule.mem_map_of_mem hφ
  have inj : ∀ x ∈ S, ∀ y ∈ S, π x = π y → x = y := fun x hx y hy h => by
    rw [hπ' x hx, hπ' y hy] at h; exact congrArg Subtype.val h
  let R : FinMaps F a a' :=
    { Pi := fun _ => S
      p := fun u => if h : v = u then h ▸ (π ∘ₗ c) else 0
      p' := fun u => if h : v = u then h ▸ (π ∘ₗ c') else 0 }
  have e : R.p v = π ∘ₗ c := dif_pos rfl
  have e' : R.p' v = π ∘ₗ c' := dif_pos rfl
  have hx : ∀ x : S, π x.1 = x := fun x => hπ' x.1 x.2
  have on : ∀ x : S, ∃ φ ∈ SB _, c φ = x := fun x => (mS.symm ▸ x.2 : x.1 ∈ (SB _).map c)
  have on' : ∀ x : S, ∃ φ ∈ SB _, c' φ = x := fun x => (mS'.symm ▸ x.2 : x.1 ∈ (SB _).map c')
  have Ω1 : c (G.M.vac v) 1 = 1 := coef_vac_one L hs hl
  have ΩS : c (G.M.vac v) ∈ S := mc _ hs
  have Ω0 : c (G.M.vac v) ≠ 0 := fun h => by
    have := congrFun h 1; rw [Ω1] at this; exact one_ne_zero this
  have hne : π (c (G.M.vac v)) ≠ 0 := fun h => Ω0 (inj _ ΩS 0 S.zero_mem (h.trans (map_zero π).symm))
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ⟨_, _, hne⟩, ?_, fun _ => ?_, fun _ h => absurd h hv⟩
  · rw [e, eq_top_iff]
    intro x _
    obtain ⟨φ, hφ, h⟩ := on x
    exact ⟨φ, hφ, by rw [LinearMap.comp_apply, h, hx]⟩
  · rw [e', eq_top_iff]
    intro x _
    obtain ⟨φ, hφ, h⟩ := on' x
    exact ⟨φ, hφ, by rw [LinearMap.comp_apply, h, hx]⟩
  · rw [e]
    exact (coef_aug L hl.aug).trans (LinearMap.ker_le_ker_comp _ _)
  · rw [e']
    exact (coef_aug L' hl'.aug).trans (LinearMap.ker_le_ker_comp _ _)
  · intro h hh φ hφ φ' hφ' φ₁ _ φ₁' _ a1 a2 heq
    rw [e, e'] at heq ⊢
    rw [(L.acts 1 o1 h hh φ hφ _).1 a1, (L'.acts 1 o1' h hh φ' hφ' _).1 a2]
    have := inj _ (mc _ hφ) _ (mc' _ hφ') heq
    change π (c (ω (1, h) φ)) = π (c' (ω' (1, h) φ'))
    rw [hc, hc', coef_transl L hh hφ, coef_transl L' hh hφ', ← hc, ← hc', this]
  · intro N hN
    rw [e] at hN
    by_cases hb : N = ⊥
    · exact Or.inl hb
    right
    obtain ⟨y, hyN, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨φ, hφ, hcφ⟩ := on y
    have hc0 : c φ ≠ 0 := fun h => hy0 (by rw [← hx y, ← hcφ, h, map_zero])
    obtain ⟨h, hU, m, k, cc, hcc, hk, hsum⟩ := reach_vac L V1 hl hφ hc0
    have hψ := L.pres 1 o1 h hU φ hφ
    have step : ∀ g ∈ UAt σ G.W (evFin F v), ∀ χ ∈ SB _, π (c χ) ∈ N → π (c (ω (1, g) χ)) ∈ N := fun g hg χ hχ hN' =>
      hN g hg χ hχ _ (L.pres 1 o1 g hg χ hχ) ((L.acts 1 o1 g hg χ hχ _).2 rfl) hN'
    have hyφ : π (c φ) ∈ N := by rw [hcφ, hx]; exact hyN
    have h1 : π (c (ω (1, h) φ)) ∈ N := step h hU φ hφ hyφ
    have h2 : ∀ i, π (c (ω (1, k i) (ω (1, h) φ))) ∈ N := fun i => step _ (hk i).1 _ hψ h1
    have h3 : π (c (∑ i, ω (1, k i) (ω (1, h) φ))) ∈ N := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum]; exact Submodule.sum_mem _ fun i _ => h2 i
    have h4 : c (∑ i, ω (1, k i) (ω (1, h) φ)) = cc • c (G.M.vac v) := by
      have := (LinearMap.mem_ker).1 (coef_aug L hl.aug hsum)
      rw [map_sub, sub_eq_zero, map_smul] at this
      rw [hc]; exact this
    rw [h4, map_smul] at h3
    have hv0 : π (c (G.M.vac v)) ∈ N := by
      have := N.smul_mem cc⁻¹ h3; rwa [smul_smul, inv_mul_cancel₀ hcc, one_smul] at this
    have hall : ∀ g ∈ UAt σ G.W (evFin F v), π (c (ω (1, g) (G.M.vac v))) ∈ N := fun g hg => step g hg _ hs hv0
    rw [eq_top_iff]
    intro x _
    have hle : S ≤ N.map S.subtype := by
      change transl (c (G.M.vac v)) v ≤ _
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, hg, rfl⟩
      have hmem : c (ω (1, g) (G.M.vac v)) ∈ S := mc _ (L.pres 1 o1 g hg _ hs)
      refine ⟨_, hall g hg, ?_⟩
      rw [hπ' _ hmem]
      change c (ω (1, g) (G.M.vac v)) = _
      rw [hc, coef_transl L hg hs]
    obtain ⟨z, hz, hzx⟩ := hle x.2
    have : z = x := Subtype.ext hzx
    exact this ▸ hz
  · rw [e, e']
    refine ⟨by rw [LinearMap.comp_apply, LinearMap.comp_apply, eΩ], hne⟩

theorem finInert_of (hV : VacInert) (hF : SphFun) (hA : LocRepEx) : FinInert := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v ⟨hv, he⟩
  have P : PairOK B G.V G.W G.M om := ⟨hT.base, ⟨_, _, hT.geo.hV⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM, _, _, hT.weil⟩
  have P' : PairOK B G.V' G.W G.M' om' := ⟨hT.base, ⟨_, _, hT.geo.hV'⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM', _, _, hT.weil'⟩
  obtain ⟨ω, ρ, L⟩ := hA F E σ _ _ B _ _ _ _ P v
  obtain ⟨ω', ρ', L'⟩ := hA F E σ _ _ B _ _ _ _ P' v
  obtain ⟨V1, V2⟩ := hV F E σ B a a' G X om om' hT v he
  have V1 := V1 ω ρ L
  have V2 := V2 ω' ρ' L'
  obtain ⟨l, l', hl, hl', hΩ⟩ := hF F E σ B a a' G X om om' hT v he ω ρ ω' ρ' L L' V1.fixW V2.fixW
  exact finAt_sph L L' hv (hT.geo.hM.vac v).1 (hT.geo.hM'.vac v).1 V1 V2 hl hl' hΩ

end PositivityTheory.Sph

end
end

