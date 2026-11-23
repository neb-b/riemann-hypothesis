module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0307

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruh
section
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.LinSchur

theorem dual {k : Type} [Field k] [ValuativeRel k] {ψ0 : AddChar k ℂ} {n d : ℕ} {s : k}
    {Y : Matrix (Fin n) (Fin d) k} (hY : Y ∉ latt ψ0 n d s) :
    ∃ l : Matrix (Fin n) (Fin d) k →ₗ[k] k, (∀ Z ∈ latt ψ0 n d s, ψ0 (l Z) = 1) ∧ ψ0 (l Y) ≠ 1 := by
  rw [mem_latt] at hY
  push_neg at hY
  obtain ⟨i, j, o, ho, h⟩ := hY
  let l : Matrix (Fin n) (Fin d) k →ₗ[k] k :=
    { toFun := fun Z => o * (s * Z i j)
      map_add' := fun a b => by simp only [Matrix.add_apply]; ring
      map_smul' := fun c a => by simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  exact ⟨l, fun Z hZ => hZ i j o ho, h⟩

theorem cind_mem {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] {L : AddSubgroup X}
    (ho : IsOpen (L : Set X)) (hc : IsCompact (L : Set X)) (y : X) : cind L y ∈ GlobalTheory.WeilM.SB X := by
  have hK : IsOpen {Z : X | Z - y ∈ L} := ho.preimage (continuous_sub_right y)
  have hKc : IsClosed {Z : X | Z - y ∈ L} := (AddSubgroup.isClosed_of_isOpen L ho).preimage (continuous_sub_right y)
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro Y
    by_cases hY : Y - y ∈ L
    · exact ⟨_, hK, hY, fun Z hZ => by simp only [cind, if_pos (show Z - y ∈ L from hZ), if_pos hY]⟩
    · exact ⟨_, hKc.isOpen_compl, hY, fun Z hZ => by simp only [cind, if_neg (show Z - y ∉ L from hZ), if_neg hY]⟩
  · have himg : {Z : X | Z - y ∈ L} = (fun Z => Z + y) '' (L : Set X) := by
      ext Z
      constructor
      · intro h
        exact ⟨Z - y, h, sub_add_cancel Z y⟩
      · rintro ⟨W, hW, rfl⟩
        show W + y - y ∈ L
        rwa [add_sub_cancel_right]
    refine IsCompact.of_isClosed_subset (himg ▸ hc.image (continuous_add_const y)) (isClosed_tsupport _)
      (closure_minimal ?_ hKc)
    intro Z hZ
    by_contra h
    exact hZ (by simp only [cind, if_neg (show Z - y ∉ L from h)])

theorem addChar_ne_zero {A : Type} [AddGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := by
  intro h
  have e := AddChar.map_add_eq_mul ψ a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at e
  exact one_ne_zero e

end GlobalTheory.LinSchur


open GlobalTheory.LinSchur in
theorem GlobalTheory.LinSchur.eq_smul_of_commute : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} {Xt : Type} [AddCommGroup Xt] [Module ℂ Xt] (V : Submodule ℂ Xt)
    (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι₁ : Xt →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)) (ι₂ : Xt → Matrix (Fin n) (Fin d) k → ℂ),
    Set.BijOn ι₁ (V : Set Xt) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) →
    (∀ x ∈ V, ∀ y ∈ V, ∀ c : ℂ, ι₂ (c • x + y) = c • ι₂ x + ι₂ y) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → Xt → Xt) (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → Xt → Xt),
    (∀ C, ∀ x ∈ V, Tr C x ∈ V ∧ ι₁ (Tr C x) = (fun Y => ι₁ x (Y + C)) ∧ ι₂ (Tr C x) = fun Y => ι₂ x (Y + C)) →
    (∀ l, ∀ x ∈ V, Mu l x ∈ V ∧ ι₁ (Mu l x) = (fun Y => ψ0 (l Y) * ι₁ x Y) ∧ ι₂ (Mu l x) = fun Y => ψ0 (l Y) * ι₂ x Y) →
    ∃ c : ℂ, ∀ x ∈ V, ι₂ x = c • ι₁ x := by
  intro k _ _ _ _ n d Xt _ _ V ψ0 hcont hne ι₁ ι₂ hbij hlin Tr Mu hTr hMu
  classical
  obtain ⟨hLoc, hBasis⟩ := _root_.GlobalTheory.LinSchurLatt.latt_open_compact_basis n d ψ0 hcont hne
  have inj : ∀ x ∈ V, ∀ y ∈ V, ι₁ x = ι₁ y → x = y := fun x hx y hy h => hbij.injOn hx hy h
  have surj : ∀ f ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k), ∃ x, x ∈ V ∧ ι₁ x = f := fun f hf => hbij.surjOn hf
  have maps : ∀ x ∈ V, ι₁ x ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) := fun x hx => hbij.mapsTo hx
  have h20 : ι₂ 0 = 0 := by
    have e := hlin 0 V.zero_mem 0 V.zero_mem 1
    simpa using e
  have hsmul : ∀ x ∈ V, ∀ c : ℂ, ι₂ (c • x) = c • ι₂ x := by
    intro x hx c
    have e := hlin x hx 0 V.zero_mem c
    rwa [add_zero, h20, add_zero] at e
  have hsum : ∀ (F : Finset (Matrix (Fin n) (Fin d) k)) (a : Matrix (Fin n) (Fin d) k → ℂ)
      (xs : Matrix (Fin n) (Fin d) k → Xt), (∀ y ∈ F, xs y ∈ V) →
      ι₂ (∑ y ∈ F, a y • xs y) = ∑ y ∈ F, a y • ι₂ (xs y) := by
    intro F a xs hxs
    induction F using Finset.induction_on with
    | empty => simpa using h20
    | insert y F hy ih =>
      rw [Finset.sum_insert hy, Finset.sum_insert hy, hlin _ (hxs y (Finset.mem_insert_self _ _)) _
        (V.sum_mem fun z hz => V.smul_mem _ (hxs z (Finset.mem_insert_of_mem hz))),
        ih fun z hz => hxs z (Finset.mem_insert_of_mem hz)]
  have stepB : ∀ x ∈ V, ∀ C, (∀ Y, ι₁ x (Y + C) = ι₁ x Y) → ∀ Y, ι₂ x (Y + C) = ι₂ x Y := by
    intro x hx C hper Y
    obtain ⟨h1, h2, h3⟩ := hTr C x hx
    have e0 : Tr C x = x := inj _ h1 _ hx (by rw [h2]; funext Y; exact hper Y)
    have e := congrFun h3 Y
    rw [e0] at e
    exact e.symm
  have stepA : ∀ s : k, ∀ x ∈ V, ∀ y, ι₁ x = cind (latt ψ0 n d s) y → ∀ Y, Y - y ∉ latt ψ0 n d s → ι₂ x Y = 0 := by
    intro s x hx y hxy Y hY
    obtain ⟨l, hl1, hl2⟩ := dual hY
    obtain ⟨m1, m2, m3⟩ := hMu l x hx
    have e1 : ι₁ (Mu l x) = ι₁ (ψ0 (l y) • x) := by
      rw [m2, map_smul, hxy]
      funext Z
      simp only [cind, Pi.smul_apply, smul_eq_mul]
      split_ifs with hZ
      · rw [mul_one, mul_one, show l Z = l (Z - y) + l y by rw [← map_add (f := _), sub_add_cancel],
          AddChar.map_add_eq_mul, hl1 _ hZ, one_mul]
      · simp
    have e2 : Mu l x = ψ0 (l y) • x := inj _ m1 _ (V.smul_mem _ hx) e1
    have e3 := congrFun m3 Y
    rw [e2, hsmul x hx] at e3
    simp only [Pi.smul_apply, smul_eq_mul] at e3
    have hYy : ψ0 (l Y) = ψ0 (l (Y - y)) * ψ0 (l y) := by
      rw [← AddChar.map_add_eq_mul, ← map_add (f := _), sub_add_cancel]
    rw [hYy] at e3
    have e4 : ψ0 (l y) * (1 - ψ0 (l (Y - y))) * ι₂ x Y = 0 := by linear_combination e3
    rcases mul_eq_zero.mp e4 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h (addChar_ne_zero ψ0 _)
      · exact absurd (sub_eq_zero.mp h).symm hl2
    · exact h
  have stepC : ∀ s : k, ∀ x ∈ V, ∀ y, ι₁ x = cind (latt ψ0 n d s) y → ι₂ x = ι₂ x y • ι₁ x := by
    intro s x hx y hxy
    funext Y
    rw [hxy]
    simp only [cind, Pi.smul_apply, smul_eq_mul]
    split_ifs with hY
    · rw [mul_one]
      have e := stepB x hx (Y - y) (fun Z => by
        rw [hxy]
        simp only [cind]
        rw [show Z + (Y - y) - y = (Z - y) + (Y - y) by abel, (latt ψ0 n d s).add_mem_cancel_right hY]) y
      rwa [add_sub_cancel] at e
    · rw [mul_zero]
      exact stepA s x hx y hxy Y hY
  have hcind : ∀ s : k, s ≠ 0 → ∀ y, cind (latt ψ0 n d s) y ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) :=
    fun s hs y => cind_mem (hLoc s hs).1 (hLoc s hs).2 y
  choose! xs hxsV hxs1 using fun s (hs : s ≠ 0) y => surj _ (hcind s hs y)
  have stepD : ∀ s : k, s ≠ 0 → ∀ x ∈ V, ∀ y, ι₁ x = cind (latt ψ0 n d s) y →
      ι₂ x = ι₂ (xs s 0) 0 • ι₁ x := by
    intro s hs x hx y hxy
    rw [stepC s x hx y hxy]
    congr 1
    obtain ⟨t1, t2, t3⟩ := hTr y x hx
    have e0 : Tr y x = xs s 0 := inj _ t1 _ (hxsV s hs 0) (by
      rw [t2, hxs1 s hs 0, hxy]
      funext Z
      simp only [cind, add_sub_cancel_right, sub_zero])
    have e := congrFun t3 0
    rw [e0, zero_add] at e
    exact e.symm
  have stepE : ∀ s : k, s ≠ 0 → ∀ x ∈ V, (∀ Y, ∀ C ∈ latt ψ0 n d s, ι₁ x (Y + C) = ι₁ x Y) →
      ι₂ x = ι₂ (xs s 0) 0 • ι₁ x := by
    intro s hs x hx hper
    obtain ⟨F, hF⟩ := GlobalTheory.T.exists_finset_eq_sum_addCosetIndicator _ (hLoc s hs).1 (ι₁ x) (maps x hx) hper
    have hxeq : x = ∑ y ∈ F, ι₁ x y • xs s y :=
      inj _ hx _ (V.sum_mem fun y _ => V.smul_mem _ (hxsV s hs y)) (by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [map_smul, hxs1 s hs]
        exact hF)
    calc ι₂ x = ι₂ (∑ y ∈ F, ι₁ x y • xs s y) := congrArg ι₂ hxeq
      _ = ∑ y ∈ F, ι₁ x y • ι₂ (xs s y) := hsum F _ _ (fun y _ => hxsV s hs y)
      _ = ∑ y ∈ F, ι₁ x y • (ι₂ (xs s 0) 0 • cind (latt ψ0 n d s) y) :=
          Finset.sum_congr rfl fun y _ => by
            rw [stepD s hs (xs s y) (hxsV s hs y) y (hxs1 s hs y), hxs1 s hs y]
      _ = ι₂ (xs s 0) 0 • ∑ y ∈ F, ι₁ x y • cind (latt ψ0 n d s) y := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun y _ => smul_comm _ _ _
      _ = ι₂ (xs s 0) 0 • ι₁ x := by rw [← hF]
  have stepF : ∀ s : k, s ≠ 0 → ∀ s' : k, s' ≠ 0 →
      (latt ψ0 n d s' : Set (Matrix (Fin n) (Fin d) k)) ⊆ latt ψ0 n d s →
      ι₂ (xs s 0) 0 = ι₂ (xs s' 0) 0 := by
    intro s hs s' hs' hsub
    have e0 := stepE s' hs' (xs s 0) (hxsV s hs 0) (fun Y C hC => by
      rw [hxs1 s hs 0]
      simp only [cind, sub_zero, (latt ψ0 n d s).add_mem_cancel_right (hsub hC)])
    have e := congrFun e0 0
    rw [hxs1 s hs 0] at e
    simpa [cind] using e
  refine ⟨ι₂ (xs 1 0) 0, fun x hx => ?_⟩
  obtain ⟨⟨s, hs⟩, hper⟩ := GlobalTheory.T.exists_openSubgroup_periodic (fun s : {s : k // s ≠ 0} => latt ψ0 n d s) (fun s => (hLoc s.1 s.2).1)
    (fun W hW => by
      obtain ⟨s, hs, h⟩ := hBasis W hW
      exact ⟨⟨s, hs⟩, h⟩) (ι₁ x) (maps x hx)
  rw [stepE s hs x hx hper]
  congr 1
  obtain ⟨s'', hs'', hsub⟩ := hBasis ((latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ∩ latt ψ0 n d 1)
    (inter_mem ((hLoc s hs).1.mem_nhds (latt ψ0 n d s).zero_mem) ((hLoc 1 one_ne_zero).1.mem_nhds (latt ψ0 n d 1).zero_mem))
  rw [stepF s hs s'' hs'' (fun z hz => (hsub hz).1), stepF 1 one_ne_zero s'' hs'' (fun z hz => (hsub hz).2)]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties :
    ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ},
    (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x,
      ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧
      ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧
      ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧
      ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧
    (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
      Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧
    (∀ α β : Cochain ((chains R).obj E) I n,
      (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧
    (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U),
      ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧
    ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x,
      ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  intro R _ E I n
  have ev_eq {F : Spc} {J : Cx R} (α : Cochain ((chains R).obj F) J n)
      (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx F p U) :
      ev α p s h U x = Sec.map ((chainsXIso R F p).inv ≫ α.v _ _ h) (freeGen R _ U x) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro α β p s h U x
    have hadd (a b : Cochain ((chains R).obj E) I n) :
        ev (a + b) p s h U x = ev a p s h U x + ev b p s h U x := by
      simp [ev, Cochain.add_v]
    let eval : Cochain ((chains R).obj E) I n →+ Sec (I.X s) U :=
      AddMonoidHom.mk' (fun a => ev a p s h U x) hadd
    exact ⟨hadd α β, map_sub eval α β, map_zero eval, fun c => map_zsmul eval c α⟩
  · intro α p s h V U g x
    rw [ev_eq, CupSpec.map_res, CupSpec.freeGen_res]
    rfl
  · intro α β H
    ext p s hs : 1
    by_cases hp : p ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R E k).inv]
      exact CupSpec.free_ext _ _ (fun U x => H k s hs U x)
    · exact (CupSpec.isZero_chains E p (by omega)).eq_of_src _ _
  · intro E' f α p s h U x
    rw [ev_eq, ev_eq, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      ← Category.assoc, CupSpec.chains_map, Category.assoc]
    change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h)
      (Sec.map ((free R).map _) (freeGen R _ U x)) = _
    rw [CupSpec.freeGen_map]
    rfl
  · intro J m α p s h U x
    rw [ev_eq, ev_eq, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
      ← Category.assoc]
    rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexDifferentialValuesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values :
    ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m)
      (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}),
      (∀ (x : Sx E 0 U), ev (δ n m α) 0 m (by simp) U x =
        Sec.map (I.d n m) (ev α 0 n (by simp) U x)) ∧
      ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s)
        (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U),
        ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
          m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i) := by
  intro R _ E I n m hm α U
  have ev_def {k : ℤ} (β : Cochain ((chains R).obj E) I k) (p : ℕ) (s : ℤ)
      (h : -(p : ℤ) + k = s) (x : Sx E p U) :
      ev β p s h U x = Sec.map ((chainsXIso R E p).inv ≫ β.v _ _ h) (freeGen R _ U x) := rfl
  have hzero (x : Sx E 0 U) :
      ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x) := by
    rw [ev_def, δ_v n m hm α _ m (by simp) n 1 (by omega) (by simp),
      (CupSpec.isZero_chains (R := R) E 1 one_pos).eq_of_tgt (((chains R).obj E).d _ 1) 0,
      zero_comp, smul_zero, add_zero]
    rfl
  have hsucc (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s)
      (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U) :
      ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
        m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i) := by
    rw [ev_def, δ_v n m hm α _ t ht s (-(p : ℤ)) (by omega) (by omega), Preadditive.comp_add,
      Units.smul_def, Preadditive.comp_zsmul, ← Category.assoc _ (((chains R).obj E).d _ _),
      CupSpec.chains_d, Category.assoc, Preadditive.sum_comp]
    refine (map_add (CupSpec.mapHom _ _ (freeGen R _ U x)) _ _).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zsmul, map_sum, Units.smul_def]
    refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
    rw [Preadditive.zsmul_comp, map_zsmul]
    congr 1
    change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ _) (Sec.map ((free R).map _) (freeGen R _ U x)) = _
    rw [CupSpec.freeGen_map]
    rfl
  exact ⟨hzero, hsucc⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleComplexStaircaseLocallyExact
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.Stair

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (s : Sec F U) :
    Sec.res (k ≫ g) s = Sec.res k (Sec.res g s) := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (s : Sec F U) :
    Sec.map φ (Sec.res g s) = Sec.res g (Sec.map φ s) :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.hom.naturality g.op)) s

theorem map_nsmul' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (n : ℕ) (s : Sec F U) :
    Sec.map φ (n • s) = n • Sec.map φ s := map_nsmul _ _ _

theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (s : Sec F U) :
    Sec.res g (n • s) = n • Sec.res g s := map_nsmul _ _ _

theorem map_add' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (s t : Sec F U) :
    Sec.map φ (s + t) = Sec.map φ s + Sec.map φ t := map_add _ _ _

theorem map_zero' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := map_zero _

theorem res_sub {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (s t : Sec F U) :
    Sec.res g (s - t) = Sec.res g s - Sec.res g t := map_sub _ _ _

theorem map_d_d {R : Type} [CommRing R] (K : Cx R) (h i j : ℤ) {U : Scheme.{0}} (w : Sec (K.X h) U) :
    Sec.map (K.d i j) (Sec.map (K.d h i) w) = 0 := by
  change ((K.d h i ≫ K.d i j).hom.app (op U)).hom w = 0
  rw [K.d_comp_d h i j]; rfl

theorem loc_of {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  loc_calculus.1 U P h

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q :=
  loc_calculus.2.1 U P Q hP h

theorem loc_bind {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q :=
  loc_calculus.2.2.2.2.1 U Q (loc_mono hP h)

def StairP {R : Type} [CommRing R] (K : Cx R) (r : ℕ) (i : ℤ) : Prop :=
  ∀ (h j : ℤ), h + 1 = i → i + 1 = j → ∀ (U : Scheme.{0}) (x : Sec (K.X i) U),
    (Loc U fun V g => ∃ y : Sec (K.X j) V, Sec.map (K.d i j) (Sec.res g x) = r • y) →
    Loc U fun V g => ∃ (u : Sec (K.X h) V) (y : Sec (K.X i) V), Sec.res g x = Sec.map (K.d h i) u + r • y

theorem stair_step {R : Type} [CommRing R] (K : Cx R) (r s : ℕ)
    (hrs : ∀ (n : ℤ) (U : Scheme.{0}) (y : Sec (K.X n) U), (r * s) • y = 0)
    (hfl : ∀ (n : ℤ) (U : Scheme.{0}) (x : Sec (K.X n) U), s • x = 0 →
      Loc U fun V g => ∃ y : Sec (K.X n) V, Sec.res g x = r • y)
    (hex : ∀ (h i j : ℤ), h + 1 = i → i + 1 = j → ∀ (U : Scheme.{0}) (b : Sec (K.X i) U),
      Sec.map (K.d i j) b = 0 → Loc U fun V g => ∃ c : Sec (K.X h) V, Sec.map (K.d h i) c = Sec.res g b)
    (i : ℤ) (ih : StairP K s (i - 1)) : StairP K r i := by
  intro h j hh hj U x hL
  obtain rfl : h = i - 1 := by omega
  refine loc_bind hL fun V g hy => ?_
  obtain ⟨y, hy⟩ := hy
  have hcyc : Sec.map (K.d i j) (s • Sec.res g x) = 0 := by
    rw [map_nsmul', hy, smul_smul, mul_comm, hrs]
  refine loc_bind (hex (i - 1) i j (by omega) hj V _ hcyc) fun W k hc => ?_
  obtain ⟨c, hc⟩ := hc
  rw [res_nsmul] at hc
  have hP := ih (i - 1 - 1) i (by omega) (by omega) W c
    (loc_of fun W' k' => ⟨Sec.res k' (Sec.res k (Sec.res g x)), by rw [map_res, hc, res_nsmul]⟩)
  refine loc_bind hP fun W' k' hw => ?_
  obtain ⟨w, u', hw⟩ := hw
  have hz : s • (Sec.res k' (Sec.res k (Sec.res g x)) - Sec.map (K.d (i - 1) i) u') = 0 := by
    rw [smul_sub, ← res_nsmul, ← hc, ← map_res, hw, map_add', map_nsmul', map_d_d, zero_add, sub_self]
  refine loc_mono (hfl i W' _ hz) fun W'' k'' hy' => ?_
  obtain ⟨y', hy'⟩ := hy'
  refine ⟨Sec.res k'' u', y', ?_⟩
  rw [res_sub, ← map_res, sub_eq_iff_eq_add] at hy'
  simp only [res_comp]
  rw [hy', add_comm]

end GlobalTheory.EtC.Stair

namespace GlobalTheory.EtC


open Stair in
theorem staircase_loc : ∀ (R : Type) [CommRing R] (q e : ℕ) (K : Cx R) (a : ℤ),
    (∀ n, n < a → ∀ (U : Scheme.{0}) (x : Sec (K.X n) U), x = 0) →
    (∀ (n : ℤ) (U : Scheme.{0}) (y : Sec (K.X n) U), (q * e) • y = 0) →
    (∀ (n : ℤ) (U : Scheme.{0}) (x : Sec (K.X n) U), e • x = 0 → Loc U fun V g => ∃ y : Sec (K.X n) V, Sec.res g x = q • y) →
    (∀ (n : ℤ) (U : Scheme.{0}) (x : Sec (K.X n) U), q • x = 0 → Loc U fun V g => ∃ y : Sec (K.X n) V, Sec.res g x = e • y) →
    (∀ (n : ℤ) (U : Scheme.{0}) (b : Sec (K.X n) U), Sec.map (K.d n (n + 1)) b = 0 →
      Loc U fun V g => ∃ c : Sec (K.X (n - 1)) V, Sec.map (K.d (n - 1) n) c = Sec.res g b) →
    ∀ (n : ℤ) (U : Scheme.{0}) (x : Sec (K.X n) U),
      (Loc U fun V g => ∃ y : Sec (K.X (n + 1)) V, Sec.map (K.d n (n + 1)) (Sec.res g x) = q • y) →
      Loc U fun V g => ∃ (u : Sec (K.X (n - 1)) V) (y : Sec (K.X n) V), Sec.res g x = Sec.map (K.d (n - 1) n) u + q • y := by
  intro R _ q e K a hbd hqe hq he hex n U x hx
  have hex' : ∀ (h i j : ℤ), h + 1 = i → i + 1 = j → ∀ (U : Scheme.{0}) (b : Sec (K.X i) U),
      Sec.map (K.d i j) b = 0 → Loc U fun V g => ∃ c : Sec (K.X h) V, Sec.map (K.d h i) c = Sec.res g b := by
    intro h i j hh hj U b hb
    obtain rfl : h = i - 1 := by omega
    obtain rfl : j = i + 1 := by omega
    exact hex i U b hb
  have hqe' : ∀ (n : ℤ) (U : Scheme.{0}) (y : Sec (K.X n) U), (e * q) • y = 0 := fun n U y => by
    rw [mul_comm]; exact hqe n U y
  have base : ∀ (r : ℕ) (i : ℤ), i < a → StairP K r i := by
    intro r i hi h j _ _ U x _
    exact loc_of fun V g => ⟨0, 0, by rw [hbd i hi V (Sec.res g x), map_zero', smul_zero, add_zero]⟩
  have key : ∀ k : ℕ, ∀ i : ℤ, i < a + k → StairP K q i ∧ StairP K e i := by
    intro k
    induction k with
    | zero => intro i hi; exact ⟨base q i (by simpa using hi), base e i (by simpa using hi)⟩
    | succ k ih =>
      intro i hi
      obtain ⟨h1, h2⟩ := ih (i - 1) (by push_cast at hi; omega)
      exact ⟨stair_step K q e hqe hq hex' i h2, stair_step K e q hqe' he hex' i h1⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n < a + k := ⟨(n - a + 1).toNat, by omega⟩
  exact (key k n hk).1 (n - 1) (n + 1) (by omega) rfl U x hx

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatDescendsOfIsColimit
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etFF_descends_of_isColimit :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D),
      IsColimit c → ∀ (B : CommRingCat.{0}) (g : c.pt ⟶ B), EtFF g →
      ∃ (j : J) (B' : CommRingCat.{0}) (g' : D.obj j ⟶ B') (h : B' ⟶ B),
        EtFF g' ∧ IsPushout g' (c.ι.app j) h g := by
  intro J _ _ D c hc B g hg
  obtain ⟨-, hsurj⟩ := (etFF_iff_spec g).1 hg
  obtain ⟨j₀⟩ := IsFiltered.nonempty (C := J)
  obtain ⟨j, -, B', g', h, hgh, hcov⟩ :=
    GlobalTheory.EtaleCoverDescent.exists_etale_cover_model_of_isColimit J D c hc Unit (fun _ ↦ B)
      (fun _ ↦ g) (fun _ ↦ hg.1)
      (fun p ↦ by
        obtain ⟨v, hv⟩ := hsurj.surj p
        exact ⟨(), v, hv⟩) j₀
  refine ⟨j, B' (), g' (), h (), ?_, (hgh ()).2⟩
  rw [etFF_iff_spec]
  refine ⟨HasRingHomProperty.Spec_iff.2 (hgh ()).1, ⟨fun p ↦ ?_⟩⟩
  obtain ⟨i, v, hv⟩ := hcov p
  cases i
  exact ⟨v, hv⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleLocal_property_calculus_rules : (∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ V g, P V g) → Loc U P) ∧ (∀ (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P → (∀ V g, P V g → Q V g) → Loc U Q) ∧ (∀ (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P → Loc U Q → Loc U fun V g => P V g ∧ Q V g) ∧ (∀ (U W : Scheme.{0}) (k : W ⟶ U) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P → Loc W fun V g => P V (g ≫ k)) ∧ (∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U (fun V g => Loc V fun W k => P W (k ≫ g)) → Loc U P) ∧ (∀ (U : Scheme.{0}) (ι : Type) [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ i, Loc U (P i)) → Loc U fun V g => ∀ i, P i V g) ∧ (∀ (U : Scheme.{0}) [IsEmpty U] (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P) := by
  first | (exact @GlobalTheory.EtC.loc_calculus) | (exact GlobalTheory.EtC.loc_calculus) | (intros; apply GlobalTheory.EtC.loc_calculus  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover : ∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), P V g → P W (k ≫ g)) → (Loc U P ↔ ∀ x : U, ∃ (V : Scheme.{0}) (g : V ⟶ U), IsAffine V ∧ Etale g ∧ x ∈ Set.range g ∧ P V g) := by
  first | (exact @GlobalTheory.EtC.loc_iff_etale_affine_points) | (exact GlobalTheory.EtC.loc_iff_etale_affine_points) | (intros; apply GlobalTheory.EtC.loc_iff_etale_affine_points  <;> assumption)
end

