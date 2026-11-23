module

public import ReciprocityTheory.DualLattices.UnramifiedCokernelLowerBoundOf
public import ReciprocityTheory.DualLattices.UpSmith
public import ReciprocityTheory.DualLattices.Bundle0004
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0017
public import ReciprocityTheory.DualLattices.Bundle0018

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.IdemGen
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

theorem idemGen : IdemGenStatement := by
  rintro R _ g d P hP ⟨e⟩

  let L : (Fin g → R) →ₗ[R] (Fin d → R) := e.toLinearMap ∘ₗ (mulVecLin P).rangeRestrict
  let T : (Fin d → R) →ₗ[R] (Fin g → R) :=
    (LinearMap.range (mulVecLin P)).subtype ∘ₗ e.symm.toLinearMap
  obtain ⟨M, hLM⟩ : ∃ M : Matrix (Fin d) (Fin g) R, Matrix.toLin' M = L :=
    ⟨_, Matrix.toLin'_toMatrix' L⟩
  obtain ⟨N, hTN⟩ : ∃ N : Matrix (Fin g) (Fin d) R, Matrix.toLin' N = T :=
    ⟨_, Matrix.toLin'_toMatrix' T⟩

  have hPNM : P = N * M := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, hLM, hTN]
    refine LinearMap.ext fun x => ?_
    simp [L, T, Matrix.toLin'_apply]

  have hMP : M * P = M := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, hLM]
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, L, LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe]
    congr 1
    apply Subtype.ext
    simp [Matrix.mulVec_mulVec, hP]

  have hrow : ∀ i, Pᵀ *ᵥ M i = M i := by
    intro i
    funext j
    have h := congrFun (congrFun hMP i) j
    simp only [Matrix.mul_apply] at h
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  refine ⟨fun i => ⟨M i, LinearMap.mem_range.mpr ⟨M i, by rw [Matrix.mulVecLin_apply]; exact hrow i⟩⟩, ?_⟩
  rw [eq_top_iff]
  rintro ⟨w, hw⟩ -
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hw

  have key : mulVecLin Pᵀ v = ∑ i, (Nᵀ *ᵥ v) i • M i := by
    rw [Matrix.mulVecLin_apply, hPNM, Matrix.transpose_mul, ← Matrix.mulVec_mulVec]
    funext j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  refine (Submodule.mem_span_range_iff_exists_fun R).mpr ⟨fun i => (Nᵀ *ᵥ v) i, ?_⟩
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  exact key.symm

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.LenEx
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

theorem lenEx : LenExStatement := by
  intro C _ v R _ _ hv g Ht A B
  classical
  have : IsDomain R := hv.hom_inj.isDomain
  have := ValuationRing.of_integers v hv
  set Mm := LinearMap.range (Matrix.mulVecLin Aᵀ) with hMm
  set N := (LinearMap.range (Matrix.mulVecLin B)).map (Matrix.mulVecLin Ht) with hN
  have hfgM : Mm.FG := by
    rw [hMm, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _
  have hfgN : N.FG := by
    rw [hN, LinearMap.range_eq_map]; exact (Module.Finite.fg_top.map _).map _
  set S := Mm ⊔ N with hS
  have hfgS : S.FG := hfgM.sup hfgN
  have : Module.Finite R S := Module.Finite.iff_fg.2 hfgS
  have : Module.Free R S := L2.SecondCohomologyLattice.free_of_finite_torsionFree S (by
    rintro r ⟨x, hx⟩ hr h
    apply Subtype.ext
    funext i
    have := congrFun (congrArg Subtype.val h) i
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Submodule.coe_zero,
      Pi.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hr)
  set bS := (Module.Free.chooseBasis R S).reindex (Fintype.equivFin _) with hbS
  set e := bS.equivFun with he
  set N' := N.comap S.subtype with hN'
  have hfgN' : N'.FG := by
    apply Submodule.fg_of_fg_map_injective S.subtype S.injective_subtype
    rw [hN', Submodule.map_comap_subtype, inf_eq_right.2 le_sup_right]
    exact hfgN
  set K := N'.map e.toLinearMap with hK
  have hfgK : K.FG := hfgN'.map _
  obtain ⟨n, gK, hgK⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfgK
  have smithGen (b : ℕ) (f : Fin n → Fin b → R) :
      ∃ c : Fin b → R, Nonempty (((Fin b → R) ⧸ Submodule.span R (Set.range f)) ≃ₗ[R]
        ((i : Fin b) → R ⧸ Ideal.span {c i})) := by
    induction b with
    | zero =>
      exact ⟨Fin.elim0, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
    | succ b ih =>
      obtain ⟨i, a, u, s, hu, hau, hs, -, -⟩ := Smith.exists_pivot hv (b := b) f
      obtain ⟨ep⟩ := Smith.pivot_equiv f i a u s hu hau hs
      obtain ⟨c, ⟨er⟩⟩ := ih (fun j => Fin.removeNth i (f j - s j • a • u))
      exact ⟨Fin.cons a c,
        ⟨(ep.trans ((LinearEquiv.refl R _).prodCongr er)).trans (Smith.consEquiv a c)⟩⟩
  obtain ⟨c, ⟨ec⟩⟩ := smithGen _ gK
  refine ⟨∏ i, v (algebraMap R C (c i)), _, c, ⟨?_⟩, rfl⟩
  have h1 : N.comap Mm.subtype = Mm.comap Mm.subtype ⊓ N.comap Mm.subtype := by
    rw [Submodule.comap_subtype_self, top_inf_eq]
  exact (Submodule.quotEquivOfEq _ _ h1).trans ((LinearMap.quotientInfEquivSupQuotient Mm N).trans
    ((Submodule.Quotient.equiv N' K e rfl).trans ((Submodule.quotEquivOfEq _ _ hgK.symm).trans ec)))

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.LenIdBStatement
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

variable {R : Type} [CommRing R] {g m : ℕ}

def inclE (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m) :
    LinearMap.range (Matrix.mulVecLin (εL i)) →ₗ[R] qE εL i j where
  toFun x := ⟨Sum.elim (0 : Fin g → R) (x : Fin g → R), by
    refine ⟨?_, ?_⟩
    · show (Sum.elim (0 : Fin g → R) (x : Fin g → R)) ∘ Sum.inl ∈ LinearMap.range (Matrix.mulVecLin (εL j)ᵀ)
      exact ⟨0, by funext k; simp⟩
    · show (Sum.elim (0 : Fin g → R) (x : Fin g → R)) ∘ Sum.inr ∈ LinearMap.range (Matrix.mulVecLin (εL i))
      exact x.2⟩
  map_add' x y := by ext k; rcases k with k | k <;> simp
  map_smul' c x := by ext k; rcases k with k | k <;> simp

def projE (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m) :
    qE εL i j →ₗ[R] LinearMap.range (Matrix.mulVecLin (εL j)ᵀ) where
  toFun q := ⟨(q : Fin g ⊕ Fin g → R) ∘ Sum.inl, q.2.1⟩
  map_add' x y := rfl
  map_smul' c x := rfl

abbrev sxE (Ht Bt : Matrix (Fin g) (Ix g) R) (εT : Fin m → Matrix (Ix g) (Ix g) R)
    (εL : Fin m → Matrix (Fin g) (Fin g) R) (π : Equiv.Perm (Fin m)) (i : Fin m) :
    Submodule R (qE εL i (π i)) :=
  ((LinearMap.range (Matrix.mulVecLin (εT i))).map (Matrix.mulVecLin (fromRows Ht Bt))).comap
    (qE εL i (π i)).subtype

abbrev yModE (Ht Bt : Matrix (Fin g) (Ix g) R) (εT : Fin m → Matrix (Ix g) (Ix g) R)
    (εL : Fin m → Matrix (Fin g) (Fin g) R) (π : Equiv.Perm (Fin m)) (i : Fin m) :=
  LinearMap.range (Matrix.mulVecLin (εL i)) ⧸ (sxE Ht Bt εT εL π i).comap (inclE εL i (π i))

private theorem fromRows_mulVec_comp_inl (Ht Bt : Matrix (Fin g) (Ix g) R) (w : Ix g → R) :
    (fromRows Ht Bt *ᵥ w) ∘ Sum.inl = Ht *ᵥ w := by
  funext k
  rfl

private theorem fromRows_mulVec_comp_inr (Ht Bt : Matrix (Fin g) (Ix g) R) (w : Ix g → R) :
    (fromRows Ht Bt *ᵥ w) ∘ Sum.inr = Bt *ᵥ w := by
  funext k
  rfl

private theorem coe_inclE_eq_elim_zero (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m)
    (x : LinearMap.range (Matrix.mulVecLin (εL i))) :
    ((inclE εL i j x : qE εL i j) : Fin g ⊕ Fin g → R) =
      Sum.elim (0 : Fin g → R) (x : Fin g → R) := rfl

private theorem coe_projE_eq_comp_inl (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m)
    (q : qE εL i j) :
    ((projE εL i j q : LinearMap.range (Matrix.mulVecLin (εL j)ᵀ)) : Fin g → R) =
      (q : Fin g ⊕ Fin g → R) ∘ Sum.inl := rfl

private theorem projE_inclE_eq_zero (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m)
    (x : LinearMap.range (Matrix.mulVecLin (εL i))) :
    projE εL i j (inclE εL i j x) = 0 := by
  apply Subtype.ext
  funext k
  rfl

private theorem sxE_le_comap_projE (Ht Bt : Matrix (Fin g) (Ix g) R)
    (εT : Fin m → Matrix (Ix g) (Ix g) R)
    (εL : Fin m → Matrix (Fin g) (Fin g) R) (π : Equiv.Perm (Fin m)) (i : Fin m) :
    sxE Ht Bt εT εL π i ≤
      (((LinearMap.range (Matrix.mulVecLin (εT i))).map (Matrix.mulVecLin Ht)).comap
        (LinearMap.range (Matrix.mulVecLin (εL (π i))ᵀ)).subtype).comap (projE εL i (π i)) := by
  intro q hq
  obtain ⟨w, hw, hwq⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hq)
  refine Submodule.mem_comap.mpr (Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨w, hw, ?_⟩))
  rw [Submodule.subtype_apply, coe_projE_eq_comp_inl, Matrix.mulVecLin_apply, ← fromRows_mulVec_comp_inl Ht Bt w]
  rw [Submodule.subtype_apply, Matrix.mulVecLin_apply] at hwq
  rw [hwq]

theorem xModE_len {C : Type} [Field C] {v : Valuation C NNReal} [Algebra R C]
    (hS2 : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (X : Matrix κ κ R),
      HasLen v R ((κ → R) ⧸ LinearMap.range X.mulVecLin) (v (algebraMap R C X.det)))
    (Ht Bt : Matrix (Fin g) (Ix g) R) (εT : Fin m → Matrix (Ix g) (Ix g) R)
    (εL : Fin m → Matrix (Fin g) (Fin g) R) (π : Equiv.Perm (Fin m)) (i : Fin m)
    (hHt : Ht * εT i = (εL (π i))ᵀ * Ht) (hBt : Bt * εT i = εL i * Bt) {y c₂ : NNReal}
    (hy : HasLen v R (yModE Ht Bt εT εL π i) y)
    (hc : HasLen v R (cokE Ht εT εL (π i) i) c₂) :
    HasLen v R (xModE Ht Bt εT εL π i) (y * c₂) := by
  refine hasLen_ext hS2
    (Submodule.mapQ ((sxE Ht Bt εT εL π i).comap (inclE εL i (π i)))
      (sxE Ht Bt εT εL π i) (inclE εL i (π i)) le_rfl)
    (Submodule.mapQ (sxE Ht Bt εT εL π i)
      (((LinearMap.range (Matrix.mulVecLin (εT i))).map (Matrix.mulVecLin Ht)).comap
        (LinearMap.range (Matrix.mulVecLin (εL (π i))ᵀ)).subtype)
      (projE εL i (π i)) (sxE_le_comap_projE Ht Bt εT εL π i))
    ?_ ?_ ?_ hy hc
  · intro a b hab
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at hab
    rw [Submodule.Quotient.eq, Submodule.mem_comap, map_sub]
    exact hab
  · intro z
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    refine ⟨Submodule.Quotient.mk ⟨Sum.elim (z : Fin g → R) (0 : Fin g → R), by
      refine ⟨?_, ?_⟩
      · show (Sum.elim (z : Fin g → R) (0 : Fin g → R)) ∘ Sum.inl ∈
          LinearMap.range (Matrix.mulVecLin (εL (π i))ᵀ)
        exact z.2
      · show (Sum.elim (z : Fin g → R) (0 : Fin g → R)) ∘ Sum.inr ∈
          LinearMap.range (Matrix.mulVecLin (εL i))
        exact ⟨0, by funext k; simp⟩⟩, ?_⟩
    rw [Submodule.mapQ_apply]
    exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)
  · apply le_antisymm
    · intro x hx
      obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hx
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
        projE_inclE_eq_zero]
      exact Submodule.zero_mem _
    · intro x hx
      obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨w, hw, hwq⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hx)
      obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hw
      rw [Submodule.subtype_apply, coe_projE_eq_comp_inl, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply] at hwq
      have hB' : Bt *ᵥ (εT i *ᵥ u) ∈ LinearMap.range (Matrix.mulVecLin (εL i)) :=
        ⟨Bt *ᵥ u, by rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBt]⟩
      have hq2 : (q : Fin g ⊕ Fin g → R) ∘ Sum.inr ∈ LinearMap.range (Matrix.mulVecLin (εL i)) := q.2.2
      have hr : (q : Fin g ⊕ Fin g → R) ∘ Sum.inr - Bt *ᵥ (εT i *ᵥ u) ∈
          LinearMap.range (Matrix.mulVecLin (εL i)) := Submodule.sub_mem _ hq2 hB'
      refine LinearMap.mem_range.mpr ⟨Submodule.Quotient.mk ⟨_, hr⟩, ?_⟩
      rw [Submodule.mapQ_apply, eq_comm, Submodule.Quotient.eq]
      refine Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨(εT i).mulVecLin u, ⟨u, rfl⟩, ?_⟩)
      rw [Submodule.subtype_apply, Submodule.coe_sub, coe_inclE_eq_elim_zero, Matrix.mulVecLin_apply,
        Matrix.mulVecLin_apply]
      funext k
      rcases k with k | k
      · have hF := congrFun (fromRows_mulVec_comp_inl Ht Bt (εT i *ᵥ u)) k
        have hk := congrFun hwq k
        simp only [Function.comp_apply] at hF hk
        rw [Pi.sub_apply, hF, Sum.elim_inl, Pi.zero_apply, sub_zero]
        exact hk
      · have hF := congrFun (fromRows_mulVec_comp_inr Ht Bt (εT i *ᵥ u)) k
        simp only [Function.comp_apply] at hF
        rw [Pi.sub_apply, hF, Sum.elim_inr]
        show _ = _ - (((q : Fin g ⊕ Fin g → R) ∘ Sum.inr - Bt *ᵥ (εT i *ᵥ u)) k)
        rw [Pi.sub_apply, Function.comp_apply, sub_sub_cancel]

def LenIdBStatement : Prop :=
  ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → ∀ (g m : ℕ) (Ht Bt : Matrix (Fin g) (Ix g) R) (E : Matrix (Ix g) (Ix g) R)
    (cp : R), cp ≠ 0 → IsUnit E.det → Btᵀ * Ht - Htᵀ * Bt = cp • E →
    ∀ (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)), (∀ i, π (π i) = i) →
    (∀ i j, εT i * εT j = if i = j then εT i else 0) → ∑ i, εT i = 1 →
    (∀ i j, εL i * εL j = if i = j then εL i else 0) → ∑ i, εL i = 1 →
    (∀ i, Ht * εT i = (εL (π i))ᵀ * Ht) → (∀ i, Bt * εT i = εL i * Bt) →
    (∀ i, (εT i)ᵀ * E = E * εT (π i)) →
    ∀ (i : Fin m) (d : ℕ), Nonempty (LinearMap.range (Matrix.mulVecLin (εL i)) ≃ₗ[R] (Fin d → R)) →
    ∀ c₁ : NNReal, HasLen v R (cokE Ht εT εL i (π i)) c₁ →
      ∃ y : NNReal, HasLen v R (yModE Ht Bt εT εL π i) y ∧ y * c₁ = v (algebraMap R C cp) ^ d

theorem lenId_of
    (hS2 : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
      v.Integers R → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (X : Matrix κ κ R),
      HasLen v R ((κ → R) ⧸ LinearMap.range X.mulVecLin) (v (algebraMap R C X.det)))
    (hB : LenIdBStatement) : LenIdStatement := by
  intro C _ v R _ _ hv g m Ht Bt E cp hcp hE hform εT εL π hπ hεT hsumT hεL hsumL hHt hBt hεE i d hd
    c₁ c₂ hc₁ hc₂
  obtain ⟨y, hy, hyc⟩ := hB C v R hv g m Ht Bt E cp hcp hE hform εT εL π hπ hεT hsumT hεL hsumL hHt hBt
    hεE i d hd c₁ hc₁
  refine ⟨y * c₂, xModE_len (hS2 C v R hv) Ht Bt εT εL π i (hHt i) (hBt i) hy hc₂, ?_⟩
  rw [mul_right_comm, hyc]

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.NsetExpInjectiveSurjective
section
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

structure ATower (R₀ : Type u) [CommRing R₀] (p : ℕ) where
  O : LAlg R₀
  R' : ℕ → LAlg R₀
  R : ℕ → LAlg R₀
  π : ∀ n, LHom (R' n) (R n)
  q : ∀ n, LHom O (R n)
  ξ : ∀ n, (R' n : Type u)
  surj : ∀ n, Function.Surjective (π n).1
  ker_eq : ∀ n, RingHom.ker (π n).1 = Ideal.span {ξ n}
  ξ_sq : ∀ n, ξ n * ξ n = 0
  ann : ∀ n (a : (R' n : Type u)), a * ξ n = 0 → a ∈ Ideal.span {ξ n}
  char : ∀ n, ((p ^ (n + 1) : ℕ) : (R' n : Type u)) = 0
  sep : ∀ a : (O : Type u), (∀ n, (q n).1 a = 0) → a = 0
  c : (O : Type u)
  cp : ∀ n, (R' n : Type u)
  cp_spec : ∀ n, (π n).1 (cp n) = (q n).1 c
  zh : ∀ n, (R' n : Type u)ˣ
  zh_pow : ∀ n, (zh n : (R' n : Type u)) ^ (p ^ (n + 1)) = 1 + cp n * ξ n
  ζ : ∀ n, (O : Type u)ˣ
  ζ_spec : ∀ n, (q n).1 (ζ n : (O : Type u)) = (π n).1 (zh n : (R' n : Type u))

variable {R₀ : Type u} [CommRing R₀]

lemma ATower.ξ_mem {p : ℕ} (Tw : ATower R₀ p) (n : ℕ) : Tw.ξ n ∈ (Tw.π n).ker := by
  rw [LHom.ker, Submodule.restrictScalars_mem, Tw.ker_eq]
  exact Ideal.subset_span (Set.mem_singleton _)

lemma ATower.sqZero {p : ℕ} (Tw : ATower R₀ p) (n : ℕ) : (Tw.π n).SqZero := ⟨Tw.surj n, by
    rw [Tw.ker_eq, sq, Ideal.span_singleton_mul_span_singleton, Tw.ξ_sq, Ideal.span_singleton_eq_bot]⟩

def NsetExpInjectiveSurjective (B : BX R₀) {p : ℕ} (Tw : ATower R₀ p) : Prop :=
  ∀ (Dp : ∀ n, DualPair (Tw.R n)) (ι : Type) (τ : ι → ℕ → B.G Tw.O)
    (E : ι → ι → (Tw.O : Type u)) (ht : ι → B.gg →ₗ[R₀] (Tw.O : Type u))
    (bt : ι → B.gg ⊗[R₀] (Tw.O : Type u)),
    (∀ i j n, ∃ k : ℕ, (Tw.q n).1 (E i j) = k ∧
      B.IsPairing (p ^ (n + 1)) (τ i n) (τ j n) (Tw.ζ n ^ k)) →
    (∀ i n, B.IsHeight (Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n))
      ((Tw.q n).1.toLinearMap ∘ₗ ht i)) →
    (∀ i n, ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)),
      B.map (Tw.π n) th = B.map (Tw.q n) (τ i n) ∧
      (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
        (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) ∧
      LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w =
        LinearMap.lTensor B.gg (Tw.q n).1.toLinearMap (bt i)) →
    ∀ i j, Tw.c * E i j = B.ev (ht j) (bt i) - B.ev (ht i) (bt j)

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.SumLatInvMulVec
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {v : Valuation C NNReal}

def phiMap {n s h : ℕ} (A : Fin n → Matrix (Fin s) (Fin h) C) (w : Fin n × Fin h → C) :
    Fin n × Fin s → C := fun y => ∑ l, A y.1 y.2 l * w (y.1, l)

lemma sumLat_inv_mulVec {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) (w : Fin n × Fin s → C)
    (τ : Fin n) (i : Fin s) :
    ((sumLat Mτ).B⁻¹ *ᵥ w) (τ, i) = ((Mτ τ).B⁻¹ *ᵥ fun j => w (τ, j)) i := by
  classical
  unfold sumLat
  simp only
  have hinv : (reindex (Equiv.prodComm (Fin s) (Fin n)) (Equiv.prodComm (Fin s) (Fin n))
      (blockDiagonal fun τ ↦ (Mτ τ).B))⁻¹ =
      reindex (Equiv.prodComm (Fin s) (Fin n)) (Equiv.prodComm (Fin s) (Fin n))
        (blockDiagonal fun τ ↦ (Mτ τ).B⁻¹) := by
    refine Matrix.inv_eq_left_inv ?_
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]
    have h1 : (fun τ ↦ (Mτ τ).B⁻¹ * (Mτ τ).B) = 1 :=
      funext fun τ ↦ Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (Mτ τ).det_ne)
    rw [h1, Matrix.blockDiagonal_one, Matrix.submatrix_one_equiv]
  rw [hinv]
  simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma v_mulVec_le {m k : Type} [Fintype k] (P : Matrix m k C) (x : k → C)
    (hP : ∀ i j, v (P i j) ≤ 1) (hx : ∀ j, v (x j) ≤ 1) (i : m) : v ((P *ᵥ x) i) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  refine v.map_sum_le fun j _ ↦ ?_
  rw [map_mul]
  exact mul_le_one₀ (hP i j) (zero_le) (hx j)

theorem polyVec_mem {n h : ℕ} {a : Fin n → C} (F : Lat v (Fin n × Fin h))
    (hF : F.B = freeMat a h) (p : Polynomial C) (hp : ∀ k, v (p.coeff k) ≤ 1)
    (hdeg : p.natDegree < n) (u : Fin h → C) (hu : ∀ l, v (u l) ≤ 1) :
    (fun y : Fin n × Fin h => p.eval (a y.1) * u y.2) ∈ F.pts := by
  classical
  refine ⟨fun y ↦ p.coeff (y.1 : ℕ) * u y.2, ?_, ?_⟩
  · intro j
    rw [map_mul]
    exact mul_le_one₀ (hp _) (zero_le) (hu _)
  · funext y
    rw [hF]
    simp only [Matrix.mulVec, dotProduct, freeMat, Matrix.of_apply, Fintype.sum_prod_type,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Polynomial.eval_eq_sum_range' hdeg, Finset.sum_mul, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun k _ ↦ by ring

end ReciprocityTheory.PGsh.Up
end
end

