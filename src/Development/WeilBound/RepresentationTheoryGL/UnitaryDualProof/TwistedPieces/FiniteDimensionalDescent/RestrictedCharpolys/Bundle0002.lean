module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocalContinuity.LocalDescentHolds
public import GroundTheory.AutomorphicForms.ContragredientTranspose.MatrixSimilarity

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.ContinuousEF
section
noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Restr.PphiB

open PositivityTheory.RgUd.TP.Desc.Restr PositivityTheory.RgUd.TP.Desc.Restr.PphiA

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p c d : ℕ} [Fact p.Prime] [CharP k p] (B : FB k (p ^ c) d) {n : ℕ}

abbrev ix (r : Fin (n * d)) : Fin n × Fin d := finProdFinEquiv.symm r

def eF (v : Fin n → k) : Fin (n * d) → k := fun r => B.cF (v (ix r).1) (ix r).2

def eI (w : Fin (n * d) → k) : Fin n → k := fun i => ∑ j, w (finProdFinEquiv (i, j)) ^ p ^ c * B.β j

def φM (x : Matrix (Fin n) (Fin n) k) : Matrix (Fin (n * d)) (Fin (n * d)) k :=
  fun r s => B.cF (x (ix r).1 (ix s).1 * B.β (ix s).2) (ix r).2

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem eI_eF (v : Fin n → k) : eI B (eF B v) = v := by
  funext i
  simp only [eI, eF, ix, Equiv.symm_apply_apply]
  exact B.recon (v i)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem eF_eI (w : Fin (n * d) → k) : eF B (eI B w) = w := by
  funext r
  have h := B.uniq (fun j => w (finProdFinEquiv ((ix r).1, j)))
  simp only [eF, eI]
  rw [h]
  exact congrArg w (finProdFinEquiv.apply_symm_apply r)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem eF_add (v v' : Fin n → k) : eF B (v + v') = eF B v + eF B v' := by
  funext r; simp [eF]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem key (x : Matrix (Fin n) (Fin n) k) (v : Fin n → k) : eF B (x *ᵥ v) = φM B x *ᵥ eF B v := by
  funext r
  simp only [eF, φM, mulVec, dotProduct]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_apply]
  rw [← (finProdFinEquiv : Fin n × Fin d ≃ Fin (n * d)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i' _ => ?_
  simp only [ix, Equiv.symm_apply_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← B.recon (v i'), Finset.mul_sum, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [show x (finProdFinEquiv.symm r).1 i' * (B.cF (v i') j' ^ p ^ c * B.β j') =
      B.cF (v i') j' ^ p ^ c * (x (finProdFinEquiv.symm r).1 i' * B.β j') by ring, fb_smul]
  ring

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem eF_surj : Function.Surjective (eF B (n := n)) := fun w => ⟨eI B w, eF_eI B w⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem ext_of_eF {M M' : Matrix (Fin (n * d)) (Fin (n * d)) k} (h : ∀ v, M *ᵥ eF B v = M' *ᵥ eF B v) : M = M' := by
  have hw : ∀ w, M *ᵥ w = M' *ᵥ w := by
    intro w
    obtain ⟨v, rfl⟩ := eF_surj B w
    exact h v
  ext i j
  have h1 := congrFun (hw (Pi.single j 1)) i
  simpa [mulVec_single_one] using h1

def φ : Matrix (Fin n) (Fin n) k →+* Matrix (Fin (n * d)) (Fin (n * d)) k where
  toFun := φM B
  map_one' := ext_of_eF B fun v => by rw [← key, one_mulVec, one_mulVec]
  map_mul' x y := ext_of_eF B fun v => by rw [← key, ← mulVec_mulVec, ← mulVec_mulVec, ← key, ← key, mulVec_mulVec]
  map_zero' := ext_of_eF B fun v => by
    rw [← key, zero_mulVec, zero_mulVec]; funext r; simp [eF]
  map_add' x y := ext_of_eF B fun v => by rw [← key, add_mulVec, add_mulVec, eF_add, key, key]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem φ_apply_mulVec (x : Matrix (Fin n) (Fin n) k) (v : Fin n → k) : φ B x *ᵥ eF B v = eF B (x *ᵥ v) :=
  (key B x v).symm

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem φ_inj : Function.Injective (φ B (n := n)) := by
  intro x y h
  have hv : ∀ v, x *ᵥ v = y *ᵥ v := by
    intro v
    have h1 := φ_apply_mulVec B x v
    rw [h, φ_apply_mulVec] at h1
    have h2 := congrArg (eI B) h1
    rw [eI_eF, eI_eF] at h2
    exact h2.symm
  ext i j
  have h1 := congrFun (hv (Pi.single j 1)) i
  simpa [mulVec_single_one] using h1

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem φ_scal (a : k) : φ B (algebraMap k (Matrix (Fin n) (Fin n) k) (a ^ p ^ c)) = algebraMap k _ a := by
  apply ext_of_eF B
  intro v
  rw [φ_apply_mulVec]
  funext r
  simp [algebraMap_eq_diagonal, mulVec_diagonal, eF, fb_smul]

def e : (Fin n → k) ≃+ (Fin (n * d) → k) where
  toFun := eF B
  invFun := eI B
  left_inv := eI_eF B
  right_inv := eF_eI B
  map_add' := eF_add B

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem continuous_eF : Continuous (eF B (n := n)) := by
  refine continuous_pi fun r => ?_
  exact (continuous_apply _).comp (B.cont.comp (continuous_apply _))

theorem continuous_eI : Continuous (eI B (n := n)) := by
  unfold eI; fun_prop

theorem continuous_φ : Continuous (φ B (n := n)) := by
  show Continuous (φM B)
  unfold φM
  refine continuous_pi fun r => continuous_pi fun s => ?_
  have hx : Continuous fun a : Matrix (Fin n) (Fin n) k => a (ix r).1 (ix s).1 * B.β (ix s).2 := by
    fun_prop
  exact (continuous_apply _).comp (B.cont.comp hx)

def ψ (M : Matrix (Fin (n * d)) (Fin (n * d)) k) : Matrix (Fin n) (Fin n) k :=
  fun i i' => eI B (M *ᵥ eF B (Pi.single i' 1)) i

theorem ψ_φ (x : Matrix (Fin n) (Fin n) k) : ψ B (φ B x) = x := by
  funext i i'
  simp [ψ, φ_apply_mulVec, eI_eF, mulVec_single_one]

theorem continuous_ψ : Continuous (ψ B (n := n)) := by
  unfold ψ
  refine continuous_pi fun i => continuous_pi fun i' => ?_
  exact (continuous_apply i).comp ((continuous_eI B).comp (continuous_id.matrix_mulVec continuous_const))

theorem φ_emb : Topology.IsClosedEmbedding (φ B (n := n)) :=
  Function.LeftInverse.isClosedEmbedding (ψ_φ B) (continuous_ψ B) (continuous_φ B)

end PositivityTheory.RgUd.TP.Desc.Restr.PphiB
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.IsClosedCharpolyEq
section
noncomputable section

open Matrix Polynomial Set

namespace PositivityTheory.RgUd.TP.Desc.Restr.Ppull2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isClosed_charpoly_eq {N : ℕ} (c : k[X]) : IsClosed {A : Matrix (Fin N) (Fin N) k | A.charpoly = c} := by
  have hc : ∀ (i : ℕ) (A : Matrix (Fin N) (Fin N) k), A.charpoly.coeff i =
      MvPolynomial.eval (fun p : Fin N × Fin N => A p.1 p.2)
        (MvPolynomial.map (Int.castRingHom k) ((Matrix.charpoly.univ ℤ (Fin N)).coeff i)) := by
    intro i A
    have h := Matrix.charpoly.univ_map_eval₂Hom (Fin N) (Int.castRingHom k) (fun p : Fin N × Fin N => A p.1 p.2)
    have hA : Matrix.of (Function.curry (fun p : Fin N × Fin N => A p.1 p.2)) = A := by
      ext a b
      rfl
    rw [hA] at h
    rw [← h, Polynomial.coeff_map, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq_eval_map]
  have hset : {A : Matrix (Fin N) (Fin N) k | A.charpoly = c} = ⋂ i : ℕ, {A | A.charpoly.coeff i = c.coeff i} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact ⟨fun h i => by rw [h], fun h => Polynomial.ext h⟩
  rw [hset]
  refine isClosed_iInter fun i => ?_
  simp only [hc]
  exact isClosed_eq ((MvPolynomial.continuous_eval _).comp
    (continuous_pi fun p => continuous_id.matrix_elem p.1 p.2)) continuous_const

theorem conj_mem_Bz {n : ℕ} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {g : GL (Fin n) k} (hg : g ∈ Gz Z)
    {x : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z) : g.val * x * g⁻¹.val ∈ Bz Z := by
  have hg' : ∀ a ∈ Z, a * g.val = g.val * a := hg
  have hx' : ∀ a ∈ Z, a * x = x * a := hx
  show ∀ a ∈ Z, a * (g.val * x * g⁻¹.val) = g.val * x * g⁻¹.val * a
  intro a ha
  have hi : a * g⁻¹.val = g⁻¹.val * a := by
    have e := congrArg (fun m => g⁻¹.val * m * g⁻¹.val) (hg' a ha)
    simp only [mul_assoc, Units.mul_inv, mul_one, Units.inv_mul_cancel_left] at e
    exact e.symm
  calc a * (g.val * x * g⁻¹.val) = a * g.val * x * g⁻¹.val := by simp only [mul_assoc]
    _ = g.val * (a * x) * g⁻¹.val := by rw [hg' a ha]; simp only [mul_assoc]
    _ = g.val * x * (a * g⁻¹.val) := by rw [hx' a ha]; simp only [mul_assoc]
    _ = g.val * x * g⁻¹.val * a := by rw [hi]; simp only [mul_assoc]

theorem pullPieces : PullPieces k := by
  unfold PullPieces
  intro n N q Z Z' φ e hZ hD χ
  have hBz : ∀ {m : ℕ} (S : Subalgebra k (Matrix (Fin m) (Fin m) k)), IsClosed (Bz S) := by
    intro m S
    have hS : Bz S = ⋂ a ∈ S, {x : Matrix (Fin m) (Fin m) k | a * x = x * a} := by
      ext x
      simp only [Set.mem_iInter]
      rfl
    rw [hS]
    exact isClosed_biInter fun a _ =>
      isClosed_eq (continuous_const.matrix_mul continuous_id) (continuous_id.matrix_mul continuous_const)
  obtain ⟨P, hP0, hP⟩ : ∃ P : k[X], P ≠ 0 ∧
      ∀ x : Matrix (Fin n) (Fin n) k, x.charpoly = χ → aeval (φ x) P = 0 := by
    by_cases hχ : χ = 0
    · exact ⟨1, one_ne_zero, fun x hx => absurd (hx.trans hχ) (Matrix.charpoly_monic x).ne_zero⟩
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      refine ⟨1, one_ne_zero, fun x _ => ?_⟩
      ext i j
      exact i.elim0
    · obtain ⟨hq, -⟩ := Ppull2A.choose_zero hD hN
      refine ⟨expand k q χ, ?_, fun x hx => Ppull2A.aeval_expand hD hN χ x (hx ▸ Matrix.aeval_self_charpoly x)⟩
      rwa [Ne, Polynomial.expand_eq_zero (by omega)]
  obtain ⟨l, hnd, hl⟩ := Ppull2A.finite_charpoly N P hP0
  refine ⟨l, fun h => ?_⟩
  choose M F' hP' hG' using h
  unfold IsPieces at hP'
  let L : Fin l.length → k[X] := fun j => l[j.val]'j.isLt
  have hLm : ∀ j, L j ∈ l := fun j => List.getElem_mem j.isLt
  let mj : Fin l.length → ℕ := fun j => M (L j) (hLm j)
  let G : (Σ j : Fin l.length, Fin (mj j)) → Set (Matrix (Fin n) (Fin n) k) := fun s =>
    {x | x ∈ Bz Z ∧ x.charpoly = χ ∧ (φ x).charpoly = L s.1 ∧ φ x ∈ F' (L s.1) (hLm s.1) s.2}
  have memG : ∀ s x, x ∈ G s ↔ (x ∈ Bz Z ∧ x.charpoly = χ ∧ (φ x).charpoly = L s.1 ∧
      φ x ∈ F' (L s.1) (hLm s.1) s.2) := fun _ _ => Iff.rfl
  have hGc : ∀ s, IsClosed (G s) ∧ G s ⊆ Bz Z ∧
      ∀ g ∈ Gz Z, ∀ x ∈ G s, (g : Matrix (Fin n) (Fin n) k) * x * ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈ G s := by
    rintro ⟨j, i⟩
    refine ⟨?_, fun x hx => ((memG _ x).1 hx).1, ?_⟩
    · exact (hBz Z).inter ((isClosed_charpoly_eq χ).inter
        (((isClosed_charpoly_eq _).preimage hD.emb.continuous).inter
          (((hP' _ _).1 i).1.preimage hD.emb.continuous)))
    · intro g hg x hx
      obtain ⟨hxB, hxc, hxφc, hxF⟩ := (memG _ x).1 hx
      let g' : GL (Fin N) k := Units.map (φ : Matrix (Fin n) (Fin n) k →* Matrix (Fin N) (Fin N) k) g
      have hg' : g' ∈ Gz Z' := (hD.gz g').2 ⟨g, hg, rfl⟩
      have hφ : φ (g.val * x * g⁻¹.val) = g'.val * φ x * g'⁻¹.val := by
        rw [map_mul, map_mul]
        rfl
      refine (memG _ _).2 ⟨conj_mem_Bz hg hxB, ?_, ?_, ?_⟩
      · rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj]
        exact hxc
      · show (φ (g.val * x * g⁻¹.val)).charpoly = _
        rw [hφ, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
        exact hxφc
      · show φ (g.val * x * g⁻¹.val) ∈ _
        rw [hφ]
        exact ((hP' _ _).1 i).2.2 g' hg' _ hxF
  have hGd : ∀ s s', s ≠ s' → Disjoint (G s) (G s') := by
    rintro ⟨j, i⟩ ⟨j', i'⟩ hne
    rw [Set.disjoint_left]
    intro x hx1 hx2
    obtain ⟨-, -, hc1, hF1⟩ := (memG _ x).1 hx1
    obtain ⟨-, -, hc2, hF2⟩ := (memG _ x).1 hx2
    by_cases hj : j = j'
    · subst hj
      have hi : i ≠ i' := fun h => hne (by rw [h])
      exact Set.disjoint_left.1 ((hP' _ _).2.1 i i' hi) hF1 hF2
    · apply hj
      have hL : L j = L j' := hc1.symm.trans hc2
      exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 hL)
  have hGcov : ∀ x ∈ Bz Z, x.charpoly = χ → ∃ s, x ∈ G s := by
    intro x hx hc
    obtain ⟨j0, hj0, hj0e⟩ := List.getElem_of_mem (hl (φ x) (hP x hc))
    let j : Fin l.length := ⟨j0, hj0⟩
    have hxB' : φ x ∈ Bz Z' := by
      rw [hD.cen]
      exact ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := (hP' (L j) (hLm j)).2.2 (φ x) hxB' hj0e.symm
    exact ⟨⟨j, i⟩, (memG _ x).2 ⟨hx, hc, hj0e.symm, hi⟩⟩
  have hGg : ∀ s, Good Z (G s) := by
    rintro ⟨j, i⟩
    have hg := hG' (L j) (hLm j) i
    unfold Good at hg ⊢
    rcases hg with ⟨c', hc', hnil⟩ | ⟨N', S, hS, hmu, hV⟩
    · have hcc : c' ∈ φ '' (Z : Set (Matrix (Fin n) (Fin n) k)) := by
        rw [← hD.carrier]
        exact hc'
      obtain ⟨c, hc, rfl⟩ := hcc
      refine Or.inl ⟨c, hc, fun x hx => ?_⟩
      obtain ⟨m, hm⟩ := hnil (φ x) ((memG _ x).1 hx).2.2.2
      exact ⟨m, hD.inj (by rw [map_pow, map_sub, hm, map_zero])⟩
    · refine Or.inr ⟨N', S, hS, by rw [← hD.mu]; exact hmu, fun hv =>
        Ppull2B.fibVan_pull hD _ _ (fun x hx => ((memG _ x).1 hx).2.2.2) (hV hv)⟩
  refine ⟨∑ j, mj j, fun t => G (finSigmaFinEquiv.symm t), ?_, fun t => hGg _⟩
  unfold IsPieces
  refine ⟨fun t => hGc _, fun t t' htt => hGd _ _ (fun h => htt (finSigmaFinEquiv.symm.injective h)), ?_⟩
  intro x hx hc
  obtain ⟨s, hs⟩ := hGcov x hx hc
  exact ⟨finSigmaFinEquiv s, by simpa using hs⟩

end PositivityTheory.RgUd.TP.Desc.Restr.Ppull2
end
end

