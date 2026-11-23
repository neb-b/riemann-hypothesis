module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0046

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.HolEq
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.holEq :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (N : Type) [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (τ : E →+* ℂ) (L : Lie E a →ₗ[ℝ] N) (x : Matrix (Fin a) (Fin a) ℂ),
      hol τ L x = (1 / 2 : ℂ) • (L (toL (x.map (atEmb τ))) - Complex.I • L (toL ((Complex.I • x).map (atEmb τ)))) := by
  intro E _ _ _ a N _ _ _ _ τ L x
  let L' : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] N := L
  have hsum : ∀ y : Matrix (Fin a) (Fin a) ℂ,
      L' (y.map (atEmb τ)) = ∑ i, ∑ j, L' (Matrix.single i j (atEmb τ (y i j))) := fun y => by
    conv_lhs => rw [Matrix.matrix_eq_sum_single (y.map (atEmb τ))]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Matrix.map_apply]
  have hL : ∀ (i j : Fin a) (w : ℂ), L' (Matrix.single i j (atEmb τ w)) =
      (w.re : ℂ) • L' (Matrix.single i j (atEmb τ 1)) +
        (w.im : ℂ) • L' (Matrix.single i j (atEmb τ Complex.I)) := fun i j w => by
    rw [atEmb_eq τ w, Matrix.single_add, ← Matrix.smul_single, ← Matrix.smul_single, map_add (f := _), map_smul, map_smul,
      ← algebraMap_smul ℂ w.re, ← algebraMap_smul ℂ w.im]
    rfl
  change ∑ i, ∑ j, x i j • ((1 / 2 : ℂ) • (L' (Matrix.single i j (atEmb τ 1)) -
      Complex.I • L' (Matrix.single i j (atEmb τ Complex.I)))) =
    (1 / 2 : ℂ) • (L' (x.map (atEmb τ)) - Complex.I • L' ((Complex.I • x).map (atEmb τ)))
  rw [hsum, hsum]
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, hL i j (x i j), hL i j (Complex.I * x i j)]
  generalize x i j = c
  conv_lhs => rw [← Complex.re_add_im c]
  simp only [Complex.I_mul_re, Complex.I_mul_im, Complex.ofReal_neg]
  match_scalars
  · ring
  · linear_combination (-(c.im : ℂ) / 2) * Complex.I_mul_I
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.HomId
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.homId :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (L : Lie E a →ₗ[ℝ] Module.End ℂ M) (q : ℕ) (ω : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M),
      dCo L ω = 0 → InfEq L ω → ∀ (X : Matrix (Fin a) (Fin a) (Cinf E)) (Y : Fin (q + 1) → Herm E a),
        ∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • (L (toL (Y i).1) (ω (Matrix.vecCons (hp (toL X)) (i.removeNth Y))) -
          ω (Matrix.vecCons (hp (toL ((Y i).1 * X - X * (Y i).1))) (i.removeNth Y))) = L (toL X) (ω Y) := by
  intro E _ _ _ a M _ _ _ _ L q ω hd hinf X Y
  let Z : Matrix (Fin a) (Fin a) (Cinf E) := (1 / 2 : ℝ) • (X - star X)
  have hZ : star Z = -Z := by
    simp only [Z]
    rw [star_smul, star_sub, star_star, star_trivial, ← smul_neg, neg_sub]
  have hX : toL X = toL (hp (toL X)).1 + toL Z := by
    have h : X = (hp (toL X)).1 + Z := by
      rw [hp_val]; simp only [Z]; module
    exact congrArg toL h
  have hb : ∀ U : Herm E a, hp (toL (U.1 * X - X * U.1)) = -brH Z hZ U := by
    intro U
    apply Subtype.ext
    have h : star U.1 = U.1 := U.2
    rw [hp_val]
    change _ = -(Z * U.1 - U.1 * Z)
    simp only [Z, star_sub, star_mul, h, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub]
    module
  have h1 := dCo_cons (L := L) ω (hp (toL X)) Y
  rw [hd, AlternatingMap.zero_apply, eq_comm, sub_eq_zero, dCo_apply] at h1
  rw [congrArg L hX, map_add (f := _), LinearMap.add_apply, h1, hinf Z hZ Y, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : ω (Matrix.vecCons (-brH Z hZ (Y i)) (i.removeNth Y)) =
      -ω (Matrix.vecCons (brH Z hZ (Y i)) (i.removeNth Y)) := by
    rw [← AlternatingMap.curryLeft_apply_apply, ← AlternatingMap.curryLeft_apply_apply, map_neg,
      AlternatingMap.neg_apply]
  rw [hb, h2, sub_neg_eq_add, smul_add, ← Fin.insertNth_removeNth, AlternatingMap.map_insertNth,
    AlternatingMap.curryLeft_apply_apply]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.KCurve
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.kCurve :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Z : Matrix (Fin a) (Fin a) (Cinf E)), star Z = -Z →
      ∃ k : ℝ → Kinf E a, k 0 = 1 ∧ HasDerivAt (fun t => toL (k t).1) (toL Z) 0 := by
  intro E _ _ _ a Z hZ
  open scoped Matrix.Norms.Operator in
  have hs : ∀ t : ℝ, star (NormedSpace.exp (t • Z)) = NormedSpace.exp (-(t • Z)) := fun t => by
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, ← Matrix.star_eq_conjTranspose, star_smul,
      star_trivial, hZ, smul_neg]
  have hm : ∀ t : ℝ, NormedSpace.exp (t • Z) ∈ unitary (Matrix (Fin a) (Fin a) (Cinf E)) := fun t => by
    rw [Unitary.mem_iff, hs, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_left,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_right]
    simp
  refine ⟨fun t => ⟨NormedSpace.exp (t • Z), hm t⟩, Subtype.ext (by simp), ?_⟩
  open scoped Matrix.Norms.Operator in
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z 0
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.LowLine
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem weight_operator_commutator_multiGl {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (F : ι → Fin n → Fin n → Module.End ℂ V) (hF : IsMultiGl F) (t : ι) (i j : Fin n) (x : V) :
    (∑ s, ∑ a : Fin n, ((a : ℕ) : ℂ) • F s a a) (F t i j x) =
      F t i j ((∑ s, ∑ a : Fin n, ((a : ℕ) : ℂ) • F s a a) x) +
        (((i : ℕ) : ℂ) - ((j : ℕ) : ℂ)) • F t i j x := by
  classical
  obtain ⟨hgl, hcomm⟩ := hF
  have key : ∀ s (a : Fin n), F s a a (F t i j x) = F t i j (F s a a x) +
      (if s = t then ((if a = i then F t a j x else 0) - (if j = a then F t i a x else 0)) else 0) := by
    intro s a
    by_cases hst : s = t
    · subst hst
      rw [if_pos rfl]
      have h1 := congrArg (fun f : Module.End ℂ V => f x) (hgl s a a i j)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1
      have h2 : (if a = i then F s a j x else 0) - (if j = a then F s i a x else 0) =
          (if a = i then F s a j else 0) x - (if j = a then F s i a else 0) x := by
        split_ifs <;> simp
      rw [h2, ← h1]
      abel
    · rw [if_neg hst]
      have h1 := congrArg (fun f : Module.End ℂ V => f x) (hcomm s t hst a a i j)
      simp only [Module.End.mul_apply] at h1
      rw [h1, add_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, key, smul_add, Finset.sum_add_distrib,
    map_sum, map_smul]
  congr 1
  simp [smul_ite, smul_sub, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.sum_ite_irrel, sub_smul]

theorem UpperTheory.V.AlgRepEndIrreducible.lowLine :
    ∀ (ι V : Type) [Fintype ι] [AddCommGroup V] [Module ℂ V] (n : ℕ) (F : ι → Fin n → Fin n → Module.End ℂ V), IsMultiGl F → ∀ (ν : ι → Fin n → ℂ) (v : V), (∀ t, Formalism.REAL.IsHW (F t) (ν t) v) →
      ∀ w ∈ low F v, (∀ t k, F t k k w = ν t k • w) → ∃ c : ℂ, w = c • v := by
  intro ι V _ _ _ n F hF ν v hv w hw hwν
  classical
  set H : Module.End ℂ V := ∑ s, ∑ a : Fin n, ((a : ℕ) : ℂ) • F s a a with hH
  set l0 : ℂ := ∑ s, ∑ a : Fin n, ((a : ℕ) : ℂ) * ν s a with hl0
  have hHx : ∀ x : V, (∀ s k, F s k k x = ν s k • x) → H x = l0 • x := by
    intro x hx
    simp only [hH, hl0, LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul, Finset.sum_smul]
  have hsh : ∀ t (i j : Fin n) (μ : ℂ) (x : V), H x = μ • x →
      H (F t i j x) = (μ + (((i : ℕ) : ℂ) - ((j : ℕ) : ℂ))) • F t i j x := by
    intro t i j μ x hx
    rw [hH, weight_operator_commutator_multiGl F hF t i j x, ← hH, hx, map_smul, add_smul]
  have hdist : ∀ i j : Fin n, j < i → ∃ d : ℕ, ((i : ℕ) : ℂ) - ((j : ℕ) : ℂ) = (d : ℂ) + 1 := by
    intro i j hji
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (show (j : ℕ) < (i : ℕ) from hji)
    refine ⟨d, ?_⟩
    rw [hd]
    push_cast
    ring
  let M : Submodule ℂ V := ⨆ k : ℕ, H.eigenspace (l0 + ((k : ℂ) + 1))
  have hFM : ∀ t (i j : Fin n), j < i → ∀ z ∈ M, F t i j z ∈ M := by
    intro t i j hji z hz
    obtain ⟨d, hd⟩ := hdist i j hji
    refine Submodule.iSup_induction _ (motive := fun z => F t i j z ∈ M) hz ?_ ?_ ?_
    · intro k z hz
      rw [Module.End.mem_eigenspace_iff] at hz
      have h1 := hsh t i j _ z hz
      refine (le_iSup (fun k : ℕ => H.eigenspace (l0 + ((k : ℂ) + 1))) (k + d + 1)) ?_
      rw [Module.End.mem_eigenspace_iff, h1, hd]
      congr 1
      push_cast
      ring
    · simp
    · intro x y hx hy
      rw [map_add (f := _)]
      exact add_mem hx hy
  let P : Submodule ℂ V := (ℂ ∙ v) ⊔ M
  have hvP : v ∈ P := Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
  have hPst : ∀ t (i j : Fin n), j < i → ∀ x ∈ P, F t i j x ∈ P := by
    intro t i j hji x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_add (f := _), map_smul]
    refine Submodule.mem_sup_right (add_mem (Submodule.smul_mem _ _ ?_) (hFM t i j hji z hz))
    obtain ⟨d, hd⟩ := hdist i j hji
    refine (le_iSup (fun k : ℕ => H.eigenspace (l0 + ((k : ℂ) + 1))) d) ?_
    rw [Module.End.mem_eigenspace_iff, hsh t i j l0 v (hHx v (fun s k => (hv s).1 k)), hd]
  have hle : low F v ≤ P := by
    unfold UpperTheory.V.AlgRepEndIrreducible.low
    exact sInf_le ⟨hvP, hPst⟩
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hle hw)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hHz : H z = l0 • z := by
    have e1 := hHx w hwν
    have e2 := hHx v (fun s k => (hv s).1 k)
    have e3 : z = w - c • v := by
      rw [← hyz]
      abel
    rw [e3, map_sub, map_smul, e1, e2, smul_sub, smul_comm]
  have hMle : M ≤ ⨆ μ, ⨆ (_ : μ ≠ l0), H.eigenspace μ := by
    refine iSup_le fun k => le_iSup₂_of_le (l0 + ((k : ℂ) + 1)) ?_ le_rfl
    intro h
    have h2 : ((k : ℂ) + 1) = 0 := by linear_combination h
    exact Nat.cast_add_one_ne_zero k h2
  have hz0 : z = 0 :=
    (Submodule.disjoint_def.mp ((Module.End.eigenspaces_iSupIndep H) l0)) z
      (Module.End.mem_eigenspace_iff.mpr hHz) (hMle hz)
  refine ⟨c, ?_⟩
  rw [← hyz, hz0, add_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.LowStab
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.lowStab :
    ∀ (ι V : Type) [Fintype ι] [AddCommGroup V] [Module ℂ V] (n : ℕ) (F : ι → Fin n → Fin n → Module.End ℂ V), IsMultiGl F → ∀ (ν : ι → Fin n → ℂ) (v : V), (∀ t, Formalism.REAL.IsHW (F t) (ν t) v) →
      v ∈ low F v ∧ Stab F (low F v) := by
  intro ι V _ _ _ n F hF ν v hv
  classical
  obtain ⟨hgl, hcomm⟩ := hF
  have hvlow : v ∈ low F v := by
    unfold UpperTheory.V.AlgRepEndIrreducible.low
    rw [Submodule.mem_sInf]
    intro p hp
    exact hp.1
  have hlow : ∀ t (i j : Fin n), j < i → ∀ w ∈ low F v, F t i j w ∈ low F v := by
    intro t i j hji w hw
    unfold UpperTheory.V.AlgRepEndIrreducible.low at hw ⊢
    rw [Submodule.mem_sInf] at hw ⊢
    intro p hp
    exact hp.2 t i j hji w (hw p hp)
  let W' : Submodule ℂ V := low F v ⊓ ⨅ t, ⨅ i, ⨅ j, (low F v).comap (F t i j)
  have hmem : ∀ w, w ∈ W' ↔ w ∈ low F v ∧ ∀ t i j, F t i j w ∈ low F v := by
    intro w
    simp [W', Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
  have hvW : v ∈ W' := by
    rw [hmem]
    refine ⟨hvlow, fun t i j => ?_⟩
    rcases lt_trichotomy i j with h | h | h
    · rw [(hv t).2 i j h]
      exact zero_mem _
    · subst h
      rw [(hv t).1 i]
      exact Submodule.smul_mem _ _ hvlow
    · exact hlow t i j h v hvlow
  have hWst : ∀ t (k l : Fin n), l < k → ∀ w ∈ W', F t k l w ∈ W' := by
    intro t k l hlk w hw
    rw [hmem] at hw ⊢
    refine ⟨hlow t k l hlk w hw.1, fun s i j => ?_⟩
    by_cases hst : s = t
    · subst hst
      have h1 := congrArg (fun f : Module.End ℂ V => f w) (hgl s i j k l)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1
      rw [sub_eq_iff_eq_add] at h1
      rw [h1]
      refine add_mem (sub_mem ?_ ?_) (hlow s k l hlk _ (hw.2 s i j))
      · split_ifs
        · exact hw.2 s i l
        · rw [LinearMap.zero_apply]
          exact zero_mem _
      · split_ifs
        · exact hw.2 s k j
        · rw [LinearMap.zero_apply]
          exact zero_mem _
    · have h1 := congrArg (fun f : Module.End ℂ V => f w) (hcomm s t hst i j k l)
      simp only [Module.End.mul_apply] at h1
      rw [h1]
      exact hlow t k l hlk _ (hw.2 s i j)
  have hle : low F v ≤ W' := by
    unfold UpperTheory.V.AlgRepEndIrreducible.low
    exact sInf_le ⟨hvW, hWst⟩
  exact ⟨hvlow, fun t i j w hw => ((hmem w).mp (hle hw)).2 t i j⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.MsetSep
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.msetSep :
    ∀ m m' : Multiset ℂ, (∀ u : ℂ, (m.map (u + ·)).prod = (m'.map (u + ·)).prod) → m = m' :=
  _root_.UpperTheory.Reformulated.B.MultisetSeparation.msetSep
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.MultiHW
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.multiHW :
    ∀ (ι V : Type) [Fintype ι] [AddCommGroup V] [Module ℂ V] (n : ℕ) (F : ι → Fin n → Fin n → Module.End ℂ V) [FiniteDimensional ℂ V] [Nontrivial V], IsMultiGl F →
      ∃ (ν : ι → Fin n → ℂ) (v : V), v ≠ 0 ∧ ∀ t, Formalism.REAL.IsHW (F t) (ν t) v ∧ Dom (ν t) := by
  intro ι V _ _ _ n F _ _ hM
  obtain ⟨hF, hcomm⟩ := hM
  classical
  have hc : ∀ t k i j, F t k k * F t i j - F t i j * F t k k =
      ((if k = i then (1 : ℂ) else 0) - (if j = k then 1 else 0)) • F t i j := by
    intro t k i j
    rw [hF t]
    by_cases h1 : k = i <;> by_cases h2 : j = k <;> simp_all
  let G : ι → Module.End ℂ V := fun s => ∑ k : Fin n, ((k : ℕ) : ℂ) • F s k k
  have hG : ∀ t i j, G t * F t i j - F t i j * G t = (((i : ℕ) : ℂ) - (j : ℕ)) • F t i j := by
    intro t i j
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, hc, smul_smul, ← Finset.sum_smul]
    simp [mul_sub]
  have hG' : ∀ s t, s ≠ t → ∀ i j, G s * F t i j - F t i j * G s = 0 := by
    intro s t hst i j
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, hcomm s t hst, sub_self]
  let H : Module.End ℂ V := ∑ s, G s
  have hH : ∀ t i j, H * F t i j = F t i j * H + (((i : ℕ) : ℂ) - (j : ℕ)) • F t i j := by
    intro t i j
    rw [← sub_eq_iff_eq_add', Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
      Finset.sum_eq_single t (fun s _ hs => hG' s t hs i j) (by simp), hG]
  obtain ⟨l, hl, hmin⟩ := Set.exists_min_image {c | H.HasEigenvalue c} Complex.re (Module.End.finite_hasEigenvalue H)
    (Module.End.exists_eigenvalue H)
  obtain ⟨v, hv, hv0, ν, hν⟩ := GlobalTheory.AlgInfChar.exists_joint_eigenvector (fun p : ι × Fin n => F p.1 p.2 p.2)
    (fun p q => by
      obtain ⟨s, i⟩ := p
      obtain ⟨t, j⟩ := q
      by_cases hst : s = t
      · subst hst
        rw [← sub_eq_zero, hc]
        by_cases h : i = j <;> simp [h, eq_comm]
      · exact hcomm s t hst _ _ _ _) (H.eigenspace l) hl
    (fun k v hv => by
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      rw [← Module.End.mul_apply, hH]
      simp [hv])
  rw [Module.End.mem_eigenspace_iff] at hv
  have hup : ∀ t i j, i < j → F t i j v = 0 := by
    intro t i j hij
    by_contra h0
    have h1 : H (F t i j v) = (l + (((i : ℕ) : ℂ) - (j : ℕ))) • F t i j v := by
      rw [← Module.End.mul_apply, hH]
      simp [hv, add_smul]
    have h2 := hmin _ (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 h1, h0⟩)
    simp at h2
    exact absurd hij (not_lt.2 h2)
  have hν' : ∀ t k, F t k k v = ν (t, k) • v := fun t k => hν (t, k)
  refine ⟨fun t k => ν (t, k), v, hv0, fun t => ⟨⟨hν' t, hup t⟩, fun i j hij =>
    GlobalTheory.AlgInfChar.exists_nat_of_primitive (F t i j) (F t j i) (F t i i - F t j j) ?_ ?_ v _ hv0
      (hup t i j hij) ?_⟩⟩
  · rw [hF t]; simp
  · have h1 := hc t i j i
    have h2 := hc t j j i
    simp only [hij.ne, if_false, if_true] at h1 h2
    rw [sub_mul, mul_sub]
    linear_combination (norm := module) h1 - h2
  · simp [hν', sub_smul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.QdetIntertw
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem qdet_intertw {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] {k : ℕ}
    (R : M →ₗ[ℂ] M') (X : Fin k → Fin k → Module.End ℂ M) (Y : Fin k → Fin k → Module.End ℂ M')
    (h : ∀ p q, R ∘ₗ X p q = Y p q ∘ₗ R) (v : ℂ) :
    R ∘ₗ Formalism.REAL.qdet X v = Formalism.REAL.qdet Y v ∘ₗ R := by
  let S : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ M') :=
    { carrier := {z | R ∘ₗ z.1 = z.2 ∘ₗ R}
      mul_mem' := fun {x y} hx hy => by
        change R ∘ₗ (x.1 ∘ₗ y.1) = (x.2 ∘ₗ y.2) ∘ₗ R
        rw [← LinearMap.comp_assoc, hx, LinearMap.comp_assoc, hy, LinearMap.comp_assoc]
      add_mem' := fun {x y} hx hy => by
        change R ∘ₗ (x.1 + y.1) = (x.2 + y.2) ∘ₗ R
        rw [LinearMap.comp_add, LinearMap.add_comp, hx, hy]
      algebraMap_mem' := fun c => by
        change R ∘ₗ (algebraMap ℂ (Module.End ℂ M) c) = (algebraMap ℂ (Module.End ℂ M') c) ∘ₗ R
        ext φ; simp }
  let Z : Fin k → Fin k → S := fun p q => ⟨(X p q, Y p q), h p q⟩
  have e1 : ((Formalism.REAL.qdet Z v : S) : Module.End ℂ M × Module.End ℂ M').1 = Formalism.REAL.qdet X v :=
    map_qdet ((AlgHom.fst ℂ _ _).comp S.val) Z v
  have e2 : ((Formalism.REAL.qdet Z v : S) : Module.End ℂ M × Module.End ℂ M').2 = Formalism.REAL.qdet Y v :=
    map_qdet ((AlgHom.snd ℂ _ _).comp S.val) Z v
  rw [← e1, ← e2]
  exact (Formalism.REAL.qdet Z v).2

set_option synthInstance.maxHeartbeats 100000 in
theorem UpperTheory.V.AlgRepEndIrreducible.tensA :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a), IsLieHom (A := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieA π Ξ) ∧
      (∀ (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)), tensorK π Ξ k * lieA π Ξ (toL X) = lieA π Ξ (toL (k.1 * X * star k.1)) * tensorK π Ξ k) ∧
      ∀ (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar τ m → ∀ u : ℂ,
        Formalism.REAL.qdet (eL (N := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieA π Ξ) τ) (u + ((a : ℂ) - 1) / 2) =
          (m.map (u + ·)).prod • (1 : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) := by
  intro E _ _ _ a π Ξ
  let f : Module.End ℂ π.V →ₐ[ℂ] Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) := Module.End.rTensorAlgHom ℂ π.V (Fin Ξ.d → ℂ)
  have hf : ∀ X, lieA π Ξ X = f (lieOp π X) := fun _ => rfl
  refine ⟨fun X Y => ?_, fun k X => ?_, fun τ m hm u => ?_⟩
  · rw [hf, hf, hf, ← map_mul f, ← map_mul f, ← map_sub f]
    congr 1
    exact LinearMap.ext fun φ => Subtype.ext (LinearMap.congr_fun ((lie_comm (toL X) (toL Y)).trans
      (map_sub (lie E a) (toL (X * Y)) (toL (Y * X))).symm) φ.1)
  · refine TensorProduct.ext' fun φ v => ?_
    have h1 : π.op (.cpt k) (lieOp π (toL X) φ) = lieOp π (toL (k.1 * X * star k.1)) (π.op (.cpt k) φ) :=
      Subtype.ext (LinearMap.congr_fun (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) X) φ.1)
    simp only [mul_apply_eq_comp, tensorK, lieA_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul, h1]
  · have e : eL (N := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieA π Ξ) τ =
        fun i j => f (eL (N := Module.End ℂ π.V) (lieOp π) τ i j) := by
      funext i j
      simp only [eL, hf, map_smul, map_sub]
    have h := qdet_intertw π.V.subtype (eL (N := Module.End ℂ π.V) (lieOp π) τ) (Eop τ) (fun _ _ => rfl)
      (u + ((a : ℂ) - 1) / 2)
    have h2 : Formalism.REAL.qdet (eL (N := Module.End ℂ π.V) (lieOp π) τ) (u + ((a : ℂ) - 1) / 2) =
        (m.map (u + ·)).prod • (1 : Module.End ℂ π.V) :=
      LinearMap.ext fun φ => Subtype.ext ((LinearMap.congr_fun h φ).trans (hm.2 u φ.1 φ.2))
    rw [e, ← map_qdet, h2, map_smul, map_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.TelGrp
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem rp_comm {X M : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M]
    (κ : Module.End ℂ M) (g : X → X) :
    ∀ (n : ℕ) (b : Fin n → X →ₗ[ℂ] Module.End ℂ M), (∀ i y, κ * b i y = b i (g y) * κ) →
      ∀ x : Fin n → X, κ * rp n b x = rp n b (fun i => g (x i)) * κ := by
  intro n
  induction n with
  | zero => intro b _ x; rw [rp_zero, rp_zero, mul_one, one_mul]
  | succ n ih =>
    intro b hb x
    have h := ih (Fin.tail b) (fun i y => hb i.succ y) (Fin.tail x)
    rw [rp_succ, rp_succ, ← mul_assoc, h, mul_assoc, hb, ← mul_assoc]
    rfl

theorem UpperTheory.V.AlgRepEndIrreducible.telGrp :
    ∀ (X M : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M] (n : ℕ) (a b : Fin n → X →ₗ[ℂ] Module.End ℂ M) (κ : Module.End ℂ M) (g : X → X),
      (∀ i y, κ * a i y = a i (g y) * κ) → (∀ i y, κ * b i y = b i (g y) * κ) →
      ∀ f f' : X →ₗ[ℂ] M, (∀ y, κ (f y) = f' (g y)) → ∀ x : Fin n → X, κ (tel n a b f x) = tel n a b f' fun i => g (x i) := by
  intro X M _ _ _ _ n
  induction n with
  | zero => intro a b κ g _ _ f f' _ x; rw [tel_zero, tel_zero, map_zero]
  | succ n ih =>
    intro a b κ g ha hb f f' hf x
    have h1 := ih (Fin.tail a) (Fin.tail b) κ g (fun i y => ha i.succ y) (fun i y => hb i.succ y) f f' hf (Fin.tail x)
    have h2 := LinearMap.congr_fun (rp_comm κ g n (Fin.tail b) (fun i y => hb i.succ y) (Fin.tail x)) (f (x 0))
    have h3 := LinearMap.congr_fun (ha 0 (x 0)) (tel n (Fin.tail a) (Fin.tail b) f (Fin.tail x))
    simp only [Module.End.mul_apply] at h2 h3
    rw [tel_succ, tel_succ, map_add (f := _), h2, h3, h1, hf]
    rfl
end

