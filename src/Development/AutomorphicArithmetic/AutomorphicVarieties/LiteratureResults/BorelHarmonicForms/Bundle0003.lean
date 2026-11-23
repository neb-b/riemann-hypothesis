module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.HolIdExp
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem emb_split {E : Type} [Field E] [_root_.NumberField.IsTotallyComplex E] (z : (E →+* ℂ) → ℂ) :
    ∃ u v : Cinf E, z = emb E u + Complex.I • emb E v := by
  refine ⟨fun w => (z w.embedding + starRingEnd ℂ (z (ComplexEmbedding.conjugate w.embedding))) / 2,
    fun w => -Complex.I * (z w.embedding - starRingEnd ℂ (z (ComplexEmbedding.conjugate w.embedding))) / 2, ?_⟩
  funext τ
  change z τ = coord τ _ + Complex.I * coord τ _
  have key : ∃ w : InfinitePlace E, τ = w.embedding ∨ τ = ComplexEmbedding.conjugate w.embedding := by
    refine ⟨InfinitePlace.mk τ, ?_⟩
    have h' : InfinitePlace.mk (InfinitePlace.mk τ).embedding = InfinitePlace.mk τ := InfinitePlace.mk_embedding _
    exact (InfinitePlace.mk_eq_iff.1 h').imp Eq.symm Eq.symm
  obtain ⟨w, rfl | rfl⟩ := key
  · rw [UpperTheory.V.FieldIso.coord_embedding, UpperTheory.V.FieldIso.coord_embedding]
    linear_combination ((z w.embedding - starRingEnd ℂ (z (ComplexEmbedding.conjugate w.embedding))) / 2) * Complex.I_mul_I
  · rw [UpperTheory.V.FieldIso.coord_conj, UpperTheory.V.FieldIso.coord_conj, UpperTheory.V.FieldIso.coord_embedding,
      UpperTheory.V.FieldIso.coord_embedding]
    simp only [map_div₀, map_add (f := _), map_sub, map_mul, map_neg, Complex.conj_I, Complex.conj_conj, map_ofNat]
    linear_combination (-(starRingEnd ℂ (z w.embedding) - z (ComplexEmbedding.conjugate w.embedding)) / 2) * Complex.I_mul_I

private theorem emb_cont {E : Type} [Field E] : Continuous (emb E) := by
  refine continuous_pi fun τ => ?_
  change Continuous (coord τ)
  unfold coord
  split_ifs
  · exact continuous_apply _
  · exact Complex.continuous_conj.comp (continuous_apply _)

open scoped Matrix.Norms.Operator in
private theorem exp_map_emb {E : Type} [Field E] [NumberField E] {a : ℕ} (Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    (NormedSpace.exp Y).map (emb E) = NormedSpace.exp (Y.map (emb E)) :=
  NormedSpace.map_exp (RingHom.mapMatrix (m := Fin a) (emb E)) (continuous_id.matrix_map emb_cont) Y

open scoped Matrix.Norms.Operator in
private theorem exp_diff {T : Type} [Fintype T] {a : ℕ} (P Q : Matrix (Fin a) (Fin a) (T → ℂ)) :
    Differentiable ℂ fun s : ℂ => (fun i j => NormedSpace.exp (P + s • Q) i j : Fin a → Fin a → T → ℂ) := by
  set_option synthInstance.maxHeartbeats 200000 in
  have h : Differentiable ℂ fun s : ℂ => NormedSpace.exp (P + s • Q) := fun s =>
    (NormedSpace.exp_analytic (𝕂 := ℂ) (P + s • Q)).differentiableAt.comp s
      (f := fun s : ℂ => P + s • Q) ((differentiableAt_const P).add (differentiableAt_id.smul_const Q))
  refine differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
  let l : Matrix (Fin a) (Fin a) (T → ℂ) →ₗ[ℂ] (T → ℂ) := Matrix.entryLinearMap ℂ (T → ℂ) i j
  exact (LinearMap.toContinuousLinearMap l).differentiable.comp h

theorem UpperTheory.V.Lit.Bor.holIdExp :
    UpperTheory.V.Lit.Bor.HolIdExp := by
  intro E _ _ _ a Φ hΦ h0 X
  choose A B hAB using fun i j => emb_split (X i j)
  let P := (Matrix.of A).map (emb E)
  let Q := (Matrix.of B).map (emb E)
  have hX : X = P + Complex.I • Q := by
    exact Matrix.ext fun i j => hAB i j
  have hd : Differentiable ℂ fun s : ℂ => Φ fun i j => NormedSpace.exp (P + s • Q) i j :=
    differentiableOn_univ.1 (hΦ.comp (exp_diff P Q).differentiableOn fun s _ => Matrix.isUnit_exp (P + s • Q))
  have hr : ∀ t : ℝ, (Φ fun i j => NormedSpace.exp (P + (t : ℂ) • Q) i j) = 0 := fun t => by
    have e : P + (t : ℂ) • Q = (Matrix.of A + t • Matrix.of B).map (emb E) := by
      ext i j τ
      change coord τ (A i j) + (t : ℂ) * coord τ (B i j) = coord τ (A i j + t • B i j)
      rw [map_add (f := _), UpperTheory.V.FieldIso.coord_smul, Complex.real_smul]
    rw [e, ← exp_map_emb]
    exact h0 (Matrix.isUnit_exp (Matrix.of A + t • Matrix.of B)).unit
  have hf : ∃ᶠ s in nhdsWithin (0 : ℂ) {0}ᶜ, (Φ fun i j => NormedSpace.exp (P + s • Q) i j) = (fun _ => 0) s := by
    have ht : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · simpa using (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun t ht => by simpa using ht
    exact ht.frequently (Filter.Frequently.of_forall hr)
  have := AnalyticOnNhd.eq_of_frequently_eq (fun s _ => hd.analyticAt s) analyticOnNhd_const hf
  rw [hX]
  exact congrFun this Complex.I
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.InclFacts
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.inclFacts :
    UpperTheory.V.Lit.Bor.InclFacts := by
  intro E _ _ _ a π Ξ r
  have hA : ∀ X m, incl π Ξ (lieA π Ξ X m) = smA Ξ X (incl π Ξ m) := fun X m => by
    induction m using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul φ v => rfl
  have hB : ∀ X m, incl π Ξ (lieB π Ξ X m) = smB Ξ X (incl π Ξ m) := fun X m => by
    rw [smB_apply]
    induction m using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul φ v => rfl
  refine ⟨?_, fun i m => ?_, fun k m => ?_, fun X m => ?_, fun X m => ?_⟩
  · exact Module.Flat.rTensor_preserves_injective_linearMap _ π.V.injective_subtype
  · induction m using TensorProduct.induction_on with
    | zero => simp only [map_zero]; rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]; rfl
    | tmul φ v =>
      rw [cmp_tmul]
      exact cmp_tmul i φ.1 v
  · induction m using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul φ v => rfl
  · induction m using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul φ v => rfl
  · rw [piAdj, smAdj, adj_apply, adj_apply, map_sub, map_sub, hA, hB, LinearMap.map_smul_of_tower]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.IndepAbs
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.indepAbs :
    UpperTheory.V.Lit.Bor.IndepAbs := by
  classical
  intro O W _ _ A s V h hs hn
  have hsup : ∀ P Q : Submodule ℂ W, (∀ o, ∀ x ∈ P, A o x ∈ P) → (∀ o, ∀ x ∈ Q, A o x ∈ Q) →
      ∀ o, ∀ x ∈ P ⊔ Q, A o x ∈ P ⊔ Q := by
    intro P Q hP hQ o x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hP o y hy) (hQ o z hz)
  have hfs : ∀ t : Finset (Fin s), ∀ o, ∀ x ∈ t.sup V, A o x ∈ t.sup V := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro o x hx
      simp only [Finset.sup_empty, Submodule.mem_bot] at hx ⊢
      rw [hx, map_zero]
    | insert j t hj ih =>
      rw [Finset.sup_insert]
      exact hsup _ _ (h j) ih
  have key : ∀ t : Finset (Fin s), ∀ i, i ∉ t → Disjoint (V i) (t.sup V) := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro i _; simp
    | insert j t hj ih =>
      intro i hi
      rw [Finset.mem_insert, not_or] at hi
      obtain ⟨hij, hit⟩ := hi
      have hSinv := hfs t
      have hiS := ih i hit
      have hjS := ih j hj
      rw [Finset.sup_insert, disjoint_iff]
      set S := t.sup V with hSdef
      by_cases hVi : V i = ⊥
      · rw [hVi, bot_inf_eq]
      have hM : ∀ o, ∀ x ∈ V i ⊓ (V j ⊔ S), A o x ∈ V i ⊓ (V j ⊔ S) :=
        fun o x hx => ⟨h i o x hx.1, hsup _ _ (h j) hSinv o x hx.2⟩
      rcases hs i _ inf_le_left hM with hbot | htop
      · exact hbot
      exfalso
      have hle : V i ≤ V j ⊔ S := inf_eq_left.mp htop
      have huniq : ∀ y y' : V j, ((y : W) - y') ∈ S → y = y' := by
        intro y y' hyy
        have h0 : ((y : W) - y') ∈ V j ⊓ S := ⟨sub_mem y.2 y'.2, hyy⟩
        rw [disjoint_iff.mp hjS, Submodule.mem_bot, sub_eq_zero] at h0
        exact Subtype.ext h0
      let fj : V j →ₗ[ℂ] W ⧸ S := S.mkQ ∘ₗ (V j).subtype
      have hfj : Function.Injective fj := by
        intro a b hab
        exact huniq a b ((Submodule.Quotient.eq S).mp hab)
      let ej := LinearEquiv.ofInjective fj hfj
      let fi : V i →ₗ[ℂ] W ⧸ S := S.mkQ ∘ₗ (V i).subtype
      have hrange : ∀ x : V i, fi x ∈ LinearMap.range fj := by
        intro x
        obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hle x.2)
        refine ⟨⟨y, hy⟩, ?_⟩
        show S.mkQ y = S.mkQ x
        rw [← hyz, map_add (f := _), Submodule.mkQ_apply S z, (Submodule.Quotient.mk_eq_zero S).mpr hz,
          add_zero]
      let T : V i →ₗ[ℂ] V j := ej.symm.toLinearMap ∘ₗ (fi.codRestrict (LinearMap.range fj) hrange)
      have hT : ∀ x : V i, ((T x : W) - x) ∈ S := by
        intro x
        have e0 : T x = ej.symm ⟨fi x, hrange x⟩ := rfl
        have e1 := ej.apply_symm_apply ⟨fi x, hrange x⟩
        rw [Subtype.ext_iff, LinearEquiv.ofInjective_apply, ← e0] at e1
        exact (Submodule.Quotient.eq S).mp e1
      have hTeq : ∀ o (x : V i), T ((A o).restrict (h i o) x) = (A o).restrict (h j o) (T x) := by
        intro o x
        apply huniq
        have e1 := hT ((A o).restrict (h i o) x)
        have e2 : A o ((T x : W) - x) ∈ S := hSinv o _ (hT x)
        have e3 : ((T ((A o).restrict (h i o) x) : W) - ((A o).restrict (h j o) (T x) : W))
            = ((T ((A o).restrict (h i o) x) : W) - ((A o).restrict (h i o) x : W))
              - A o ((T x : W) - x) := by
          simp only [LinearMap.restrict_coe_apply, map_sub]
          abel
        rw [e3]
        exact sub_mem e1 e2
      have hTinj : Function.Injective T := by
        rw [← LinearMap.ker_eq_bot, eq_bot_iff]
        intro x hx
        rw [LinearMap.mem_ker] at hx
        have e1 := hT x
        rw [hx, Submodule.coe_zero, zero_sub] at e1
        have hxS : (x : W) ∈ S := by simpa using S.neg_mem e1
        have e2 : (x : W) ∈ V i ⊓ S := ⟨x.2, hxS⟩
        rw [disjoint_iff.mp hiS, Submodule.mem_bot] at e2
        exact (Submodule.mem_bot ℂ).mpr (Subtype.ext e2)
      let N := (LinearMap.range T).map (V j).subtype
      have hNle : N ≤ V j := Submodule.map_subtype_le _ _
      have hNinv : ∀ o, ∀ x ∈ N, A o x ∈ N := by
        intro o x hx
        obtain ⟨y, ⟨z, rfl⟩, rfl⟩ := hx
        refine ⟨T ((A o).restrict (h i o) z), ⟨_, rfl⟩, ?_⟩
        rw [hTeq]
        rfl
      have hTsurj : Function.Surjective T := by
        rcases hs j N hNle hNinv with hN0 | hNj
        · exfalso
          obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVi
          have hmem : ((T ⟨x, hx⟩ : V j) : W) ∈ N := ⟨T ⟨x, hx⟩, ⟨_, rfl⟩, rfl⟩
          rw [hN0, Submodule.mem_bot] at hmem
          have : T ⟨x, hx⟩ = T 0 := by rw [map_zero]; exact Subtype.ext hmem
          exact hx0 (congrArg Subtype.val (hTinj this))
        · intro y
          have hy : (y : W) ∈ N := by rw [hNj]; exact y.2
          obtain ⟨y', ⟨z, rfl⟩, hz⟩ := hy
          exact ⟨z, Subtype.ext hz⟩
      exact hn i j hij ⟨LinearEquiv.ofBijective T ⟨hTinj, hTsurj⟩, hTeq⟩
  rw [iSupIndep_iff_supIndep]
  intro t u _ i _ hiu
  exact key u i hiu
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.IpAdj
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.ipAdj :
    UpperTheory.V.Lit.Bor.IpAdj := by
  intro E _ _ _ a n e M _ _ _ _ L L' H N hadj q ω η hω hη
  have key : ∀ i : Fin (q + 1), ∑ I : Fin (q + 1) → Fin n,
      H (ω fun k => e (I k)) ((-1 : ℤ) ^ (i : ℕ) • L (toL (e (I i)).1) (η (i.removeNth fun k => e (I k)))) =
      ip e H (del L' e ω) η := fun i => by
    rw [← (Fin.insertNthEquiv (fun _ => Fin n) i).sum_comp, Fintype.sum_prod_type, Finset.sum_comm, ip]
    refine Finset.sum_congr rfl fun J _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [del_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : (fun k => e ((Fin.insertNthEquiv (fun _ => Fin n) i (j, J)) k)) =
        i.insertNth (α := fun _ => Herm E a) (e j) (fun k => e (J k)) := by
      funext k
      refine Fin.succAboveCases i ?_ (fun k => ?_) k <;> simp [Fin.insertNthEquiv]
    have h2 : (Fin.insertNthEquiv (fun _ => Fin n) i (j, J)) i = j := by simp [Fin.insertNthEquiv]
    rw [h1, h2, Fin.removeNth_insertNth, AlternatingMap.map_insertNth, ← hadj _ _ (hω _) _ (hη _),
      map_zsmul, map_zsmul, LinearMap.smul_apply, smul_smul, ← mul_pow]
    simp
  have h0 : ip e H ω (dCo L η) = ∑ i : Fin (q + 1), ∑ I : Fin (q + 1) → Fin n,
      H (ω fun k => e (I k)) ((-1 : ℤ) ^ (i : ℕ) • L (toL (e (I i)).1) (η (i.removeNth fun k => e (I k)))) := by
    rw [Finset.sum_comm, ip]
    refine Finset.sum_congr rfl fun I _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [dCo_apply, map_sum]
  rw [h0, Finset.sum_congr rfl fun i _ => key i]
  simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.KugaZero
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.kugaZero :
    UpperTheory.V.Lit.Bor.KugaZero := by
  intro E _ _ _ a n e M _ _ _ _ A B hc ω hω X
  rw [del_apply]
  simp only [cas, LinearMap.sub_apply, LinearMap.sum_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs : star (Complex.I • (e j).1) = -(Complex.I • (e j).1) := by
    have h : star (e j).1 = (e j).1 := (e j).2
    rw [star_smul, h, Complex.star_def, Complex.conj_I, neg_smul]
  have h0 := hω _ hs X
  rw [Fin.sum_univ_zero, LinearMap.add_apply, LinearMap.add_apply] at h0
  have h1 : ∀ (Y Z) (m : M), A Y (B Z m) = B Z (A Y m) := fun Y Z m => LinearMap.congr_fun (hc Y Z).eq m
  have h2 := congrArg (B (toL (Complex.I • (e j).1))) h0
  have h3 := congrArg (A (toL (Complex.I • (e j).1))) h0
  rw [map_add (f := _), map_zero] at h2 h3
  rw [h1] at h3
  have h4 : B (toL (Complex.I • (e j).1)) (B (toL (Complex.I • (e j).1)) (ω X)) =
      A (toL (Complex.I • (e j).1)) (A (toL (Complex.I • (e j).1)) (ω X)) := by
    rw [← sub_eq_zero, ← sub_self (0 : M)]
    nth_rewrite 1 [← h2]
    rw [← h3]
    abel
  rw [dCo_apply, Fin.sum_univ_one, Subsingleton.elim (Fin.removeNth _ _) X]
  simp only [Fin.val_zero, pow_zero, one_smul, Matrix.cons_val_zero, LinearMap.add_apply, map_add (f := _), Module.End.mul_apply, h1, h4]
  abel
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.LieOneComm
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem lie_left (X : Lie E a) (φ : Sm E a) (h g : GA E a) (hφ : ∀ g, φ.1 (h * g) = φ.1 g) :
    (lie E a X φ).1 (h * g) = (lie E a X φ).1 g := by
  have e : chart φ.1 (h * g) =ᶠ[nhds (oneL E a)] chart φ.1 g := by
    filter_upwards [isOpen_invSet.mem_nhds (val_mem_invSet (1 : GL (Fin a) (Cinf E)))] with x hx
    obtain ⟨u, hu⟩ := hx
    obtain rfl : x = toL u.val := hu.symm
    rw [chart_val, chart_val, mul_assoc, hφ]
  change fderiv ℝ (chart φ.1 (h * g)) (oneL E a) X = fderiv ℝ (chart φ.1 g) (oneL E a) X
  rw [e.fderiv_eq]

private theorem lie_fin (X : Lie E a) (k : GL (Fin a) (Af E)) (φ : Sm E a) :
    act (.fin k) (lie E a X φ) = lie E a X (act (.fin k) φ) :=
  (LinearMap.congr_fun (lie_rt_fin X k) φ).symm

private theorem lie_one_comm (X : Lie E a) (φ : Sm E a) :
    lie E a (oneL E a) (lie E a X φ) = lie E a X (lie E a (oneL E a) φ) := by
  have h := lie_comm (oneL E a) X
  have e : Matrix.of (oneL E a) * Matrix.of X = Matrix.of X * Matrix.of (oneL E a) :=
    (one_mul (Matrix.of X)).trans (mul_one (Matrix.of X)).symm
  rw [e, sub_self, sub_eq_zero] at h
  exact LinearMap.congr_fun h φ

private theorem level_lie (X : Lie E a) (φ : Sm E a) (h : IsOpen {k | act (.fin k) φ = φ}) :
    IsOpen {k | act (.fin k) (lie E a X φ) = lie E a X φ} := by
  let ρ : GL (Fin a) (Af E) →* Module.End ℂ (Sm E a) := (rt E a).comp (finGL E a)
  let S : Sm E a → Subgroup (GL (Fin a) (Af E)) := fun ψ =>
    { carrier := {k | ρ k ψ = ψ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        change ρ (x * y) ψ = ψ
        rw [map_mul, mul_apply_eq_comp, hy, hx]
      inv_mem' := fun {x} hx => by
        change ρ x⁻¹ ψ = ψ
        have hx' : ρ x ψ = ψ := hx
        conv_lhs => rw [← hx', ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self] }
  have hle : S φ ≤ S (lie E a X φ) := fun k hk => (lie_fin X k φ).trans (congrArg (lie E a X) hk)
  exact Subgroup.isOpen_mono hle h

private theorem isSq_lie (r : ℝ) (X : Lie E a) (φ : Sm E a) (h : IsSq r φ) : IsSq r (lie E a X φ) := by
  refine ⟨fun γ g => lie_left X φ _ g (h.left γ), level_lie X φ h.level, ?_, ?_⟩
  · rw [lie_one_comm, h.one, map_smul]
  · intro l
    have := h.sq (l ++ [X])
    rwa [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, mul_apply_eq_comp] at this

end

theorem UpperTheory.V.Lit.Bor.sqLie :
    UpperTheory.V.Lit.Bor.SqLie := by
  intro E _ _ _ a r
  refine ⟨isSq_lie r, fun X φ hφ => ?_⟩
  have h : sqSub E a r ≤ (sqSub E a r).comap (lie E a X) :=
    Submodule.span_le.2 fun ψ hψ => Submodule.subset_span (isSq_lie r X ψ hψ)
  exact h hφ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneParam
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem op_cont_inf (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  have hs : Continuous (sInf E : Cinf E → Ad E) := (GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

open scoped Matrix.Norms.Operator in
private theorem exists_one_parameter_exp {E : Type} [Field E] [NumberField E] {a : ℕ} (Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    ∃ c : ℝ → GL (Fin a) (Cinf E), c 0 = 1 ∧ (∀ s t, c (s + t) = c s * c t) ∧ Continuous c ∧
      HasDerivAt (fun t => toL (c t).val) (toL Y) 0 ∧ ∀ t : ℝ, (c t).val = NormedSpace.exp (t • Y) := by
  let c : ℝ → GL (Fin a) (Cinf E) := fun t => (Matrix.isUnit_exp (t • Y)).unit
  have hc : ∀ t, (c t).val = NormedSpace.exp (t • Y) := fun t => rfl
  have h0 : c 0 = 1 := Units.ext (by simp [c])
  have hadd : ∀ s t, c (s + t) = c s * c t := fun s t => Units.ext (by
    rw [Units.val_mul, hc, hc, hc, add_smul,
      Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left s).smul_right t)])
  have hv : Continuous fun t : ℝ => NormedSpace.exp (t • Y) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y t).continuousAt
  have hinv : ∀ t, (c t)⁻¹ = c (-t) := fun t =>
    inv_eq_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, h0])
  refine ⟨c, h0, hadd, Units.continuous_iff.2 ⟨hv, ?_⟩, ?_, hc⟩
  · simp only [hinv, hc]
    exact hv.comp continuous_neg
  · have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h

theorem UpperTheory.V.Lit.Bor.oneParam :
    UpperTheory.V.Lit.Bor.OneParam := by
  intro E _ _ _ a X
  obtain ⟨c, h0, hadd, hc, hd, he⟩ := exists_one_parameter_exp (E := E) (Matrix.of X)
  exact ⟨c, h0, hadd, (op_cont_inf E a).comp hc, hd, he⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.TformAdj
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem cmp_lTensor_toLin {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j ((Matrix.toLin' Q).lTensor W y) = ∑ k, Q j k • cmp k y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
    simp only [LinearMap.lTensor_tmul, cmp_tmul, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Finset.sum_smul, smul_smul]
  | add a b ha hb =>
    simp only [map_add (f := _), ha, hb, smul_add, Finset.sum_add_distrib]

private theorem cmp_rTensor_end {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (S : Module.End ℂ W)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j (S.rTensor (Fin d → ℂ) y) = S (cmp j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v => simp only [LinearMap.rTensor_tmul, cmp_tmul, map_smul]

theorem UpperTheory.V.Lit.Bor.tformAdj :
    UpperTheory.V.Lit.Bor.TformAdj := by
  intro W _ _ d H N G P Q S T
  refine ⟨fun hPQ x y => ?_, fun hST x hx y hy => ?_⟩
  · have key : ∀ a b, (G * Q) a b = (Pᴴ * G) a b := fun a b => by rw [hPQ]
    have hL : tform H G x ((Matrix.toLin' Q).lTensor W y)
        = ∑ a, ∑ b, (G * Q) a b * H (cmp a x) (cmp b y) := by
      rw [tform_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [cmp_lTensor_toLin, map_sum, map_smul, smul_eq_mul, Matrix.mul_apply,
        Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    have hR : tform H G ((Matrix.toLin' P).lTensor W x) y
        = ∑ a, ∑ b, (Pᴴ * G) a b * H (cmp a x) (cmp b y) := by
      rw [tform_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [cmp_lTensor_toLin, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply,
        starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
      conv_lhs => rw [Finset.sum_comm]
      conv_lhs => enter [2, j]; rw [Finset.sum_comm]
      conv_lhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun i _ => by ring
    rw [hL, hR]
    simp only [key]
  · rw [mem_tens] at hx hy
    rw [tform_apply, tform_apply]
    simp only [cmp_rTensor_end, hST _ (hx _) _ (hy _)]
end

