module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.LevShrink
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CuspSupportOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0019

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.SliceT
section
open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp

section SlopeTestRemainingChoices

open UpperTheory.V.Af.Fin GroundTheory.Automorphic.AutomorphicForm

private theorem st_emb_val {R : Type} [CommRing R] {a n : ℕ} (e : Fin a ↪ Fin n) (g : GL (Fin a) R) (i j : Fin a) :
    (emb e g).val (e i) (e j) = g.val i j := by
  rw [coe_emb, Matrix.add_apply, matrixExtendByZero_apply, Matrix.sub_apply]
  simp [Matrix.one_apply]

private theorem st_mem_of_emb {L : Type} [Field L] (O : Subring L) {a n : ℕ} (e : Fin a ↪ Fin n) {h : GL (Fin a) L}
    (hk : emb e h ∈ GLint (Fin n) O) : h ∈ GLint (Fin a) O := by
  obtain ⟨k, hk⟩ := hk
  have hk' : bc O.subtype k⁻¹ = emb e h⁻¹ := by rw [map_inv, hk, map_inv]
  let A : Matrix (Fin a) (Fin a) O := fun i j => k.val (e i) (e j)
  let B : Matrix (Fin a) (Fin a) O := fun i j => (k⁻¹).val (e i) (e j)
  have hA : A.map O.subtype = h.val := by
    ext i j
    rw [← st_emb_val e h, ← hk]
    rfl
  have hB : B.map O.subtype = (h⁻¹).val := by
    ext i j
    rw [← st_emb_val e h⁻¹, ← hk']
    rfl
  have inj : Function.Injective (fun M : Matrix (Fin a) (Fin a) O => M.map O.subtype) :=
    Matrix.map_injective Subtype.val_injective
  have hAB : A * B = 1 := inj (by
    change (A * B).map O.subtype = (1 : Matrix (Fin a) (Fin a) O).map O.subtype
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
    exact congrArg Units.val (mul_inv_cancel h))
  have hBA : B * A = 1 := inj (by
    change (B * A).map O.subtype = (1 : Matrix (Fin a) (Fin a) O).map O.subtype
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
    exact congrArg Units.val (inv_mul_cancel h))
  exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

variable {R S : Type} [CommRing R] [CommRing S]

private theorem st_corner_sub {a : ℕ} (s : R →ₙ+* S) (g : GL (Fin a) R) (i j : Fin a) :
    ((cornerGL a s g).val - 1) i j = s ((g.val - 1) i j) := by
  change (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g.val i j)
    - (1 : Matrix (Fin a) (Fin a) S) i j = s (g.val i j - (1 : Matrix (Fin a) (Fin a) R) i j)
  rw [map_sub]
  ring

private theorem st_corner_emb {a n : ℕ} (e : Fin a ↪ Fin n) (s : R →ₙ+* S) (g : GL (Fin a) R) :
    cornerGL n s (emb e g) = emb e (cornerGL a s g) := by
  refine Units.ext (sub_left_injective (b := (1 : Matrix (Fin n) (Fin n) S)) ?_)
  ext i j
  beta_reduce
  rw [st_corner_sub, coe_emb, coe_emb, add_sub_cancel_left, add_sub_cancel_left]
  by_cases hi : ∃ k, i = e k
  · obtain ⟨k, rfl⟩ := hi
    by_cases hj : ∃ l, j = e l
    · obtain ⟨l, rfl⟩ := hj
      rw [matrixExtendByZero_apply, matrixExtendByZero_apply, st_corner_sub]
    · push Not at hj
      rw [matrixExtendByZero_apply_of_outside_col e _ _ hj, matrixExtendByZero_apply_of_outside_col e _ _ hj, map_zero]
  · push Not at hi
    rw [extendByZero_apply_eq_zero_of_row_not_mem e _ hi, extendByZero_apply_eq_zero_of_row_not_mem e _ hi, map_zero]

end SlopeTestRemainingChoices

section Main

open UpperTheory.V.Af.Fin GroundTheory.Automorphic.AutomorphicForm
open PositivityTheory.Rg.BcB.SpectralAccumulation (TypeB)
open UpperTheory.V.Cj.S (res)

variable {E : Type} [Field E] [NumberField E]

private theorem st_emb_fin {a n : ℕ} (e : Fin a ↪ Fin n) (u : GL (Fin a) (Af E)) :
    emb e (finGL E a u) = finGL E n (emb e u) := by
  simp only [finGL, st_corner_emb]

private theorem st_emb_loc {a n : ℕ} (e : Fin a ↪ Fin n) (w) (k : GL (Fin a) (HeightOneSpectrum.adicCompletion E w)) :
    emb e (locGL E a w k) = locGL E n w (emb e k) := by
  simp only [locGL, st_corner_emb]

variable [IsCMField E]

private theorem st_lev {a n : ℕ} (e : Fin a ↪ Fin n) {bad : Set (UpperTheory.V.Cj.S.Pl E)} {K : Subgroup (GL (Fin n) (Af E))}
    (hK : Lev bad K) : Lev bad (K.comap (emb e)) := by
  refine ⟨hK.isOpen.preimage
    (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous E a n e).2.2, ?_, ?_⟩
  · intro u hu w
    have h := hK.int _ hu w
    rw [emb_map] at h
    exact st_mem_of_emb _ e h
  · intro w hw k hk
    change emb e (locGL E a w k) ∈ K
    rw [st_emb_loc]
    refine hK.loc w hw _ ?_
    obtain ⟨k, rfl⟩ := hk
    exact ⟨emb e k, emb_map e _ k⟩

private theorem st_arch {a n : ℕ} (e : Fin a ↪ Fin n) (k : archCompact E a) : embArch e k.1 ∈ archCompact E n := by
  have h := UpperTheory.blockEmbedding_adelic_norm_compat E a n e _ (Subgroup.mem_comap.1 k.2)
  rw [(UpperTheory.blockEmbedding_comm_infEmb_and_exp E a n e).1] at h
  exact Subgroup.mem_comap.2 h

private noncomputable def stJ {a n : ℕ} (e : Fin a ↪ Fin n) (k : Kinf E a) : Kinf E n :=
  (UpperTheory.V.Cm.cptEq E n).symm ⟨embArch e (UpperTheory.V.Cm.cptEq E a k).1, st_arch e _⟩

private theorem st_emb_inf {a n : ℕ} (e : Fin a ↪ Fin n) (k : Kinf E a) :
    emb e (infGL E a (Unitary.toUnits k)) = infGL E n (Unitary.toUnits (stJ e k)) := by
  rw [← UpperTheory.V.Cm.infEmb_cptEq, ← UpperTheory.V.Cm.infEmb_cptEq, stJ, MulEquiv.apply_symm_apply]
  exact (UpperTheory.blockEmbedding_comm_infEmb_and_exp E a n e).1 _

private theorem st_ct_fin {n r : ℕ} {K : Subgroup (GL (Fin n) (Af E))} {φ : Sm E n}
    (h : ∀ u ∈ K, ∀ g, φ.1 (g * finGL E n u) = φ.1 g) :
    ∀ u ∈ K, ∀ g, constantTerm r φ.1 (g * finGL E n u) = constantTerm r φ.1 g := by
  intro u hu g
  unfold constantTerm
  simp only [← mul_assoc, h u hu]

private theorem st_ct_inf {n r : ℕ} (W : Submodule ℂ (Kinf E n → ℂ)) (hW : FiniteDimensional ℂ W) {φ : Sm E n}
    (hc : Continuous φ.1) (h : ∀ g, (fun k : Kinf E n => φ.1 (g * infGL E n (Unitary.toUnits k))) ∈ W) (g : GA E n) :
    (fun k : Kinf E n => constantTerm r φ.1 (g * infGL E n (Unitary.toUnits k))) ∈ W := by
  refine @UpperTheory.locallyFinite_of_algMod_criterion _ (Kinf E n) (_) _ W hW (fun X k => φ.1 (unipGL X * (g * infGL E n (Unitary.toUnits k)))) (fun X => ?_)
    (fun k => integrableOn_constantTerm hc _)
  simpa only [mul_assoc] using h (unipGL X * g)

private theorem st_slice {a n : ℕ} (e : Fin a ↪ Fin n) {K : Subgroup (GL (Fin n) (Af E))} {W : Submodule ℂ (Kinf E n → ℂ)}
    {Φ : GA E n → ℂ} (h1 : ∀ u ∈ K, ∀ g, Φ (g * finGL E n u) = Φ g)
    (h2 : ∀ g, (fun k : Kinf E n => Φ (g * infGL E n (Unitary.toUnits k))) ∈ W) (f : Sm E a) (g₀ : GA E n)
    (hf : ∀ m, f.1 m = Φ (g₀ * emb e m)) :
    TypeB (K.comap (emb e)) (W.map (LinearMap.funLeft ℂ ℂ (stJ e))) f := by
  refine ⟨fun u hu g => ?_, fun g => ⟨_, h2 (g₀ * emb e g), funext fun k => ?_⟩⟩
  · rw [hf, hf, map_mul, st_emb_fin, ← mul_assoc]
    exact h1 _ hu _
  · simp only [LinearMap.funLeft_apply]
    rw [hf, map_mul, st_emb_inf, mul_assoc]

end Main

open UpperTheory.V.Af.Fin GroundTheory.Automorphic.AutomorphicForm in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.sliceT :
    SliceT := by
  intro E _ _ _ r s bad K W hL hW
  refine ⟨K.comap (emb (e1 r s)), W.map (LinearMap.funLeft ℂ ℂ (stJ (e1 r s))), K.comap (emb (e2 r s)),
    W.map (LinearMap.funLeft ℂ ℂ (stJ (e2 r s))), st_lev _ hL, Module.Finite.map W _, st_lev _ hL, Module.Finite.map W _,
    fun φ hφ hT => ?_⟩
  have hc : Continuous φ.1 := ((UpperTheory.V.Cm.isAutForm_iff φ).1 hφ).continuous
  have h1 := st_ct_fin (r := r) hT.1
  have h2 := st_ct_inf (r := r) W hW hc hT.2
  refine ⟨fun y f hf => st_slice _ h1 h2 f (emb (e2 r s) y) fun m => ?_,
    fun x f hf => st_slice _ h1 h2 f (emb (e1 r s) x) fun m => ?_⟩
  · rw [hf, ← emb_comm]
    rfl
  · rw [hf]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.SplitLim
section
open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp

private theorem rel_le_mono {s t : Multiset ℂ} {a b : ℝ} (hab : a ≤ b)
    (h : Multiset.Rel (fun x y => ‖x - y‖ ≤ a) s t) :
    Multiset.Rel (fun x y => ‖x - y‖ ≤ b) s t :=
  h.mono fun _ _ _ _ hxy => hxy.trans hab

private theorem rel_shift {s c : Multiset ℂ} {ε : ℝ} (α : ℂ)
    (h : Multiset.Rel (fun x y => ‖x - y‖ ≤ ε) (s.map (· + α)) c) :
    Multiset.Rel (fun x y => ‖x - y‖ ≤ ε) s (c.map (· - α)) := by
  rw [Multiset.rel_map_left] at h
  rw [Multiset.rel_map_right]
  refine h.mono fun x _ y _ hxy => ?_
  have : x - (y - α) = x + α - y := by ring
  rw [this]
  exact hxy

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.splitLim :
    SplitLim := by
  classical
  intro E _ _ _ m₀ α β
  let A : (E →+* ℂ) → Set (Multiset ℂ × Multiset ℂ) := fun t => {x | x.1 + x.2 = m₀ t}
  have hA : ∀ t, (A t).Finite := fun t => by
    refine ((Multiset.antidiagonal (m₀ t)).toFinset.finite_toSet).subset ?_
    intro x hx
    simpa [A, Multiset.mem_antidiagonal] using hx
  have hS : (Set.pi Set.univ A).Finite := Set.Finite.pi' hA |>.subset (fun σ hσ t => hσ t (Set.mem_univ t))
  let F : ((E →+* ℂ) → Multiset ℂ × Multiset ℂ) →
      ((E →+* ℂ) → Multiset ℂ) × ((E →+* ℂ) → Multiset ℂ) :=
    fun σ => (fun t => (σ t).1.map (· - α), fun t => (σ t).2.map (· - β))
  refine ⟨(hS.image F).toFinset, ?_⟩
  intro m m₁ m₂ hm hto
  let Good : ((E →+* ℂ) → Multiset ℂ × Multiset ℂ) → ℕ → ℕ → Prop := fun σ j k =>
    ∀ t, Multiset.Rel (fun x y => ‖x - y‖ ≤ 1 / ((j : ℝ) + 1)) (m₁ k t) ((F σ).1 t) ∧
      Multiset.Rel (fun x y => ‖x - y‖ ≤ 1 / ((j : ℝ) + 1)) (m₂ k t) ((F σ).2 t)
  have hmono : ∀ σ {i j : ℕ} {k : ℕ}, i ≤ j → Good σ j k → Good σ i k := by
    intro σ i j k hij h t
    have hle : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      Nat.one_div_le_one_div hij
    exact ⟨rel_le_mono hle (h t).1, rel_le_mono hle (h t).2⟩
  have step1 : ∀ j, ∀ᶠ k in atTop, ∃ σ ∈ Set.pi Set.univ A, Good σ j k := by
    intro j
    have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := Nat.one_div_pos_of_nat
    have hall : ∀ᶠ k in atTop, ∀ t, Multiset.Rel (fun x y => ‖x - y‖ ≤ 1 / ((j : ℝ) + 1)) (m k t) (m₀ t) :=
      eventually_all.2 fun t => hto t _ hpos
    filter_upwards [hall] with k hk
    have hsplit : ∀ t, ∃ x : Multiset ℂ × Multiset ℂ, x.1 + x.2 = m₀ t ∧
        Multiset.Rel (fun x y => ‖x - y‖ ≤ 1 / ((j : ℝ) + 1)) ((m₁ k t).map (· + α)) x.1 ∧
        Multiset.Rel (fun x y => ‖x - y‖ ≤ 1 / ((j : ℝ) + 1)) ((m₂ k t).map (· + β)) x.2 := by
      intro t
      have h := hk t
      rw [hm k t, Multiset.rel_add_left] at h
      obtain ⟨c₁, c₂, h₁, h₂, hc⟩ := h
      exact ⟨(c₁, c₂), hc.symm, h₁, h₂⟩
    choose σ hσ h₁ h₂ using hsplit
    exact ⟨σ, fun t _ => hσ t, fun t => ⟨rel_shift α (h₁ t), rel_shift β (h₂ t)⟩⟩
  have step2 : ∃ σ ∈ Set.pi Set.univ A, ∀ j, ∃ᶠ k in atTop, Good σ j k := by
    by_contra hcon
    have hJ : ∀ σ, ∃ j, σ ∈ Set.pi Set.univ A → ∀ᶠ k in atTop, ¬ Good σ j k := by
      intro σ
      by_cases hσ : σ ∈ Set.pi Set.univ A
      · by_contra hno
        refine hcon ⟨σ, hσ, fun j => ?_⟩
        intro hev
        exact hno ⟨j, fun _ => hev⟩
      · exact ⟨0, fun h => absurd h hσ⟩
    choose J hJ using hJ
    let N := hS.toFinset.sup J
    have hN : ∀ᶠ k in atTop, ∀ σ ∈ Set.pi Set.univ A, ¬ Good σ N k := by
      refine (Filter.eventually_all_finite hS).2 fun σ hσ => ?_
      filter_upwards [hJ σ hσ] with k hk hg
      exact hk (hmono σ (Finset.le_sup (f := J) (hS.mem_toFinset.2 hσ)) hg)
    obtain ⟨k, hk₁, hk₂⟩ := (hN.and (step1 N)).exists
    obtain ⟨σ, hσ, hg⟩ := hk₂
    exact hk₁ σ hσ hg
  obtain ⟨σ, hσ, hfreq⟩ := step2
  obtain ⟨s, hs, hgood⟩ := Filter.extraction_forall_of_frequently hfreq
  have hlim : ∀ (ε : ℝ), 0 < ε → ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) ≤ ε := by
    intro ε hε
    obtain ⟨j₀, hj₀⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop j₀] with k hk
    exact (Nat.one_div_le_one_div hk).trans hj₀.le
  refine ⟨F σ, ?_, s, hs, ?_, ?_⟩
  · simpa using Set.mem_image_of_mem F hσ
  · intro τ ε hε
    filter_upwards [hlim ε hε] with k hk
    exact rel_le_mono hk (hgood k τ).1
  · intro τ ε hε
    filter_upwards [hlim ε hε] with k hk
    exact rel_le_mono hk (hgood k τ).2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.TypeSat
section
open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.typeSat :
    TypeSat := by
  intro G _ W hW
  let W0 : Submodule ℂ (G → ℂ) :=
    { carrier := {f | ∀ a, (fun k => f (a * k)) ∈ W}
      add_mem' := fun {f g} hf hg a => W.add_mem (hf a) (hg a)
      zero_mem' := fun _ => W.zero_mem
      smul_mem' := fun c f hf a => W.smul_mem c (hf a) }
  have hle : W0 ≤ W := by
    intro f hf
    have h1 : (fun k => f (1 * k)) ∈ W := hf 1
    simpa using h1
  haveI : FiniteDimensional ℂ W0 := Submodule.finiteDimensional_of_le hle
  have hstab : ∀ (a : G) (f : G → ℂ), f ∈ W0 → (fun k => f (a * k)) ∈ W0 := by
    intro a f hf c
    have h1 : (fun k => f ((a * c) * k)) ∈ W := hf (a * c)
    simpa [mul_assoc] using h1
  let L : G → (W0 →ₗ[ℂ] W0) := fun a =>
    { toFun := fun f => ⟨fun k => f.1 (a * k), hstab a f.1 f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let b := Module.finBasis ℂ W0
  let c : (Fin (Module.finrank ℂ W0) × Fin (Module.finrank ℂ W0)) → G → ℂ :=
    fun p k => b.repr (L k (b p.2)) p.1
  refine ⟨Submodule.span ℂ (Set.range c),
    FiniteDimensional.span_of_finite ℂ (Set.finite_range c), ?_⟩
  intro f hf y
  let F : W0 := ⟨f, hf⟩
  have key : (fun k => f (k * y)) =
      ∑ i, ∑ j, ((b i).1 y * b.repr F j) • c (i, j) := by
    funext k
    have h3 : L k F = ∑ j, b.repr F j • L k (b j) := by
      conv_lhs => rw [← b.sum_repr F]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul]
    have h4 : ∀ i, b.repr (L k F) i = ∑ j, b.repr F j * c (i, j) k := by
      intro i
      rw [h3]
      simp [c, Finsupp.finsetSum_apply]
    have h5 : f (k * y) = (L k F).1 y := rfl
    have h6 : (L k F).1 y = ∑ i, b.repr (L k F) i * (b i).1 y := by
      have h7 := congrArg (fun v : W0 => (v : G → ℂ) y) (b.sum_repr (L k F))
      simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, Submodule.coe_smul,
        Pi.smul_apply, smul_eq_mul] at h7
      exact h7.symm
    rw [h5, h6]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h4, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [key]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
end

