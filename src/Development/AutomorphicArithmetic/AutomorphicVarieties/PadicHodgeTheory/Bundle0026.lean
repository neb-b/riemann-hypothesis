module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PosExact
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0021

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsTotallyRealPrimitiveElementPadicFiniteExt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

section
open Polynomial IntermediateField Filter Topology

private theorem totally_real_of_sign_changes (n : ℕ) (g : ℚ[X]) (hg : g.Monic) (hd : g.natDegree = n)
    (hs : ∀ j < n, aeval ((j : ℝ) - 1 / 2) g * aeval ((j : ℝ) + 1 / 2) g < 0) :
    ∀ z : ℂ, aeval z g = 0 → z.im = 0 := by
  have hroot : ∀ j : Fin n, ∃ r : ℝ, ((j : ℕ) : ℝ) - 1 / 2 < r ∧ r < ((j : ℕ) : ℝ) + 1 / 2 ∧
      aeval r g = 0 := by
    intro j
    have hc : ContinuousOn (fun x : ℝ => aeval x g)
        (Set.Icc (((j : ℕ) : ℝ) - 1 / 2) (((j : ℕ) : ℝ) + 1 / 2)) :=
      (Polynomial.continuous_aeval g).continuousOn
    have hle : ((j : ℕ) : ℝ) - 1 / 2 ≤ ((j : ℕ) : ℝ) + 1 / 2 := by linarith
    rcases mul_neg_iff.1 (hs j j.2) with h | h
    · obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo' hle hc ⟨h.2, h.1⟩
      exact ⟨r, hr.1, hr.2, hr0⟩
    · obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo hle hc ⟨h.1, h.2⟩
      exact ⟨r, hr.1, hr.2, hr0⟩
  choose r hr1 hr2 hr0 using hroot
  have hinj : Function.Injective fun j : Fin n => ((r j : ℝ) : ℂ) := by
    intro i j hij
    have hij' : r i = r j := Complex.ofReal_injective hij
    have h1 : ((i : ℕ) : ℝ) < (j : ℕ) + 1 := by linarith [hr1 i, hr2 j]
    have h2 : ((j : ℕ) : ℝ) < (i : ℕ) + 1 := by linarith [hr1 j, hr2 i]
    have h1' : (i : ℕ) < (j : ℕ) + 1 := by exact_mod_cast h1
    have h2' : (j : ℕ) < (i : ℕ) + 1 := by exact_mod_cast h2
    exact Fin.ext (by omega)
  intro z hz
  by_contra hzim
  classical
  have hne : g.map (algebraMap ℚ ℂ) ≠ 0 := (hg.map _).ne_zero
  have hnot : z ∉ (Finset.univ : Finset (Fin n)).image fun j : Fin n => ((r j : ℝ) : ℂ) := by
    intro hmem
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hmem
    exact hzim (by rw [← hj]; simp)
  have hcard := Polynomial.card_le_degree_of_subset_roots (p := g.map (algebraMap ℚ ℂ))
    (Z := insert z ((Finset.univ : Finset (Fin n)).image fun j : Fin n => ((r j : ℝ) : ℂ))) (by
      intro x hx
      rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap]
      rcases Finset.mem_insert.1 (Finset.mem_def.2 hx) with rfl | hx
      · exact hz
      · obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hx
        rw [← hj]
        have := Polynomial.aeval_algebraMap_apply ℂ (r j) g
        rw [hr0 j, map_zero] at this
        exact this)
  rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hinj,
    Polynomial.natDegree_map, hd] at hcard
  simp at hcard

private theorem sign_change_between_integers (n j : ℕ) (hj : j < n) :
    aeval ((j : ℝ) - 1 / 2) (∏ i ∈ Finset.range n, (X - C (i : ℚ)) : ℚ[X]) *
      aeval ((j : ℝ) + 1 / 2) (∏ i ∈ Finset.range n, (X - C (i : ℚ)) : ℚ[X]) < 0 := by
  rw [map_prod, map_prod, ← Finset.prod_mul_distrib,
    ← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hj)]
  refine mul_neg_of_neg_of_pos ?_ (Finset.prod_pos fun i hi => ?_)
  · simp
  · have hij : i ≠ j := (Finset.mem_erase.1 hi).1
    simp only [map_sub, aeval_X, aeval_C, eq_ratCast, Rat.cast_natCast]
    rcases lt_or_gt_of_ne hij with h | h
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      apply mul_pos <;> linarith
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      apply mul_pos_of_neg_of_neg <;> linarith

private theorem approx_monic_totally_real_rational (l : ℕ) [Fact l.Prime] (f : ℚ_[l][X]) (hf : f.Monic)
    (ε : ℝ) (hε : ε > 0) :
    ∃ g : ℚ[X], g.Monic ∧ f.natDegree = g.natDegree ∧
      (∀ i, ‖(g.map (algebraMap ℚ ℚ_[l])).coeff i - f.coeff i‖ < ε) ∧
      ∀ z : ℂ, aeval z g = 0 → z.im = 0 := by
  obtain ⟨g₀, gmon, gdeg, gcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt
      (Padic.denseRange_ratCast l) hf hε
  set n := g₀.natDegree with hn
  set h : ℚ[X] := ∏ i ∈ Finset.range n, (X - C (i : ℚ)) with hh
  have hmon : h.Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hdeg : h.natDegree = n := by
    rw [hh, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
    simp only [natDegree_X_sub_C]
    simp
  have hdlt : (g₀ - h).degree < h.degree := by
    have e : g₀.degree = h.degree := by
      rw [degree_eq_natDegree gmon.ne_zero, degree_eq_natDegree hmon.ne_zero, hdeg]
    rw [← e]
    exact degree_sub_lt e gmon.ne_zero (by rw [gmon.leadingCoeff, hmon.leadingCoeff])
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  let u : ℕ → ℚ := fun N => (1 + (l : ℚ) ^ N)⁻¹
  have huR : Tendsto (fun N => ((u N : ℚ) : ℝ)) atTop (𝓝 0) := by
    have : Tendsto (fun N : ℕ => 1 + (l : ℝ) ^ N) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop_atTop_of_one_lt hl)
    have := this.inv_tendsto_atTop
    refine this.congr fun N => ?_
    simp [u]
  have huP : Tendsto (fun N => ((u N : ℚ) : ℚ_[l])) atTop (𝓝 1) := by
    have h1 : Tendsto (fun N : ℕ => (l : ℚ_[l]) ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
    have h2 := ((tendsto_const_nhds (x := (1 : ℚ_[l]))).add h1).inv₀ (by simp)
    simp only [add_zero, inv_one] at h2
    refine h2.congr fun N => ?_
    simp [u]
  have hG : ∀ N, (h + C (u N) * (g₀ - h)).Monic ∧ (h + C (u N) * (g₀ - h)).natDegree = n := by
    intro N
    have hlt : (C (u N) * (g₀ - h)).degree < h.degree := by
      rw [← smul_eq_C_mul]
      exact (degree_smul_le _ _).trans_lt hdlt
    exact ⟨hmon.add_of_left hlt, by rw [natDegree_add_eq_left_of_degree_lt hlt, hdeg]⟩
  have e1 : ∀ᶠ N in atTop, ∀ j ∈ Finset.range n,
      aeval ((j : ℝ) - 1 / 2) (h + C (u N) * (g₀ - h)) *
        aeval ((j : ℝ) + 1 / 2) (h + C (u N) * (g₀ - h)) < 0 := by
    rw [Filter.eventually_all_finset]
    intro j hj
    have hev : ∀ x : ℝ, Tendsto (fun N => aeval x (h + C (u N) * (g₀ - h))) atTop
        (𝓝 (aeval x h)) := by
      intro x
      have := (tendsto_const_nhds (x := aeval x h)).add (huR.mul_const (aeval x (g₀ - h)))
      simp only [zero_mul, add_zero] at this
      refine this.congr fun N => ?_
      simp only [map_add (f := _), map_mul, aeval_C, eq_ratCast]
    exact ((hev _).mul (hev _)).eventually
      (gt_mem_nhds (sign_change_between_integers n j (Finset.mem_range.1 hj)))
  have e2 : ∀ᶠ N in atTop, ∀ i ∈ Finset.range (n + 1),
      ‖((h + C (u N) * (g₀ - h)).map (algebraMap ℚ ℚ_[l])).coeff i - f.coeff i‖ < ε := by
    rw [Filter.eventually_all_finset]
    intro i _
    have hev : Tendsto (fun N => ((h + C (u N) * (g₀ - h)).map (algebraMap ℚ ℚ_[l])).coeff i)
        atTop (𝓝 ((g₀.map (algebraMap ℚ ℚ_[l])).coeff i)) := by
      have := (tendsto_const_nhds (x := ((h.coeff i : ℚ) : ℚ_[l]))).add
        (huP.mul_const (((g₀.coeff i : ℚ) : ℚ_[l]) - ((h.coeff i : ℚ) : ℚ_[l])))
      simp only [one_mul, add_sub_cancel] at this
      simp only [coeff_map, coeff_add, coeff_C_mul, coeff_sub, eq_ratCast]
      refine this.congr fun N => ?_
      push_cast
      ring
    exact ((hev.sub_const _).norm).eventually (gt_mem_nhds (gcoeff i))
  obtain ⟨N, hN1, hN2⟩ := (e1.and e2).exists
  refine ⟨h + C (u N) * (g₀ - h), (hG N).1, by rw [(hG N).2, gdeg], fun i => ?_,
    totally_real_of_sign_changes n _ (hG N).1 (hG N).2 fun j hj => hN1 j (Finset.mem_range.2 hj)⟩
  by_cases hi : i < n + 1
  · exact hN2 i (Finset.mem_range.2 hi)
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_map, (hG N).2]; omega),
      coeff_eq_zero_of_natDegree_lt (by rw [gdeg]; omega)]
    simpa using hε

private theorem krasner_totally_real_generator (l : ℕ) [Fact l.Prime] (α : PadicAlgCl l) :
    ∃ β : PadicAlgCl l, ∃ g : ℚ[X], g.Monic ∧ g.natDegree = (minpoly ℚ_[l] α).natDegree ∧
      aeval β g = 0 ∧ (∀ z : ℂ, aeval z g = 0 → z.im = 0) ∧ α ∈ ℚ_[l]⟮β⟯ := by
  have hint : ∀ z : PadicAlgCl l, IsIntegral ℚ_[l] z := fun z =>
    (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  have fmon : (minpoly ℚ_[l] α).Monic := minpoly.monic (hint α)
  have fa0 : (minpoly ℚ_[l] α).aeval α = 0 := minpoly.aeval _ _
  have hfin : ({x' | IsConjRoot ℚ_[l] α x' ∧ α ≠ x'} : Set (PadicAlgCl l)).Finite := by
    refine ((minpoly ℚ_[l] α).rootSet_finite (PadicAlgCl l)).subset fun x' hx' => ?_
    exact (isConjRoot_iff_mem_minpoly_rootSet (hint α)).1 hx'.1
  have hop : IsOpen (⋂ x' ∈ ({x' | IsConjRoot ℚ_[l] α x' ∧ α ≠ x'} : Set (PadicAlgCl l)),
      {y : PadicAlgCl l | ‖α - y‖ < ‖α - x'‖}) :=
    hfin.isOpen_biInter fun x' _ => isOpen_lt (by fun_prop) continuous_const
  have hmem : α ∈ (⋂ x' ∈ ({x' | IsConjRoot ℚ_[l] α x' ∧ α ≠ x'} : Set (PadicAlgCl l)),
      {y : PadicAlgCl l | ‖α - y‖ < ‖α - x'‖}) := by
    simp only [Set.mem_iInter, Set.mem_setOf_eq, sub_self, norm_zero, norm_pos_iff, sub_ne_zero]
    exact fun x' h => h.2
  obtain ⟨δ, δpos, hball⟩ := Metric.isOpen_iff.1 hop α hmem
  have hn : (minpoly ℚ_[l] α).natDegree ≠ 0 := (minpoly.natDegree_pos (hint α)).ne'
  have hε : (δ / (max ‖α‖ 1)) ^ (minpoly ℚ_[l] α).natDegree /
      ((minpoly ℚ_[l] α).natDegree + 1) > 0 := by positivity
  obtain ⟨g, gmon, gdeg, gcoeff, greal⟩ := approx_monic_totally_real_rational l _ fmon _ hε
  obtain ⟨β, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt (L := PadicAlgCl l)
      hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff (IsAlgClosed.splits _)
  have hab : ‖α - β‖ < δ := by
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
        ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀] at hab
    · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖α‖ 1) > 0).ne'] using hab
    · simp [hn]
    · positivity
  have hβU := hball
    (show β ∈ Metric.ball α δ by rw [Metric.mem_ball, dist_comm, dist_eq_norm]; exact hab)
  have hgβ : aeval β g = 0 := by
    rw [Polynomial.mem_aroots] at hb
    simpa [Polynomial.aeval_map_algebraMap] using hb.2
  refine ⟨β, g, gmon, gdeg.symm, hgβ, greal, ?_⟩
  refine IsKrasner.krasner (minpoly.irreducible (hint α)).separable (IsAlgClosed.splits _)
    (hint β) fun x' h1 h2 => ?_
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hβU
  exact hβU x' ⟨h1, h2⟩

private theorem exists_totally_real_generator (l : ℕ) [Fact l.Prime]
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    ∃ (β : PadicAlgCl l) (g : ℚ[X]), g.Monic ∧ aeval β g = 0 ∧
      (∀ z : ℂ, aeval z g = 0 → z.im = 0) ∧ ℚ_[l]⟮β⟯ = K := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ_[l] K
  have hKα : K = ℚ_[l]⟮(α : PadicAlgCl l)⟯ := by
    rw [← IntermediateField.lift_adjoin_simple, hα, IntermediateField.lift_top]
  obtain ⟨β, g, gmon, gdeg, hgβ, greal, hαβ⟩ := krasner_totally_real_generator l (α : PadicAlgCl l)
  refine ⟨β, g, gmon, hgβ, greal, ?_⟩
  have hint : ∀ z : PadicAlgCl l, IsIntegral ℚ_[l] z := fun z =>
    (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  rw [hKα]
  symm
  haveI : FiniteDimensional ℚ_[l] ℚ_[l]⟮β⟯ := IntermediateField.adjoin.finiteDimensional (hint β)
  refine IntermediateField.eq_of_le_of_finrank_le
    (IntermediateField.adjoin_simple_le_iff.2 hαβ) ?_
  rw [IntermediateField.adjoin.finrank (hint β), IntermediateField.adjoin.finrank (hint _), ← gdeg]
  have hg0 : g.map (algebraMap ℚ ℚ_[l]) ≠ 0 := (gmon.map _).ne_zero
  have hdvd : minpoly ℚ_[l] β ∣ g.map (algebraMap ℚ ℚ_[l]) :=
    minpoly.dvd _ _ (by rw [Polynomial.aeval_map_algebraMap]; exact hgβ)
  calc (minpoly ℚ_[l] β).natDegree ≤ (g.map (algebraMap ℚ ℚ_[l])).natDegree :=
        Polynomial.natDegree_le_of_dvd hdvd hg0
    _ = g.natDegree := g.natDegree_map _

end

theorem UpperTheory.exists_totally_real_primitive_element_padic_finite_ext :
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∃ (β : Om l) (g : Polynomial ℚ), g.Monic ∧ Polynomial.aeval β g = 0 ∧ (∀ z : ℂ, Polynomial.aeval z g = 0 → z.im = 0) ∧ IntermediateField.adjoin ℚ_[l] {β} = K.1 := by
  intro l _ K
  haveI := K.2
  exact exists_totally_real_generator l K.1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineTriangularIffMemFiniteCocyclesOfCha
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private theorem coc {G B : Type} [Group G] [CommRing B] {κ : Fin 3 → G →* Bˣ} {x y z : G → B}
    {ρ : G →* GL (Fin 3) B}
    (h : ∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) :
    (∀ g g', x (g * g') = x g + ((κ 0 / κ 1) g : Bˣ) * x g') ∧
    ∀ g g', z (g * g') = z g + ((κ 0 / κ 2) g : Bˣ) * z g' + x g * ((κ 1 / κ 2) g : Bˣ) * y g' := by
  have e : ∀ (i j : Fin 3) g, (((κ i / κ j) g : Bˣ) : B) * κ j g = κ i g := fun i j g => by
    rw [← Units.val_mul, MonoidHom.div_apply, div_mul_cancel]
  have m : ∀ g g', triM (fun i => κ i (g * g')) (x (g * g')) (y (g * g')) (z (g * g')) =
      triM (fun i => κ i g) (x g) (y g) (z g) * triM (fun i => κ i g') (x g') (y g') (z g') := fun g g' => by
    rw [← h, ← h, ← h, map_mul, Units.val_mul]
  refine ⟨fun g g' => ?_, fun g g' => ?_⟩
  · have h1 := congrFun (congrFun (m g g') 0) 1
    simp only [triM, Matrix.mul_apply, Fin.sum_univ_three, map_mul, Units.val_mul] at h1
    simp at h1
    apply (κ 1 g * κ 1 g').isUnit.mul_right_cancel
    rw [Units.val_mul, h1, ← e 0 1 g]
    ring
  · have h1 := congrFun (congrFun (m g g') 0) 2
    simp only [triM, Matrix.mul_apply, Fin.sum_univ_three, map_mul, Units.val_mul] at h1
    simp at h1
    apply (κ 2 g * κ 2 g').isUnit.mul_right_cancel
    rw [Units.val_mul, h1, ← e 0 2 g, ← e 1 2 g]
    ring

private theorem mem_ker_smul {E B V : Type} [Field E] [CommRing B] [Algebra E B] [AddCommGroup V] [Module B V]
    (π : B →ₐ[E] E) {a : B} (ha : π a = 0) (v : V) :
    a • v ∈ (RingHom.ker (π : B →+* E)) • (⊤ : Submodule B V) :=
  Submodule.smul_mem_smul (by simpa using ha) trivial

theorem UpperTheory.isCrystalline_triangular_iff_mem_finiteCocycles_of_charData :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) {e : ℕ} {ψ : G →* Eˣ} {κ : Fin 3 → G →* Bˣ}, Chars φ π e ψ κ → ∀ (x y z : G → B) (ρ : G →* GL (Fin 3) B), Continuous x → Continuous y → Continuous z → (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) → (∀ g, π (x g) = 0) → IsCr φ (colRep ρ) → ∀ (z' : G → B) (ρ' : G →* GL (Fin 3) B), Continuous z' → (∀ g, (ρ' g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z' g)) → z' - z ∈ Z1 (chRep (κ 0 / κ 2)) ∧ (IsCr φ (colRep ρ') ↔ z' - z ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep (κ 0 / κ 2))) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ e ψ κ hκ x y z ρ hxc hyc hzc hρ hx0 hcr z' ρ' hzc' hρ'
  obtain ⟨hx, hz⟩ := coc hρ
  obtain ⟨-, hz'⟩ := coc hρ'
  have : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  have := contConstSMul_alg (B := B) E
  have hZ : z' - z ∈ Z1 (chRep (κ 0 / κ 2)) := by
    refine ⟨hzc'.sub hzc, fun g h => ?_⟩
    simp only [Pi.sub_apply, hz, hz', chRep_apply]
    ring
  refine ⟨hZ, ?_⟩
  have w0 : wt1 0 = 1 := rfl
  have w1 : wt1 1 = 0 := rfl
  have w2 : wt1 2 = -1 := rfl
  have cd : ∀ i j, Continuous fun g => (((κ i / κ j) g : Bˣ) : B) := fun i j => cont_char_div (hκ.cont i) (hκ.cont j)
  have crk : ∀ i, IsCr φ (chRep (κ i)) := fun i =>
    crUnr φ hφ _ (contAction_chRep (hκ.cont i)) (e * wt1 i) fun g hg v => by
      rw [chRep_apply, hκ.ine g hg, smul_eq_mul]
  have crd : ∀ i j, IsCr φ (chRep (κ i / κ j)) := fun i j =>
    crUnr φ hφ _ (contAction_chRep (cd i j)) (e * wt1 i - e * wt1 j) fun g hg v => by
      rw [chRep_apply, MonoidHom.div_apply, hκ.ine g hg, hκ.ine g hg, zpow_sub, div_eq_mul_inv, smul_eq_mul]
  have red : ∀ i j g, π (((κ i / κ j) g : Bˣ) : B) = (((ψ ^ (wt1 i - wt1 j)) g : Eˣ) : E) := fun i j g => by
    have e1 : (((κ i / κ j) g : Bˣ) : B) * κ j g = κ i g := by
      rw [← Units.val_mul, MonoidHom.div_apply, div_mul_cancel]
    have e2 := congrArg π e1
    rw [map_mul, hκ.red, hκ.red] at e2
    apply (ψ g ^ wt1 j).isUnit.mul_right_cancel
    rw [e2, ← Units.val_mul, MonoidHom.zpow_apply, ← zpow_add, sub_add_cancel]
  have hw : ∀ n : ℤ, 1 ≤ n → (ψ ^ n) ∈ {κ : G →* Eˣ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w} := fun n hn => by
    have := hκ.e_pos
    refine ⟨e * n, by nlinarith, ⊤, by simp, fun g _ hg => ?_⟩
    rw [MonoidHom.zpow_apply, hκ.wt g hg, zpow_mul, zpow_natCast]
  have cρ : ContAction (colRep ρ) := contAction_colRep (by
    simp only [hρ]
    exact continuous_triM hκ.cont hxc hyc hzc)
  have c2 := contAction_charExtension_of_continuous_cocycle (hκ.cont 0) (hκ.cont 1) hx hxc
  have cr2 : IsCr φ (ext2 (κ 0) (κ 1) x hx) := by
    let f : B × B →ₗ[ℚ_[l]] (Fin 3 → B) :=
      { toFun := fun v => ![v.1, v.2, 0]
        map_add' := fun v w => by ext i; fin_cases i <;> simp
        map_smul' := fun c v => by ext i; fin_cases i <;> simp }
    refine ((isCrys_isDR_sub_quot φ hφ _ _ c2 cρ f fun g v => ?_).1 fun v w h => ?_).1 hcr
    · ext i
      fin_cases i <;> simp [f, characterExtensionRep_apply, colRep_apply, hρ, triM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · exact Prod.ext (congrFun h 0) (congrFun h 1)
  have hxf := (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (hκ.cont 0) (hκ.cont 1) x hx hxc (crk 0) (crk 1)).1 cr2
  have ed : (κ 0 / κ 2) / (κ 1 / κ 2) = κ 0 / κ 1 := div_div_div_cancel_right _ _ _
  have hx' : ∀ g h, x (g * h) = x g + (((κ 0 / κ 2) / (κ 1 / κ 2)) g : Bˣ) * x h := by rw [ed]; exact hx
  have eM : twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx) = ext2 (κ 0 / κ 2) (κ 1 / κ 2) x hx' := by
    refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
    simp only [twist_apply, characterExtensionRep_apply, div_eq_mul_inv, MonoidHom.mul_apply, Units.val_mul, Prod.smul_mk, smul_eq_mul]
    ext <;> simp only [] <;> ring
  have k1 := (UpperTheory.isCrystalline_upperTriangular_iff_mem_finiteCocycles φ hφ κ hκ.cont x y z ρ hxc hyc hzc hρ hx cr2 (crk 2)).1 hcr
  have k2 := UpperTheory.isCrystalline_upperTriangular_iff_mem_finiteCocycles φ hφ κ hκ.cont x y z' ρ' hxc hyc hzc' hρ' hx cr2 (crk 2)
  rw [eM] at k1 k2
  set M := ext2 (κ 0 / κ 2) (κ 1 / κ 2) x hx' with hM
  have cM : ContAction M := contAction_charExtension_of_continuous_cocycle (cd 0 2) (cd 1 2) hx' hxc
  have crM : IsCr φ M :=
    (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (cd 0 2) (cd 1 2) x hx' hxc (crd 0 2) (crd 1 2)).2 (by rw [ed]; exact hxf)
  have cχ := contAction_chRep (cd 0 2)
  have inl : ∀ g v, LinearMap.inl E B B (chRep (κ 0 / κ 2) g v) = M g (LinearMap.inl E B B v) := fun g v => by
    simp [hM, characterExtensionRep_apply, chRep_apply]
  have pχ : Positive φ (resCoef E (chRep (κ 0 / κ 2))) := by
    refine ⟨(isCrys_isDR_restrict_openSubgroup φ hφ _ cχ).1 (crd 0 2), UpperTheory.filtBy_restrictScalars_of_residual_characters π hπ _ _ (fun _ : Unit => (1 : B))
      (fun _ => ψ ^ (wt1 0 - wt1 2)) (by simp) (fun _ => hw _ (by decide)) fun g _ => ?_⟩
    have := mem_ker_smul π (a := ((κ 0 / κ 2) g : Bˣ) - algebraMap E B ((ψ ^ (wt1 0 - wt1 2)) g : Eˣ))
      (by rw [map_sub, red, AlgHom.commutes]; simp) (1 : B)
    rwa [sub_smul, algebraMap_smul] at this
  have pM : Positive φ (resCoef E M) := by
    refine ⟨(isCrys_isDR_restrict_openSubgroup φ hφ _ cM).1 crM, UpperTheory.filtBy_restrictScalars_of_residual_characters π hπ _ _ (![(1, 0), (0, 1)] : Fin 2 → B × B)
      ![ψ ^ (wt1 0 - wt1 2), ψ ^ (wt1 1 - wt1 2)] ?_ (fun j => ?_) fun g j => ?_⟩
    · refine eq_top_iff.2 fun v _ => ?_
      have : v = v.1 • ((1, 0) : B × B) + v.2 • ((0, 1) : B × B) := by simp
      rw [this]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    · fin_cases j
      · exact hw _ (by decide)
      · exact hw _ (by decide)
    · have t : ∀ i (v : B × B), _ := fun i v =>
        mem_ker_smul π (a := ((κ i / κ 2) g : Bˣ) - algebraMap E B ((ψ ^ (wt1 i - wt1 2)) g : Eˣ))
          (by rw [map_sub, red, AlgHom.commutes]; simp) v
      fin_cases j
      · convert t 0 (1, 0) using 1
        rw [sub_smul, algebraMap_smul]
        simp [hM, characterExtensionRep_apply]
      · convert add_mem (t 1 (0, 1)) (mem_ker_smul π (a := x g * ((κ 1 / κ 2) g : Bˣ))
          (by rw [map_mul, hx0, zero_mul]) ((1, 0) : B × B)) using 1
        rw [sub_smul, algebraMap_smul]
        simp [hM, characterExtensionRep_apply]
  have dif : (fun g => (z' g, y g)) - (fun g => (z g, y g)) = fun g => LinearMap.inl E B B ((z' - z) g) := by
    funext g
    simp
  rw [k2]
  constructor
  · intro h
    have h1 := sub_mem h k1
    rw [dif] at h1
    have h2 := (z1fMap φ M (resCoef E M)).2 LinearMap.id (fun _ _ => rfl) _ h1
    have h3 := (posExact hP φ hφ (resCoef E (chRep (κ 0 / κ 2))) (resCoef E M) cχ cM pχ (LinearMap.inl E B B) inl).2 LinearMap.inl_injective pM _ hZ h2
    exact (z1fMap φ (resCoef E (chRep (κ 0 / κ 2))) (chRep (κ 0 / κ 2))).2 LinearMap.id (fun _ _ => rfl) _ h3
  · intro h
    have h1 := (z1fMap φ _ M).2 ((LinearMap.inl E B B).restrictScalars ℚ_[l]) inl _ h
    have h2 := add_mem h1 k1
    convert h2 using 1
    funext g
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TorsionDatumFiniteCocyclesBaseChange
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private theorem multiplicity_one_positive {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ}
    (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B]
    [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E)
    (hπ : ∀ a, π a = 0 → IsNilpotent a) (T : Tor η B) (hT : T.Good π Ψ) :
    Positive (MonoidHom.id (GQ l)) (resCoef E T.M1) := by
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  have hc : ContAction (resCoef E T.M1) := T.contAction_torus_module hD.ηlc hT.cont hT.cont_inv
  have w0 : wt1 (0 : Fin 3) = 1 := by decide
  have w1 : wt1 (1 : Fin 3) = 0 := by decide
  have w2 : wt1 (2 : Fin 3) = -1 := by decide
  have hid : IsOpenEmbedding (MonoidHom.id (GQ l)) := IsOpenEmbedding.id
  refine ⟨?_, ?_⟩
  · have hφ : IsOpenEmbedding ((MonoidHom.id (GQ l)).comp H.subtype) := hD.isOpen.isOpenEmbedding_subtypeVal
    have hcH : ContAction ((resCoef E T.M1).comp H.subtype : Representation E H (B × B)) :=
      Continuous.comp (g := fun p : GQ l × B × B => resCoef E T.M1 p.1 p.2)
        (f := fun p : H × B × B => ((p.1 : GQ l), p.2)) hc (by fun_prop)
    rw [((isCrys_isDR_restrict_openSubgroup _ hid _ hc).2 H hD.isOpen).2]
    refine (isCrys_isDR_restrict_openSubgroup _ hφ _ hcH).1 (crUnr _ hφ _ hcH e fun g hg x => ?_)
    have hg' : (g : GQ l) ∈ Iq l := hg
    have hu : ∀ i, T.t g i = Units.map (algebraMap E B : E →* B) (Ψ g ^ wt1 i) := fun i =>
      Units.ext (hT.ine g hg' i)
    change T.M1 g x = ((cycA l l E g ^ (e : ℤ) : Eˣ) : E) • x
    rw [zpow_natCast, ← hD.ΨH g g.2 hg', Tor.adjointSuperdiagRep_apply, if_pos (hD.ηH g g.2)]
    simp only [hu, w0, w1, w2, ← map_div]
    ext <;> simp [Algebra.smul_def]
  · let ε : GQ l →* Eˣ := (Units.map (Int.castRingHom E : ℤ →* E)).comp η
    have h2 : (2 : B) * algebraMap ℚ_[l] B (1 / 2) = 1 := by
      rw [← map_ofNat (algebraMap ℚ_[l] B) 2, ← map_mul]
      norm_num
    refine UpperTheory.filtBy_restrictScalars_of_residual_characters π hπ T.M1 _ ![((1 : B), (1 : B)), (1, -1)] ![ε * Ψ, Ψ] ?_ ?_ ?_
    · rw [eq_top_iff]
      rintro ⟨a, b⟩ -
      have : (a, b) = (algebraMap ℚ_[l] B (1 / 2) * (a + b)) • ((1 : B), (1 : B)) +
          (algebraMap ℚ_[l] B (1 / 2) * (a - b)) • ((1 : B), (-1 : B)) := by
        ext
        · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
          linear_combination (-a) * h2
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
          linear_combination (-b) * h2
      rw [this]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    · have he : (1 : ℤ) ≤ e := by exact_mod_cast hD.e_pos
      intro j
      refine ⟨e, he, H, hD.isOpen, fun g hg hI => ?_⟩
      have h1 := hD.ΨH g hg hI
      fin_cases j
      · simp [ε, hD.ηH g hg, h1]
      · simp [h1]
    · have key : ∀ v : B × B, π v.1 = 0 → π v.2 = 0 →
          v ∈ (RingHom.ker (π : B →+* E)) • (⊤ : Submodule B (B × B)) := by
        rintro ⟨a, b⟩ ha hb
        have : (a, b) = a • ((1 : B), (0 : B)) + b • ((0 : B), (1 : B)) := by simp
        rw [this]
        exact add_mem (Submodule.smul_mem_smul ha trivial) (Submodule.smul_mem_smul hb trivial)
      intro g j
      have hu : ∀ i, Units.map (π : B →* E) (T.t g i) = Ψ g ^ wt1 i := fun i => Units.ext (hT.red g i)
      have ha : π ((T.t g 0 / T.t g 1 : Bˣ) : B) = Ψ g := by
        have : Units.map (π : B →* E) (T.t g 0 / T.t g 1) = Ψ g := by simp [map_div, hu, w0, w1]
        exact congrArg Units.val this
      have hb : π ((T.t g 1 / T.t g 2 : Bˣ) : B) = Ψ g := by
        have : Units.map (π : B →* E) (T.t g 1 / T.t g 2) = Ψ g := by simp [map_div, hu, w1, w2]
        exact congrArg Units.val this
      have hn : ((-1 : ℤˣ) = 1) = False := by decide
      rw [Tor.adjointSuperdiagRep_apply]
      generalize ((T.t g 0 / T.t g 1 : Bˣ) : B) = a at ha ⊢
      generalize ((T.t g 1 / T.t g 2 : Bˣ) : B) = b at hb ⊢
      apply key <;> rcases Int.units_eq_one_or (η g) with hg | hg <;> fin_cases j <;>
        simp [ε, hg, hn, ha, hb, Algebra.smul_def]

theorem UpperTheory.torsionDatum_finiteCocycles_baseChange :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ} (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) {B' : Type} [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [TopologicalSpace B'] [IsModuleTopology ℚ_[l] B'] [IsTopologicalRing B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] [Algebra E B'] [IsScalarTower ℚ_[l] E B'] (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → ∀ (T : Tor η B) (T' : Tor η B'), T.Good π Ψ → T'.Good π' Ψ → (∀ g i, p (T.t g i : B) = (T'.t g i : B')) → ∀ β' ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) T'.M1, ∃ β ∈ UpperTheory.V.Loc.finiteCocycles (MonoidHom.id (GQ l)) T.M1, ∀ g, p (β g).1 = (β' g).1 ∧ p (β g).2 = (β' g).2 := by
  intro hP l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' _ p hp T T' hT hT' ht β' hβ'
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  haveI : ContinuousConstSMul E B' := contConstSMul_alg E
  have hc : ContAction (resCoef E T.M1) := T.contAction_torus_module hD.ηlc hT.cont hT.cont_inv
  have hc' : ContAction (resCoef E T'.M1) := T'.contAction_torus_module hD.ηlc hT'.cont hT'.cont_inv
  have hu : ∀ g i j, p ((T.t g i / T.t g j : Bˣ) : B) = ((T'.t g i / T'.t g j : B'ˣ) : B') := fun g i j => by
    have h : ∀ i, Units.map (p : B →* B') (T.t g i) = T'.t g i := fun i => Units.ext (ht g i)
    rw [← h, ← h, ← map_div]
    rfl
  obtain ⟨β, hβ, hpβ⟩ := (posExact hP (MonoidHom.id (GQ l)) IsOpenEmbedding.id (resCoef E T.M1) (resCoef E T'.M1)
    hc hc' (multiplicity_one_positive hD π hπ T hT) (p.toLinearMap.prodMap p.toLinearMap) (fun g x => by
      change Prod.map p p (T.M1 g x) = T'.M1 g (Prod.map p p x)
      simp only [Tor.adjointSuperdiagRep_apply]
      split_ifs <;> simp only [Prod.map, map_mul, map_neg, hu])).1 (hp.prodMap hp) β'
    ((z1fMap (MonoidHom.id (GQ l)) T'.M1 (resCoef E T'.M1)).2 LinearMap.id (fun _ _ => rfl) β' hβ')
  refine ⟨β, (z1fMap (MonoidHom.id (GQ l)) (resCoef E T.M1) T.M1).2 LinearMap.id (fun _ _ => rfl) β hβ, fun g => ?_⟩
  rw [← hpβ]
  exact ⟨rfl, rfl⟩
end

