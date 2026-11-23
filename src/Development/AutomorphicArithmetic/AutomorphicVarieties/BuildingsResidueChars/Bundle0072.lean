module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0068
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0067
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0069
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0066
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InducedFlagCondition
section
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2
open scoped Matrix Pointwise

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

private theorem ex_lift (k₀ : IntermediateField ℚ Ω) {g : G ℚ Ω} (hg : g ∈ k₀.fixingSubgroup) :
    ∃ h : G k₀ Ω, resQ k₀ h = g :=
  ⟨{ g.toRingEquiv with commutes' := fun x => hg x }, rfl⟩

private theorem res_mem (F : IntermediateField ℚ Ω) (g : G F Ω) : resQ F g ∈ F.fixingSubgroup :=
  fun x => g.commutes x

private theorem val_comap (A : ValuationSubring Ω) (t : G ℚ Ω) (y : Ω) :
    (A.comap (t : Ω →+* Ω)).valuation y < 1 ↔ A.valuation (t y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, map_eq_zero_iff _ t.injective]
  rfl

private theorem dec_conj {A : ValuationSubring Ω} (t : G ℚ Ω) {s : G ℚ Ω} (hs : s ∈ Dec (F := ℚ) A) :
    t⁻¹ * s * t ∈ Dec (F := ℚ) (A.comap (t : Ω →+* Ω)) := by
  rw [← Subgroup.inv_mem_iff, mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
  show t (t⁻¹ (s (t x))) ∈ A ↔ t x ∈ A
  rw [mul_inv_apply, apply_mem_iff_of_mem_Dec hs]

private theorem ine_conj {A : ValuationSubring Ω} (t : G ℚ Ω) {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) :
    t⁻¹ * s * t ∈ Ine (F := ℚ) (A.comap (t : Ω →+* Ω)) := by
  refine ⟨dec_conj t hs.1, fun x hx => ?_⟩
  rw [val_comap, map_sub]
  show A.valuation (t (t⁻¹ (s (t x))) - t x) < 1
  rw [mul_inv_apply]
  refine hs.2 _ ?_
  rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
  exact hx

private theorem norm_of_cong {a b : (Qbar l)ˣ} (h : Cong a b) (hb : ‖(b : Qbar l)‖ = 1) : ‖(a : Qbar l)‖ = 1 := by
  have h' : ‖(a : Qbar l) - b‖ < ‖(b : Qbar l)‖ := hb ▸ h
  have e := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h'.ne
  rw [sub_add_cancel, max_eq_right h'.le] at e
  rw [e, hb]

private theorem pull (k₀ : IntermediateField ℚ Ω) [NumberField k₀] {S : Type} (r : G k₀ Ω →* GL (Fin 2) (Qbar l))
    {m : Fin 2 → ℤ} {ψ : Fin 2 → G k₀ Ω →* (Qbar l)ˣ} {B : ValuationSubring Ω} (hO : OrdAt r m ψ B) (h : S → G k₀ Ω)
    (hD : ∀ s, resQ k₀ (h s) ∈ Dec (F := ℚ) B) :
    ∃ κ : Fin 2 → S → (Qbar l)ˣ, S2.Flag (fun s => r (h s)) κ ∧
      (∀ i s, resQ k₀ (h s) ∈ Ine (F := ℚ) B → κ i s = cycBar ℚ Ω l (resQ k₀ (h s)) ^ m i) ∧ ∀ i s, Cong (κ i s) (ψ i (h s)) := by
  obtain ⟨κ, ⟨g, hg⟩, h2, h3⟩ := hO
  refine ⟨fun i s => κ i ⟨h s, hD s⟩, ⟨g, fun s => ⟨(hg ⟨h s, hD s⟩).1 1 0 (by decide), (hg ⟨h s, hD s⟩).2⟩⟩,
    fun i s hs => h2 i ⟨h s, hD s⟩ ⟨hD s, hs.2⟩, fun i s => h3 i ⟨h s, hD s⟩⟩

end

theorem UpperTheory.induced_flag_condition :
    UpperTheory.V.Sd.S2.IndFlag := by
  intro Ω _ _ _ l _ c D T k₀ _ _ φ ι k t r α β R δ H
  refine ⟨![(k : ℤ) + t, k, 0, -(t : ℤ)], ?_, fun A hA => ?_⟩
  · have := H.dat.hk
    have := H.dat.ht
    intro i
    fin_cases i <;> simp <;> omega
  have hA' : (A.comap (resQ T.F T.g0 : Ω →+* Ω)).valuation (l : Ω) < 1 := by
    rw [val_comap, map_natCast]
    exact hA
  have hD : ∀ s : Dec (F := T.F) A, resQ T.F s ∈ Dec (F := ℚ) A := fun s => s.2
  choose h hh using fun s : Dec (F := T.F) A => ex_lift k₀ (H.hyp.spl A hA (hD s))
  choose h' hh' using fun s : Dec (F := T.F) A => ex_lift k₀ (H.hyp.spl _ hA' (dec_conj (resQ T.F T.g0) (hD s)))
  have hcomm : ∀ (χ : G ℚ Ω →* (Qbar l)ˣ) s, χ (resQ k₀ (h' s)) = χ (resQ T.F s) := fun χ s => by
    rw [hh', map_mul, map_mul, map_inv, inv_mul_cancel_comm]
  have hne : ∃ s : Dec (F := T.F) A, ¬ Cong (up D.ξ (resQ T.F s)) 1 := by
    obtain ⟨g, hg, hg4⟩ := H.hyp.two.bigL A hA
    refine ⟨⟨g, hg⟩, fun hc => hg4 ?_⟩
    have := (H.chars.al g 1).2 (by rwa [pow_one])
    rw [pow_one] at this
    rw [this, one_pow]
  have hR : ∀ s, Rib (r (h s)) (up D.ξ (resQ T.F s)) := fun s => by
    have := H.rib (h s) (hh s ▸ res_mem T.F s)
    rwa [hh] at this
  have hR' : ∀ s, Rib (r (h' s)) (up D.ξ (resQ T.F s)) := fun s => by
    have := H.rib (h' s) (by
      rw [hh', ← map_inv, ← map_mul, ← map_mul]
      exact res_mem T.F _)
    rwa [hcomm] at this
  have hmix : ∀ s : Dec (F := T.F) A, (R (resQ T.F s) : M4 (Qbar l)) = mix (β / α) (r (h s)) (r (h' s)) := fun s => by
    rw [← hh s]
    exact H.mix.on _ _ (by rw [hh, hh'])
  have hγ : ‖((β / α : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
    rw [Units.val_div_eq_div_val, norm_div, norm_of_cong H.α_cong (H.chars.unit _ _),
      norm_of_cong H.β_cong (H.chars.unit _ _), div_one]
  have hI : ∀ s : Dec (F := T.F) A, (s : G T.F Ω) ∈ Ine (F := T.F) A → resQ T.F s ∈ Ine (F := ℚ) A :=
    fun s hs => ⟨hD s, hs.2⟩
  have hdet : ∀ {M : GL (Fin 2) (Qbar l)} {a b : (Qbar l)ˣ}, Matrix.GeneralLinearGroup.det M = a * b →
      (M : Matrix (Fin 2) (Fin 2) (Qbar l)).det = a * b := fun e => congrArg Units.val e
  rcases H.dat.above A _ hA _ H.chars.out (fun y => (Iff.rfl : _ ↔ y ∈ A.comap (resQ T.F T.g0 : Ω →+* Ω))) with ⟨o, o'⟩ | ⟨o, o'⟩
  all_goals
    obtain ⟨κ, f, i1, c1⟩ := pull k₀ r o h fun s => hh s ▸ hD s
    obtain ⟨κ', f', i2, c2⟩ := pull k₀ r o' h' fun s => hh' s ▸ dec_conj _ (hD s)
    obtain ⟨d1, u1, w1⟩ := UpperTheory.mix_stable_line_local l _ _ _ κ hne hR f
    obtain ⟨d2, u2, w2⟩ := UpperTheory.mix_stable_line_local l _ _ _ κ' hne hR' f'
    have j1 := fun i s hs => i1 i s (hh s ▸ hI s hs)
    have j2 := fun i s hs => i2 i s (hh' s ▸ ine_conj _ (hI s hs))
    simp only [hh, hcomm] at j1 j2
    have c10 := c1 0
    have c11 := c1 1
    have c20 := c2 0
    have c21 := c2 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.comp_apply, MonoidHom.one_apply, hh, hcomm] at c10 c11 c20 c21
  · obtain ⟨u, hu, eu⟩ := u1 c10
    obtain ⟨w, hw, ew⟩ := w2 c20
    obtain ⟨n, hn, hf⟩ := (UpperTheory.mix_flag_exists l H.hyp.good.l_odd _ u w hγ hu hw).1
    refine ⟨n, hn, fun s hs => ?_⟩
    obtain ⟨g1, g2⟩ := hf _ _ _ _ _ _ (Units.ne_zero _) (Units.ne_zero _) (eu ⟨s, hs⟩) (ew ⟨s, hs⟩) (hdet (d1 _)) (hdet (d2 _))
    rw [← hmix] at g1 g2
    refine ⟨g1, fun i => ?_⟩
    rw [g2]
    fin_cases i
    · exact ⟨c10 _, fun hs' => congrArg Units.val (j1 0 _ hs')⟩
    · exact ⟨c20 _, fun hs' => congrArg Units.val (j2 0 _ hs')⟩
    · exact ⟨c21 _, fun hs' => congrArg Units.val (j2 1 _ hs')⟩
    · exact ⟨c11 _, fun hs' => congrArg Units.val (j1 1 _ hs')⟩
  · obtain ⟨u, hu, eu⟩ := u2 c20
    obtain ⟨w, hw, ew⟩ := w1 c10
    obtain ⟨n, hn, hf⟩ := (UpperTheory.mix_flag_exists l H.hyp.good.l_odd _ u w hγ hu hw).2
    refine ⟨n, hn, fun s hs => ?_⟩
    obtain ⟨g1, g2⟩ := hf _ _ _ _ _ _ (Units.ne_zero _) (Units.ne_zero _) (ew ⟨s, hs⟩) (eu ⟨s, hs⟩) (hdet (d1 _)) (hdet (d2 _))
    rw [← hmix] at g1 g2
    refine ⟨g1, fun i => ?_⟩
    rw [g2]
    fin_cases i
    · exact ⟨c20 _, fun hs' => congrArg Units.val (j2 0 _ hs')⟩
    · exact ⟨c10 _, fun hs' => congrArg Units.val (j1 0 _ hs')⟩
    · exact ⟨c11 _, fun hs' => congrArg Units.val (j1 1 _ hs')⟩
    · exact ⟨c21 _, fun hs' => congrArg Units.val (j2 1 _ hs')⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InducedIrreducible
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Sd.S2

private theorem conjHom {Γ₀ Γ : Type} [Group Γ₀] [Group Γ] (j : Γ₀ →* Γ) (hj : Function.Injective j) (hi : j.range.index = 2)
    (t : Γ) : ∃ c : Γ₀ →* Γ₀, ∀ h, j (c h) = t⁻¹ * j h * t := by
  have hn : j.range.Normal := Subgroup.normal_of_index_eq_two hi
  have : ∀ h, ∃ h', j h' = t⁻¹ * j h * t := fun h => hn.conj_mem' _ ⟨h, rfl⟩ t
  choose c hc using this
  refine ⟨MonoidHom.mk' c fun a b => hj ?_, hc⟩
  rw [map_mul, hc, hc, hc, map_mul]; group

private theorem cp_conj {K : Type} [Field K] (g r : GL (Fin 2) K) :
    ((g * r * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly = (r : Matrix (Fin 2) (Fin 2) K).charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj g _

private theorem cp_ord {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
    {r : G F Ω →* GL (Fin 2) (Qbar l)} {a b : ℤ} {ψ : Fin 2 → G F Ω →* (Qbar l)ˣ} {A : ValuationSubring Ω}
    (h : OrdAt r ![a, b] ψ A) {s : G F Ω} (hs : s ∈ Ine (F := F) A) :
    (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly =
      (X - C ((cycBar F Ω l s ^ a : (Qbar l)ˣ) : Qbar l)) * (X - C ((cycBar F Ω l s ^ b : (Qbar l)ˣ) : Qbar l)) := by
  obtain ⟨κ, ⟨g, hg⟩, hκ, -⟩ := h
  let s' : ↥(Dec (F := F) A) := ⟨s, Ine_le_Dec A hs⟩
  have h0 := (hg s').2 0
  have h1 := (hg s').2 1
  rw [hκ 0 s' hs] at h0
  rw [hκ 1 s' hs] at h1
  rw [← cp_conj g, Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => (hg s').1 i j hij), Fin.prod_univ_two]
  exact congrArg₂ (fun x y => (X - C x) * (X - C y)) h0 h1

private theorem cp_ne {K : Type} [Field K] (e : Kˣ) (he : ¬ IsOfFinOrder e) (k t : ℕ) (ht : 2 ≤ t) :
    (X - C ((e ^ ((k : ℤ) + t) : Kˣ) : K)) * (X - C ((e ^ (-(t : ℤ)) : Kˣ) : K)) ≠
      (X - C ((e ^ (k : ℤ) : Kˣ) : K)) * (X - C ((e ^ (0 : ℤ) : Kˣ) : K)) := by
  intro h
  have h1 := congrArg (Polynomial.eval 1) h
  simp only [eval_mul, eval_sub, eval_X, eval_C, zpow_zero, Units.val_one, sub_self, mul_zero, mul_eq_zero] at h1
  have hinj := injective_zpow_iff_not_isOfFinOrder.2 he
  rcases h1 with h1 | h1
  · have : e ^ ((k : ℤ) + t) = e ^ (0 : ℤ) := Units.ext (by rw [zpow_zero, Units.val_one]; exact (sub_eq_zero.1 h1).symm)
    have := hinj this
    omega
  · have : e ^ (-(t : ℤ)) = e ^ (0 : ℤ) := Units.ext (by rw [zpow_zero, Units.val_one]; exact (sub_eq_zero.1 h1).symm)
    have := hinj this
    omega

private theorem range_res {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (E : IntermediateField ℚ Ω) :
    (resQ E).range = E.fixingSubgroup := by
  refine (range_galEmb ℚ E Ω).trans ?_
  ext g
  rw [mem_galOf, IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x x.2⟩

private theorem ine_move {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (g x : G ℚ Ω)
    (hx : x ∈ Ine (F := ℚ) A) : g⁻¹ * x * g ∈ Ine (F := ℚ) (A.comap g.toRingEquiv.toRingHom) := by
  have h : UpperTheory.V.IsLift (RingEquiv.refl ℚ) g.toRingEquiv := fun x => g.commutes x
  exact UpperTheory.V.conjGal_mem_Ine h (fun _ => Iff.rfl) hx

theorem UpperTheory.induced_irreducible :
    UpperTheory.V.Sd.S2.IndIrr := by
  intro Ω _ _ _ l _ c D T k₀ _ _ φ ι k t r α β R δ hd
  haveI : IsGalois ℚ Ω := {}
  haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) k₀⟩
  set τ : G ℚ Ω := resQ T.F T.g0 with hτ
  let V : Subgroup (G ℚ Ω) := T.F.fixingSubgroup ⊓ T.K.fixingSubgroup
  let U : Subgroup (G ℚ Ω) := V ⊓ (cycZ ℚ Ω l).ker
  have hV : IsOpen (V : Set (G ℚ Ω)) := T.F.fixingSubgroup_isOpen.inter T.K.fixingSubgroup_isOpen
  have hU : ∀ g ∈ T.G', resQ T.F g ∈ U := fun g hg => ⟨⟨range_res T.F ▸ ⟨g, rfl⟩, hg.1⟩, hg.2⟩
  have hU' : ∀ g ∈ U, ∃ g' ∈ T.G', resQ T.F g' = g := by
    intro g hg
    obtain ⟨g', rfl⟩ : g ∈ (resQ T.F).range := range_res T.F ▸ hg.1.1
    exact ⟨g', ⟨hg.1.2, hg.2⟩, rfl⟩
  have hcont : Continuous (resQ k₀) := (resFacts ℚ k₀ Ω l 1 1).1
  have hirr : IsIrr (r.comp (U.comap (resQ k₀)).subtype) := by
    refine irrAb l _ 2 r hd.dat.cont hd.dat.irr (V.comap (resQ k₀)) _ (hV.preimage hcont) (Subgroup.comap_mono inf_le_left) ?_
    intro a ha b hb
    refine ⟨(V.comap (resQ k₀)).mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb), ?_⟩
    show cycZ ℚ Ω l (resQ k₀ (a * b * a⁻¹ * b⁻¹)) = 1
    simp only [map_mul, map_inv]
    rw [mul_inv_cancel_comm, mul_inv_cancel]
  have key : IsIrr (R.comp U.subtype) := by
    refine UpperTheory.mix_invariant_plane_decomposition _ _ _ (resQ k₀) τ α β r R hd.mix U ?_ hirr ?_
    · obtain ⟨g, hg, hne⟩ := UpperTheory.residual_characters_psi_ne Ω l c D T hd.hyp.good hd.hyp.ok hd.hyp.two
      intro hle
      exact hne ((hd.hyp.ps g).2 (range_res k₀ ▸ hle (hU g hg)))
    · rintro ⟨M, hM⟩
      obtain ⟨cj, hcj⟩ := conjHom (resQ k₀) hd.mix.inj hd.mix.index τ
      have hchar : ∀ (χ : G ℚ Ω →* (Qbar l)ˣ) (h : G k₀ Ω), χ (resQ k₀ (cj h)) = χ (resQ k₀ h) := by
        intro χ h
        rw [hcj, map_mul, map_mul, map_inv, inv_mul_cancel_comm]
      have hcyc : ∀ h, cycBar k₀ Ω l (cj h) = cycBar k₀ Ω l h := hchar (cycBar ℚ Ω l)
      let H : Subgroup (G ℚ Ω) := V ⊓ k₀.fixingSubgroup
      have hH : IsOpen (H : Set (G ℚ Ω)) := hV.inter k₀.fixingSubgroup_isOpen
      haveI : Finite (G ℚ Ω ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
      haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      obtain ⟨n, hn, -, hnH⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (H := H) Subgroup.FiniteIndex.index_ne_zero
        (D.s0 : G ℚ Ω)
      obtain ⟨s, hs⟩ : (D.s0 : G ℚ Ω) ^ n ∈ (resQ k₀).range := range_res k₀ ▸ hnH.2
      have hsV : resQ k₀ s ∈ V := hs ▸ hnH.1
      have hsI : resQ k₀ (s * s) ∈ Ine (F := ℚ) (D.pl l) := by
        rw [map_mul, hs]
        exact mul_mem (pow_mem hd.hyp.good.decompSigma_mem.1.1 n) (pow_mem hd.hyp.good.decompSigma_mem.1.1 n)
      have hdet : ∀ h, Matrix.GeneralLinearGroup.det (r h) = cycBar k₀ Ω l h ^ k * up D.ξ (resQ k₀ h) :=
        fun h => DFunLike.congr_fun hd.dat.det h
      have hsq := UpperTheory.mix_sign_twist _ _ r (r.comp cj) (U.comap (resQ k₀)) M hirr (fun h hh => hM h (cj h) hh (hcj h)) s
        (fun h hh => ⟨(V.comap (resQ k₀)).mul_mem ((V.comap (resQ k₀)).mul_mem hsV hh.1) ((V.comap (resQ k₀)).inv_mem hsV), by
          have h1 : cycZ ℚ Ω l (resQ k₀ h) = 1 := hh.2
          show cycZ ℚ Ω l (resQ k₀ (s * h * s⁻¹)) = 1
          simp only [map_mul, map_inv, h1, mul_one, mul_inv_cancel]⟩)
        (by rw [MonoidHom.comp_apply, hdet, hdet, hcyc, hchar])
      have hcp : (r (cj (s * s)) : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly =
          (r (s * s) : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly := by
        rw [← cp_conj M (r (s * s)), ← hsq]; rfl
      have hI : s * s ∈ Ine (F := k₀) (D.pl l) := mem_Ine.2 (mem_Ine.1 hsI)
      have hI' : cj (s * s) ∈ Ine (F := k₀) ((D.pl l).comap τ.toRingEquiv.toRingHom) := by
        have := ine_move (D.pl l) τ _ hsI
        rw [← hcj] at this
        exact mem_Ine.2 (mem_Ine.1 this)
      have he : ¬ IsOfFinOrder (cycBar k₀ Ω l (s * s)) := by
        have hinj : Function.Injective
            (Units.map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom) :=
          Units.map_injective ((algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective)
        intro hf
        have h1 : IsOfFinOrder (cycZ ℚ Ω l (resQ k₀ (s * s))) := (hinj.isOfFinOrder_iff).1 hf
        rw [map_mul, hs, ← pow_add, map_pow] at h1
        exact hd.hyp.good.decompSigma_ord (h1.of_pow (by omega))
      rcases hd.dat.above (D.pl l) ((D.pl l).comap τ.toRingEquiv.toRingHom) (hd.hyp.good.pl_over l Fact.out) τ
        hd.chars.out (fun _ => Iff.rfl) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [cp_ord h1 hI, cp_ord h2 hI', hcyc] at hcp
        exact cp_ne _ he k t hd.dat.ht hcp.symm
      · rw [cp_ord h1 hI, cp_ord h2 hI', hcyc] at hcp
        exact cp_ne _ he k t hd.dat.ht hcp
  refine ⟨key.1, fun _ _ _ => trivial, fun W hW hi => key.2.2 W hW ?_⟩
  rintro ⟨g, hg⟩ v hv
  obtain ⟨g', hg', rfl⟩ := hU' g hg
  exact hi ⟨g', hg'⟩ v hv
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricCubeIrreducible
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem isIrr_iso {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (h : RepIso r r')
    (hr : IsIrr r) : IsIrr r' := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨h1, -, h3⟩ := hr
  refine ⟨h1, fun _ _ _ => Submodule.mem_top, fun W _ hi => ?_⟩
  have key := h3 (W.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k))) le_top (fun s v hv => by
    have h4 := hi s _ hv
    rw [hg s] at h4
    simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc] using h4)
  have hs : Function.Surjective (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)) := fun v =>
    ⟨((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v, by
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
  have e := Submodule.map_comap_eq_of_surjective hs W
  rcases key with key | key
  · left
    rw [← e, key, Submodule.map_bot]
  · right
    rw [← e, key, Submodule.map_top, LinearMap.range_eq_top.mpr hs]
end

