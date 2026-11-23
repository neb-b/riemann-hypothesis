module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1108

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.Count1Pf
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

theorem PositivityTheory.Rg.BcB.G3.count1_pf (h1 : Param) : Count1 := by
  intro E _ _ _ hU n S hS P hP y hy hint
  obtain ⟨ι, _, K, L, _, _, _, _, _, _, x, hcard, hR, hC, hA, hsum, ⟨e⟩⟩ :=
    h1 E hU n S hS P hP y hy hint
  rw [Nat.card_congr e, Nat.card_pi, ← hcard, ← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.card_univ,
    ← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => GlobalTheory.QuadSymbol.SignCount.card_classes_mul_two (K i) (L i) (hR i) (hC i) (x i) (hA i)

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PAbsSum
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.AbsSumP
end PositivityTheory.Rg.BcB.G3.AbsSumP

theorem PositivityTheory.Rg.BcB.G3.absSum_pf : PositivityTheory.Rg.BcB.G3.AbsSum := by
  intro V C S L A o f D loc m N hA ho hf hD hN hcard
  set T : Set V := {v | ¬ ∀ l ∈ A v, f v l = if l = o v then 1 else 0} with hTdef
  have hT : T.Finite := Filter.eventually_cofinite.mp hf
  let _ : ∀ v, Fintype (A v) := fun v => (hA v).fintype
  obtain ⟨U, hUS, hgood⟩ : ∃ U : Finset V, (∀ v ∈ U, v ∈ S) ∧
      ∀ v, v ∈ S → v ∉ U → ∀ l ∈ A v, f v l = if l = o v then 1 else 0 := by
    refine ⟨hT.toFinset.filter (fun v => v ∈ S), fun v hv => (Finset.mem_filter.mp hv).2, ?_⟩
    intro v hvS hvU
    by_contra h
    exact hvU (Finset.mem_filter.mpr ⟨hT.mem_toFinset.mpr h, hvS⟩)
  have hkey : ∀ c ∈ D, (∏ᶠ v ∈ S, f v (loc c v)) =
      if (∀ v ∈ S, v ∉ U → loc c v = o v) then ∏ v ∈ U, f v (loc c v) else 0 := by
    intro c hc
    obtain ⟨hcA, hcf⟩ := hD c hc
    have hW : {v | ¬ loc c v = o v}.Finite := Filter.eventually_cofinite.mp hcf
    obtain ⟨F, hUF, hFS, hWF⟩ : ∃ F : Finset V, U ⊆ F ∧ (↑F : Set V) ⊆ S ∧
        ∀ v ∈ S, ¬ loc c v = o v → v ∈ F := by
      refine ⟨U ∪ hW.toFinset.filter (fun v => v ∈ S), Finset.subset_union_left, ?_, ?_⟩
      · intro v hv
        rcases Finset.mem_union.mp (Finset.mem_coe.mp hv) with hv | hv
        · exact hUS v hv
        · exact (Finset.mem_filter.mp hv).2
      · intro v hvS hne
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hW.mem_toFinset.mpr hne, hvS⟩)
    have hsupp : S ∩ Function.mulSupport (fun v => f v (loc c v)) ⊆ ↑F := by
      rintro v ⟨hvS, hv1⟩
      rw [Function.mem_mulSupport] at hv1
      rw [Finset.mem_coe]
      by_cases hvU : v ∈ U
      · exact hUF hvU
      · apply hWF v hvS
        intro heq
        apply hv1
        rw [hgood v hvS hvU _ (hcA v), if_pos heq]
    rw [finprod_mem_eq_prod_of_subset _ hsupp hFS]
    rw [← Finset.prod_sdiff hUF]
    have hrest : ∀ v ∈ F \ U, f v (loc c v) = if loc c v = o v then 1 else 0 := by
      intro v hv
      rw [Finset.mem_sdiff] at hv
      exact hgood v (hFS hv.1) hv.2 _ (hcA v)
    rw [Finset.prod_congr rfl hrest, Finset.prod_boole]
    have hiff : (∀ v ∈ F \ U, loc c v = o v) ↔ (∀ v ∈ S, v ∉ U → loc c v = o v) := by
      constructor
      · intro h v hvS hvU
        by_contra hne
        exact hne (h v (Finset.mem_sdiff.mpr ⟨hWF v hvS hne, hvU⟩))
      · intro h v hv
        rw [Finset.mem_sdiff] at hv
        exact h v (hFS hv.1) hv.2
    by_cases hc' : ∀ v ∈ S, v ∉ U → loc c v = o v
    · rw [if_pos (hiff.mpr hc'), if_pos hc', one_mul]
    · rw [if_neg (fun h => hc' (hiff.mp h)), if_neg hc', zero_mul]
  let zmap : C → ((v : U) → A v.1) := fun c v =>
    if h : loc c v.1 ∈ A v.1 then ⟨loc c v.1, h⟩ else ⟨o v.1, ho v.1⟩
  let yz : ((v : U) → A v.1) → (∀ v, L v) := fun z v => if h : v ∈ U then (z ⟨v, h⟩).1 else o v
  have hyz_ok : ∀ z, (∀ v, yz z v ∈ A v) ∧ (∀ᶠ v in cofinite, yz z v = o v) := by
    intro z
    refine ⟨fun v => ?_, ?_⟩
    · dsimp only [yz]
      split_ifs with h
      · exact (z ⟨v, h⟩).2
      · exact ho v
    · rw [Filter.eventually_cofinite]
      apply (U.finite_toSet).subset
      intro v hv
      by_contra hvU
      exact hv (by dsimp only [yz]; rw [dite_eq_right (fun h => hvU (Finset.mem_coe.mpr h))])
  have hfibfin : ∀ z, {c | c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v}.Finite := by
    intro z
    have h := hcard (yz z) (hyz_ok z).1 (hyz_ok z).2
    have hne : Nat.card {c : C // c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v} ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h; exact hN h.symm
    exact Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero hne)
  set G : Set C := {c | c ∈ D ∧ ∀ v ∈ S, v ∉ U → loc c v = o v} with hGdef
  have hGsub : G ⊆ ⋃ z, {c | c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v} := by
    rintro c ⟨hcD, hc⟩
    refine Set.mem_iUnion.mpr ⟨zmap c, hcD, fun v hvS => ?_⟩
    dsimp only [yz, zmap]
    by_cases hvU : v ∈ U
    · rw [dite_eq_left hvU, dite_eq_left ((hD c hcD).1 v)]
    · rw [dite_eq_right hvU]; exact hc v hvS hvU
  have hGfin : G.Finite := (Set.finite_iUnion hfibfin).subset hGsub
  have hsuppG : ∀ c, c ∈ D → (∏ᶠ v ∈ S, f v (loc c v)) ≠ 0 → c ∈ G := by
    intro c hcD hne
    rw [hkey c hcD] at hne
    by_contra hcG
    apply hne
    rw [if_neg]
    intro h; exact hcG ⟨hcD, h⟩
  refine ⟨hGfin.subset (fun c hc => hsuppG c hc.1 hc.2), ?_⟩
  have hsum1 : (∑ᶠ c : C, if c ∈ D then ∏ᶠ v ∈ S, f v (loc c v) else 0) =
      ∑ c ∈ hGfin.toFinset, ∏ v : U, f v.1 (zmap c v).1 := by
    rw [finsum_eq_sum_of_support_subset _ (s := hGfin.toFinset) ?_]
    · apply Finset.sum_congr rfl
      intro c hc
      rw [Set.Finite.mem_toFinset] at hc
      obtain ⟨hcD, hcG⟩ := hc
      rw [if_pos hcD, hkey c hcD, if_pos hcG, ← Finset.prod_coe_sort U (fun v => f v (loc c v))]
      apply Finset.prod_congr rfl
      intro v _
      dsimp only [zmap]
      rw [dite_eq_left ((hD c hcD).1 v.1)]
    · intro c hc
      rw [Function.mem_support] at hc
      rw [Set.Finite.coe_toFinset]
      by_cases hcD : c ∈ D
      · rw [if_pos hcD] at hc; exact hsuppG c hcD hc
      · rw [if_neg hcD] at hc; exact absurd rfl hc
  have hmem : ∀ z c, (c ∈ hGfin.toFinset ∧ zmap c = z) ↔ (c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v) := by
    intro z c
    rw [Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨hcD, hcG⟩, hzc⟩
      refine ⟨hcD, fun v hvS => ?_⟩
      dsimp only [yz]
      by_cases hvU : v ∈ U
      · rw [dite_eq_left hvU, ← hzc]
        dsimp only [zmap]
        rw [dite_eq_left ((hD c hcD).1 v)]
      · rw [dite_eq_right hvU]; exact hcG v hvS hvU
    · rintro ⟨hcD, hc⟩
      refine ⟨⟨hcD, fun v hvS hvU => ?_⟩, ?_⟩
      · rw [hc v hvS]; dsimp only [yz]; rw [dite_eq_right hvU]
      · funext v
        apply Subtype.ext
        dsimp only [zmap]
        rw [dite_eq_left ((hD c hcD).1 v.1)]
        show loc c v.1 = (z v).1
        rw [hc v.1 (hUS v.1 v.2)]
        dsimp only [yz]
        rw [dite_eq_left v.2]
  have hcardfib : ∀ z (s' : Finset C), (∀ c, c ∈ s' ↔ (c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v)) →
      s'.card = Nat.card {c : C // c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v} := by
    intro z s' hs'
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight hs')
  rw [hsum1, ← Finset.sum_fiberwise hGfin.toFinset zmap (fun c => ∏ v : U, f v.1 (zmap c v).1),
    Finset.sum_mul]
  rw [Finset.sum_congr rfl (g := fun z => (N : ℂ) * ∏ v : U, f v.1 (z v).1) ?_, ← Finset.mul_sum]
  swap
  · intro z _
    rw [Finset.sum_congr rfl (g := fun _ => ∏ v : U, f v.1 (z v).1) ?_, Finset.sum_const, nsmul_eq_mul,
      mul_right_comm]
    swap
    · intro c hc
      rw [(Finset.mem_filter.mp hc).2]
    congr 1
    rw [← hcard (yz z) (hyz_ok z).1 (hyz_ok z).2, Nat.cast_mul,
      hcardfib z _ (fun c => Finset.mem_filter.trans (hmem z c))]
  congr 1
  have hR : ∀ v, (∑ᶠ l : L v, if l ∈ A v then f v l else 0) = ∑ l : A v, f v l.1 := by
    intro v
    rw [finsum_eq_sum_of_support_subset _ (s := (A v).toFinset) ?_,
      Finset.sum_set_coe (f := fun l => f v l)]
    · exact Finset.sum_congr rfl (fun l hl => if_pos (Set.mem_toFinset.mp hl))
    · intro l hl
      rw [Function.mem_support] at hl
      rw [Set.coe_toFinset]
      by_contra h
      exact hl (if_neg h)
  have hR1 : ∀ v, v ∈ S → v ∉ U → (∑ᶠ l : L v, if l ∈ A v then f v l else 0) = 1 := by
    intro v hvS hvU
    rw [hR, Finset.sum_set_coe (f := fun l => f v l),
      Finset.sum_congr rfl (fun l hl => hgood v hvS hvU l (Set.mem_toFinset.mp hl)), Finset.sum_ite_eq',
      if_pos (Set.mem_toFinset.mpr (ho v))]
  rw [← Fintype.prod_sum (fun (v : U) (l : A v.1) => f v.1 l.1)]
  rw [finprod_mem_eq_prod_of_subset _ (t := U) ?_ ?_]
  · rw [← Finset.prod_coe_sort U]
    exact Finset.prod_congr rfl (fun v _ => (hR v.1).symm)
  · rintro v ⟨hvS, hv1⟩
    by_contra hvU
    rw [Function.mem_mulSupport] at hv1
    exact hv1 (hR1 v hvS hvU)
  · intro v hv
    exact hUS v hv
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PBaseFrame
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.BaseFrameP

theorem phi_map {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (n : ℕ) :
    (GlobalTheory.Tw.Phi n R).map p = GlobalTheory.Tw.Phi n S := by
  ext i k
  simp only [Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

end PositivityTheory.Rg.BcB.G3.BaseFrameP

open PositivityTheory.Rg.BcB.G3.BaseFrameP in
theorem PositivityTheory.Rg.BcB.G3.baseFrame_pf : BaseFrame := by
  intro F E F' E' _ _ _ _ _ _ _ p j c c' s d hj hc hcj hs0 hcs hspE hspE' n δ hsep B _ _ ρ hfr
  have hps0 : p s ≠ 0 := (map_ne_zero p).2 hs0
  have hcps : c' (p s) = - p s := by rw [hc, hcs, map_neg]
  have indep' : ∀ u v : F', j u + p s * j v = 0 → u = 0 ∧ v = 0 := by
    intro u v h
    have h2 := congrArg c' h
    simp only [map_add (f := _), map_mul, hcj, hcps, map_zero] at h2
    have hu : j u = 0 := by
      have h3 : (2 : E') * j u = 0 := by linear_combination h + h2
      exact (mul_eq_zero.1 h3).resolve_left two_ne_zero
    have hv : j v = 0 := by
      rw [hu, zero_add] at h
      exact (mul_eq_zero.1 h).resolve_left hps0
    exact ⟨(map_eq_zero j).1 hu, (map_eq_zero j).1 hv⟩
  have indepE : ∀ a b : F, algebraMap F E a + s * algebraMap F E b = 0 → a = 0 ∧ b = 0 := by
    intro a b h
    have h1 := congrArg p h
    simp only [map_add (f := _), map_mul, ← hj, map_zero] at h1
    obtain ⟨h2, h3⟩ := indep' _ _ h1
    exact ⟨(map_eq_zero (algebraMap F F')).1 h2, (map_eq_zero (algebraMap F F')).1 h3⟩
  have hli : LinearIndependent F ![(1 : E), s] := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    apply indepE a b
    simp only [Algebra.smul_def] at h
    linear_combination h
  have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : E), s]) := by
    intro z _
    obtain ⟨a, b, rfl⟩ := hspE z
    have h1 : (1 : E) ∈ Submodule.span F (Set.range ![(1 : E), s]) := Submodule.subset_span ⟨0, rfl⟩
    have h2 : s ∈ Submodule.span F (Set.range ![(1 : E), s]) := Submodule.subset_span ⟨1, rfl⟩
    have h3 := Submodule.add_mem _ (Submodule.smul_mem _ a h1) (Submodule.smul_mem _ b h2)
    convert h3 using 1
    rw [Algebra.smul_def, Algebra.smul_def]
    ring
  obtain ⟨bE, hb0, hb1⟩ : ∃ bE : Module.Basis (Fin 2) F E, bE 0 = 1 ∧ bE 1 = s :=
    ⟨Module.Basis.mk hli hsp, by simp, by simp⟩
  have hdec : ∀ e : E, e = algebraMap F E (bE.repr e 0) + s * algebraMap F E (bE.repr e 1) := by
    intro e
    conv_lhs => rw [← bE.sum_repr e]
    rw [Fin.sum_univ_two, hb0, hb1, Algebra.smul_def, Algebra.smul_def]
    ring
  have hsq : ρ (algebraMap F B d) = s ^ 2 • (1 : Matrix (Fin n) (Fin n) E) := hfr.sq
  have hadj : ∀ a, ρ a * (δ.val * GlobalTheory.Tw.Phi n E) = δ.val * GlobalTheory.Tw.Phi n E * ((ρ a).map c)ᵀ := hfr.adj
  have hcm : ∀ a, ρ a * (δ * thetaGL n c δ).val = (δ * thetaGL n c δ).val * ρ a := hfr.comm

  obtain ⟨ρ', hρt⟩ : ∃ ρ' : F' ⊗[F] B →+* Matrix (Fin n) (Fin n) E',
      ∀ x b, ρ' (x ⊗ₜ b) = j x • (ρ b).map p := by
    let _ : Algebra F E' := (p.comp (algebraMap F E)).toAlgebra
    let pA : E →ₐ[F] E' := { p with commutes' := fun _ => rfl }
    let fA : F' →ₐ[F] Matrix (Fin n) (Fin n) E' :=
      { (Matrix.scalar (Fin n) : E' →+* Matrix (Fin n) (Fin n) E').comp j with
        commutes' := fun x => by
          show Matrix.scalar (Fin n) (j (algebraMap F F' x)) = _
          rw [hj, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
          rfl }
    let gA : B →ₐ[F] Matrix (Fin n) (Fin n) E' := pA.mapMatrix.comp ρ
    have hcomm : ∀ x y, Commute (fA x) (gA y) := fun x y => by
      show Commute (Matrix.scalar (Fin n) (j x)) _
      exact Matrix.scalar_commute _ (fun _ => Commute.all _ _) _
    refine ⟨(Algebra.TensorProduct.lift fA gA hcomm).toRingHom, fun x b => ?_⟩
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul]
    show Matrix.scalar (Fin n) (j x) * (ρ b).map p = _
    rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  have hρ1 : ∀ a, ρ' (1 ⊗ₜ a) = (ρ a).map p := by
    intro a; rw [hρt, map_one, one_smul]
  have hρu : ∀ u : F', ρ' (u ⊗ₜ (1 : B)) = j u • (1 : Matrix (Fin n) (Fin n) E') := by
    intro u; rw [hρt, map_one ρ, Matrix.map_one _ (map_zero p) (map_one p)]
  have hD : ρ' ((1 : F') ⊗ₜ algebraMap F B d) = (p s) ^ 2 • (1 : Matrix (Fin n) (Fin n) E') := by
    rw [hρ1, hsq]
    ext i k
    by_cases h : i = k <;> simp [h, Matrix.one_apply]
  have hN' : (GeneralLinearGroup.map p δ * thetaGL n c' (GeneralLinearGroup.map p δ)).val =
      (δ * thetaGL n c δ).val.map p := by
    rw [← GlobalTheory.ThetaPull.map_thetaGL p c c' (fun x => (hc x).symm) δ, ← map_mul]
    rfl
  refine ⟨ρ', hρ1, ⟨?_, hD, ?_, ?_, ?_⟩⟩
  ·
    obtain ⟨φ, hφdef⟩ : ∃ φ : B →ₗ[F] (Fin n × Fin n × Fin 2 → F),
        ∀ b i, φ b i = bE.repr (ρ b i.1 i.2.1) i.2.2 :=
      ⟨{ toFun := fun b i => bE.repr (ρ b i.1 i.2.1) i.2.2
         map_add' := fun a b => by funext i; simp [map_add (f := _)]
         map_smul' := fun r b => by funext i; simp [map_smul] }, fun _ _ => rfl⟩
    have hφ : Function.Injective φ := by
      refine (injective_iff_map_eq_zero φ).2 fun b hb => ?_
      have h1 : ρ b = 0 := by
        ext i k
        have h2 : bE.repr (ρ b i k) = 0 := by
          ext t
          have := congrFun hb (i, k, t)
          rw [hφdef] at this
          simpa using this
        simpa using h2
      exact (injective_iff_map_eq_zero ρ.toRingHom).1 hfr.inj b h1
    have hL : Function.Injective (φ.lTensor F') := Module.Flat.lTensor_preserves_injective_linearMap φ hφ
    have hkey : ∀ X : F' ⊗[F] B, ∀ i k, ρ' X i k =
        j (TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2) (φ.lTensor F' X) (i, k, 0)) +
        p s * j (TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2) (φ.lTensor F' X) (i, k, 1)) := by
      intro X i k
      induction X using TensorProduct.induction_on with
      | zero => simp
      | tmul x b =>
        rw [hρt]
        simp only [LinearMap.lTensor_tmul, TensorProduct.piScalarRight_apply,
          TensorProduct.piScalarRightHom_tmul, hφdef, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
          Algebra.smul_def, map_mul]
        conv_lhs => rw [hdec (ρ b i k)]
        simp only [map_add (f := _), map_mul, ← hj]
        ring
      | add X Y hX hY =>
        simp only [map_add (f := _), Matrix.add_apply, hX, hY, Pi.add_apply]
        ring
    refine (injective_iff_map_eq_zero ρ').2 fun X hX => ?_
    have hW : TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2) (φ.lTensor F' X) = 0 := by
      funext ⟨i, k, t⟩
      have h := hkey X i k
      rw [hX, Matrix.zero_apply] at h
      obtain ⟨h0, h1⟩ := indep' _ _ h.symm
      have ht : t = 0 ∨ t = 1 := by fin_cases t <;> simp
      rcases ht with rfl | rfl
      · exact h0
      · exact h1
    have h0 : φ.lTensor F' X = 0 :=
      (TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2)).injective (hW.trans (map_zero _).symm)
    exact hL (by rw [h0, map_zero])
  ·
    intro X
    rw [show (GeneralLinearGroup.map p δ).val = δ.val.map p from rfl, ← phi_map p n, ← Matrix.map_mul]
    induction X using TensorProduct.induction_on with
    | zero => simp
    | tmul x b =>
      rw [hρt]
      have e1 : ((j x • (ρ b).map p).map c') = j x • (((ρ b).map c).map p) := by
        ext i k; simp [hcj, hc]
      rw [e1, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      rw [← Matrix.map_mul, hadj, ← Matrix.transpose_map, Matrix.map_mul, Matrix.transpose_map, Matrix.transpose_map]
    | add X Y hX hY =>
      rw [map_add (f := _), add_mul, hX, hY, Matrix.map_add _ (map_add c'), Matrix.transpose_add, mul_add]
  ·
    intro X
    rw [hN']
    induction X using TensorProduct.induction_on with
    | zero => simp
    | tmul x b =>
      rw [hρt, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul, ← Matrix.map_mul, hcm]
    | add X Y hX hY =>
      rw [map_add (f := _), add_mul, mul_add, hX, hY]
  ·
    intro x hx
    rw [hN'] at hx
    have hsepN' : ((δ * thetaGL n c δ).val.map p).charpoly.Separable := by
      rw [Matrix.charpoly_map]; exact hsep.map
    obtain ⟨q, rfl⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm _ x hsepN' hx.symm
    have hTadd : ∀ y z : Matrix (Fin n) (Fin n) E', (∃ a b, y = ρ' a + p s • ρ' b) →
        (∃ a b, z = ρ' a + p s • ρ' b) → ∃ a b, y + z = ρ' a + p s • ρ' b := by
      rintro y z ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
      exact ⟨a + a', b + b', by rw [map_add (f := _), map_add (f := _), smul_add]; abel⟩
    have hT0 : ∃ a b, (0 : Matrix (Fin n) (Fin n) E') = ρ' a + p s • ρ' b := ⟨0, 0, by simp⟩
    have hTsmul : ∀ (e : E') (y : Matrix (Fin n) (Fin n) E'), (∃ a b, y = ρ' a + p s • ρ' b) →
        ∃ a b, e • y = ρ' a + p s • ρ' b := by
      rintro e y ⟨a, b, rfl⟩
      obtain ⟨u, v, rfl⟩ := hspE' e
      refine ⟨(u ⊗ₜ (1 : B)) * a + ((1 : F') ⊗ₜ algebraMap F B d) * ((v ⊗ₜ (1 : B)) * b),
        (u ⊗ₜ (1 : B)) * b + (v ⊗ₜ (1 : B)) * a, ?_⟩
      simp only [map_add (f := _), map_mul, hρu, hD, Matrix.smul_mul, one_mul]
      module
    have hTpow : ∀ k : ℕ, ∃ a b, ((δ * thetaGL n c δ).val.map p) ^ k = ρ' a + p s • ρ' b := by
      intro k
      obtain ⟨a, b, hab⟩ := hfr.span ((δ * thetaGL n c δ).val ^ k)
        (Commute.self_pow (δ * thetaGL n c δ).val k).eq.symm
      refine ⟨1 ⊗ₜ a, 1 ⊗ₜ b, ?_⟩
      have hpw : ((δ * thetaGL n c δ).val.map p) ^ k = ((δ * thetaGL n c δ).val ^ k).map p :=
        (map_pow p.mapMatrix _ k).symm
      rw [hpw, hρ1, hρ1, hab]
      ext i k
      simp
    rw [aeval_eq_sum_range]
    exact Finset.sum_induction _ (fun y => ∃ a b, y = ρ' a + p s • ρ' b) hTadd hT0
      (fun i _ => hTsmul _ _ (hTpow i))
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PClsNorm
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.ClsNormP

theorem thetaGL_val' {k : Type} [CommRing k] (n : ℕ) (c : k →+* k) (g : GL (Fin n) k) :
    (thetaGL n c g).val = GlobalTheory.Tw.Phi n k * ((g⁻¹).val.map c)ᵀ * (GlobalTheory.Tw.Phi n k)ᵀ := rfl

theorem phi_mul_transpose_eq_one {k : Type} [CommRing k] (n : ℕ) : GlobalTheory.Tw.Phi n k * (GlobalTheory.Tw.Phi n k)ᵀ = 1 :=
  GlobalTheory.GramTwistNorm.phi_mul_transpose n

theorem units_map_val {k : Type} [Field k] {n : ℕ} {B : Type} [CommRing B]
    (ρ : B →+* Matrix (Fin n) (Fin n) k) (t : Bˣ) : (Units.map ρ.toMonoidHom t).val = ρ t := rfl

theorem units_map_inv_val {k : Type} [Field k] {n : ℕ} {B : Type} [CommRing B]
    (ρ : B →+* Matrix (Fin n) (Fin n) k) (t : Bˣ) : ((Units.map ρ.toMonoidHom t)⁻¹).val = ρ (↑t⁻¹ : B) := by
  rw [← map_inv]; rfl

theorem delta_theta {k : Type} [Field k] {n : ℕ} {c : k →+* k} {δ : GL (Fin n) k} {s : k} {B : Type} [CommRing B]
    {d : B} {ρ : B →+* Matrix (Fin n) (Fin n) k} (hF : IsFrame c δ s d ρ) (t : Bˣ) :
    δ.val * (thetaGL n c (Units.map ρ.toMonoidHom t)).val = ρ (↑t⁻¹ : B) * δ.val := by
  rw [thetaGL_val', units_map_inv_val]
  calc δ.val * (GlobalTheory.Tw.Phi n k * ((ρ (↑t⁻¹ : B)).map c)ᵀ * (GlobalTheory.Tw.Phi n k)ᵀ)
      = (δ.val * GlobalTheory.Tw.Phi n k * ((ρ (↑t⁻¹ : B)).map c)ᵀ) * (GlobalTheory.Tw.Phi n k)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = ρ (↑t⁻¹ : B) * (δ.val * GlobalTheory.Tw.Phi n k) * (GlobalTheory.Tw.Phi n k)ᵀ := by rw [← hF.adj]
    _ = ρ (↑t⁻¹ : B) * δ.val := by rw [Matrix.mul_assoc, Matrix.mul_assoc, phi_mul_transpose_eq_one, Matrix.mul_one]

end PositivityTheory.Rg.BcB.G3.ClsNormP

namespace PositivityTheory.Rg.BcB.G3

theorem clsNorm_pf : ClsNorm := by
  intro k _ _ n c _ δ s _ _ B _ d ρ hF t
  apply Units.ext
  simp only [pt, map_mul, Units.val_mul]
  rw [ClsNormP.units_map_val]
  have h := ClsNormP.delta_theta hF t
  have h1 : ρ (t : B) * ρ (↑t⁻¹ : B) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  calc ρ (t : B) * δ.val * ((thetaGL n c (Units.map ρ.toMonoidHom t)).val * (thetaGL n c δ).val)
      = ρ (t : B) * (δ.val * (thetaGL n c (Units.map ρ.toMonoidHom t)).val) * (thetaGL n c δ).val := by
        simp only [Matrix.mul_assoc]
    _ = δ.val * (thetaGL n c δ).val := by
        rw [h, ← Matrix.mul_assoc, h1, Matrix.one_mul]

end PositivityTheory.Rg.BcB.G3

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.SuppPf
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.SuppP
end PositivityTheory.Rg.BcB.G3.SuppP

theorem PositivityTheory.Rg.BcB.G3.supp_pf : PositivityTheory.Rg.BcB.G3.Supp := by
  intro G _ _ θ K y f h
  by_contra hne
  push Not at hne
  apply h
  unfold twOrb avg
  simp only [hne, finsum_zero, mul_zero]
end
end

