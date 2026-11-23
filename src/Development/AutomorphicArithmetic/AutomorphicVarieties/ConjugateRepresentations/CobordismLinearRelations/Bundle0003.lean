module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AdmEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ZigClosed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ExactSub
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem conj_level {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)
    (h1 : IsOpen (U : Set G)) (h2 : IsCompact (U : Set G)) (x : G) :
    ∃ U' : Subgroup G, IsOpen (U' : Set G) ∧ IsCompact (U' : Set G) ∧ ∀ u ∈ U', x⁻¹ * u * x ∈ U := by
  have e : ((U.comap (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G) =
      ((Homeomorph.mulLeft x⁻¹).trans (Homeomorph.mulRight x)) ⁻¹' (U : Set G) := by
    ext u
    simp
  refine ⟨U.comap (MulAut.conj x⁻¹).toMonoidHom, ?_, ?_, fun u hu => by simpa using hu⟩
  · rw [e]; exact h1.preimage (Homeomorph.continuous _)
  · rw [e]; exact (Homeomorph.isCompact_preimage _).2 h2

theorem UpperTheory.V.Cj.exactSub :
    UpperTheory.V.Cj.ExactSub := by
  intro E _ _ _ a Ξ q
  have comb : ∀ (s : ℂ) (α β : Co Ξ q), Exact Ξ α → Exact Ξ β → Exact Ξ (s • α + β) := by
    rintro s α β ⟨U, u1, u2, hα⟩ ⟨V, v1, v2, hβ⟩
    have hα' := ((levSub E a Ξ q).2.1 U (U ⊓ V) inf_le_left α).2 hα
    have hβ' := ((levSub E a Ξ q).2.1 V (U ⊓ V) inf_le_right β).2 hβ
    refine ⟨U ⊓ V, u1.inter v1, u2.inter_right (V.isClosed_of_isOpen v1), ?_⟩
    cases q with
    | zero =>
      change α = 0 at hα'
      change β = 0 at hβ'
      change s • α + β = 0
      rw [hα', hβ', smul_zero, add_zero]
    | succ q =>
      obtain ⟨η, e1, rfl⟩ := hα'
      obtain ⟨ζ, z1, rfl⟩ := hβ'
      exact ⟨s • η + ζ, (levSub E a Ξ q).1 _ s η ζ e1 z1, dCo_comb s η ζ⟩
  have hz : Exact Ξ (0 : Co Ξ q) := by
    obtain ⟨L, hL, -⟩ := (levSub E a Ξ q).2.2
    obtain ⟨U, u1, u2, -⟩ := (hL 0).1 L.zero_mem
    refine ⟨U, u1, u2, ?_⟩
    cases q with
    | zero => rfl
    | succ q =>
      exact ⟨0, ⟨fun k X => by simp, fun X i _ => rfl, fun X => Submodule.zero_mem _⟩,
        AlternatingMap.ext fun X => by simp [dCo_apply]⟩
  refine ⟨{ carrier := {ω | Exact Ξ ω}
            add_mem' := fun {α β} hα hβ => by simpa only [one_smul, Set.mem_ofPred_eq] using comb 1 α β hα hβ
            zero_mem' := hz
            smul_mem' := fun s α hα => by simpa only [add_zero, Set.mem_ofPred_eq] using comb s α 0 hα hz }, fun _ => Iff.rfl, ?_⟩
  rintro x ω ⟨U, u1, u2, hω⟩
  obtain ⟨U', v1, v2, hx⟩ := conj_level U u1 u2 x
  refine ⟨U', v1, v2, ?_⟩
  cases q with
  | zero =>
    change ω = 0 at hω
    change trans x ω = 0
    rw [hω, ← transRep_apply, map_zero]
  | succ q =>
    obtain ⟨η, e1, rfl⟩ := hω
    obtain ⟨p1, p2, -⟩ := perNat E a U U' x hx Ξ q η e1
    exact ⟨trans x η, p1, p2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.HarmInj
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

theorem UpperTheory.V.Cj.harmInj :
    UpperTheory.V.Cj.HarmInj := by
  intro E _ _ _ a ha π Ξ r n e he hr q ω ⟨⟨U, u1, u2, u3⟩, _, hco, hV⟩ ⟨U', v1, v2, v3⟩
  cases q with
  | zero => exact v3
  | succ q =>
    have ho : IsOpen ((U ⊓ U' : Subgroup _) : Set (GL (Fin a) (Af E))) := u1.inter v1
    have hc : IsCompact ((U ⊓ U' : Subgroup _) : Set (GL (Fin a) (Af E))) :=
      u2.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) fun k hk => hk.1
    have hm := (levSub E a Ξ (q + 1)).2.1
    have hL := (hm U (U ⊓ U') inf_le_left ω).1 u3
    obtain ⟨η, hη, rfl⟩ := (hm U' (U ⊓ U') inf_le_right ω).2 v3
    have hR : Rapid (dCo (smLie Ξ) η) := fun X N => cuspRapid E a π Ξ (q + 1) _ hV [] X N
    obtain ⟨χ, hχ⟩ := twEx E a ha r
    obtain ⟨G, hG⟩ := admEx E a Ξ
    have hd : IsData Ξ r χ G e := ⟨hr, hχ, hG, he⟩
    have hM : Moderate (dCo (smLie Ξ) η) := ⟨0, fun X => by
      obtain ⟨C, hC⟩ := hR X 0
      exact ⟨C, fun g => by simpa using hC g⟩⟩
    set_option synthInstance.maxHeartbeats 400000 in
    have hP := pairFacts E a ha MeasureTheory.Measure.haar _ ho Ξ r χ G n e hd (q + 1)
    set_option synthInstance.maxHeartbeats 400000 in
    exact hP.2.2.1 _ hL (hP.1 _ _ hL hL hR hM)
      (g1 E a ha MeasureTheory.Measure.haar _ ho hc Ξ r χ G n e hd q _ η hL hη hR hco hM)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.HarmSub
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a}

private theorem rT_adj (r : ℝ) (x : GL (Fin a) (Af E)) (X : Lie E a) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :
    (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (smAdj Ξ r X m) = smAdj Ξ r X ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) m) := by
  have h : lie E a X * act (.fin x) = act (.fin x) * lie E a X := lie_rt_fin X x
  have h1 : (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (smA Ξ X m) = smA Ξ X ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) m) := by
    rw [smA_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, ← LinearMap.rTensor_mul, ← LinearMap.rTensor_mul, h]
  have h2 : (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (smB Ξ X m) = smB Ξ X ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) m) := by
    rw [smB_apply]
    clear h1
    induction m using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
    | tmul φ v => simp
  rw [smAdj, adj_apply, adj_apply, map_sub, map_sub, h1, h2, LinearMap.map_smul_of_tower]

variable {π : CuspSub E a} {r : ℝ} {n : ℕ} {e : Fin n → GlobalTheory.GKCoh.Herm E a}

private theorem cocl_comb {q : ℕ} (s : ℂ) {ω η : Geo.Co Ξ q} (hω : Coclosed (smAdj Ξ r) e ω)
    (hη : Coclosed (smAdj Ξ r) e η) : Coclosed (smAdj Ξ r) e (s • ω + η) := by
  have ap : ∀ X, (s • ω + η) X = s • ω X + η X := fun X => rfl
  cases q with
  | zero => trivial
  | succ q =>
    refine AlternatingMap.ext fun X => ?_
    have h1 := DFunLike.congr_fun (show del _ e ω = 0 from hω) X
    have h2 := DFunLike.congr_fun (show del _ e η = 0 from hη) X
    rw [del_apply, AlternatingMap.zero_apply] at h1 h2 ⊢
    simp only [ap, map_add (f := _), map_smul, Finset.sum_add_distrib, h2, add_zero, ← Finset.smul_sum, h1, smul_zero]

private theorem cocl_zero {q : ℕ} : Coclosed (smAdj Ξ r) e (0 : Geo.Co Ξ q) := by
  cases q with
  | zero => trivial
  | succ q => exact AlternatingMap.ext fun X => by simp [del_apply]

private theorem cocl_trans {q : ℕ} (x : GL (Fin a) (Af E)) {ω : Geo.Co Ξ q} (hω : Coclosed (smAdj Ξ r) e ω) :
    Coclosed (smAdj Ξ r) e (Geo.trans x ω) := by
  have ap : ∀ X, Geo.trans x ω X = (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (ω X) := fun X => rfl
  cases q with
  | zero => trivial
  | succ q =>
    refine AlternatingMap.ext fun X => ?_
    have h1 := DFunLike.congr_fun (show del _ e ω = 0 from hω) X
    rw [del_apply, AlternatingMap.zero_apply] at h1 ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ap, ← rT_adj, ← map_sum, h1, map_zero]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.harmSub :
    UpperTheory.V.Cj.HarmSub := by
  intro E _ _ _ a π Ξ r n e q
  obtain ⟨L, L1, L2⟩ := (levSub E a Ξ q).2.2
  have comb : ∀ (s : ℂ) (α β : Geo.Co Ξ q), IsPiHarm π Ξ r e α → IsPiHarm π Ξ r e β → IsPiHarm π Ξ r e (s • α + β) :=
    fun s α β hα hβ => ⟨(L1 _).1 (L.add_mem (L.smul_mem s ((L1 _).2 hα.1)) ((L1 _).2 hβ.1)),
      by rw [dCo_comb, hα.2.1, hβ.2.1, smul_zero, add_zero], cocl_comb s hα.2.2.1 hβ.2.2.1,
      fun X => Submodule.add_mem _ (Submodule.smul_mem _ s (hα.2.2.2 X)) (hβ.2.2.2 X)⟩
  have zero : IsPiHarm π Ξ r e (0 : Geo.Co Ξ q) :=
    ⟨(L1 _).1 L.zero_mem, AlternatingMap.ext fun X => by simp [dCo_apply], cocl_zero, fun X => Submodule.zero_mem _⟩
  refine ⟨{ carrier := {ω | IsPiHarm π Ξ r e ω}, add_mem' := ?_, zero_mem' := zero, smul_mem' := ?_ },
    fun ω => Iff.rfl, ?_⟩
  · intro α β hα hβ
    have := comb 1 α β hα hβ
    rwa [one_smul] at this
  · intro s α hα
    have := comb s α 0 hα zero
    rwa [add_zero] at this
  · rintro x ω ⟨h1, h2, h3, h4⟩
    refine ⟨(L1 _).1 (L2 x ω ((L1 _).2 h1)), ?_, cocl_trans x h3, fun X => mem_tens.2 fun i => ?_⟩
    · obtain ⟨U, -, -, u3⟩ := h1
      rw [(perNat E a U ⊥ x (fun u hu => by rw [Subgroup.mem_bot.1 hu]; simp) Ξ q ω u3).2.1, h2,
        ← transRep_apply, map_zero]
    · rw [cmp_trans]
      exact π.stable (.fin x) _ (mem_tens.1 (h4 X) i)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.RelLin
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

theorem UpperTheory.V.Cj.relLin :
    UpperTheory.V.Cj.RelLin := by
  intro E _ _ _ a U σ Ξ Ξ' h q s α α' β β' ⟨a1, b1, c, d, p1, p2, p3⟩ ⟨a2, b2, c', d', r1, r2, r3⟩
  refine ⟨(levSub E a Ξ q).1 U s _ _ a1 a2, (levSub E a Ξ' q).1 U (σ s) _ _ b1 b2, s • c + c', σ s • d + d', ?_, ?_, ?_⟩
  · simpa only [one_smul] using (perEx E a U Ξ q).2.2 α α' c c' s 1 p1 r1
  · simpa only [one_smul] using (perEx E a U Ξ' q).2.2 β β' d d' (σ s) 1 p2 r2
  · have e : σ s • d + d' - sigC σ h (s • c + c') = σ s • (d - sigC σ h c) + (d' - sigC σ h c') := by
      funext z y i
      simp only [sigC, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul]
      ring
    rw [e]
    exact cobLin _ _ _ q (σ s) _ _ p3 r3
end

