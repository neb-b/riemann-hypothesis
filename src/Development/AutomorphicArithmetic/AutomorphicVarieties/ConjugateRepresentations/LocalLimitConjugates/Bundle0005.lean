module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ValNhds
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem inf_cont (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  have hs : Continuous (sInf E : Cinf E → Ad E) := (GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const
  exact Continuous.units_map _ ((continuous_const.sub continuous_const).add (continuous_id.matrix_map hs))

open scoped Matrix.Norms.Operator in
private theorem val_nhds (E : Type) [Field E] [NumberField E] (a : ℕ) (y : GL (Fin a) (Cinf E))
    {N : Set (GL (Fin a) (Cinf E))} (hN : N ∈ 𝓝 y) : (fun z : GL (Fin a) (Cinf E) => toL z.val) '' N ∈ 𝓝 (toL y.val) :=
  (Units.isOpenEmbedding_val (R := Matrix (Fin a) (Fin a) (Cinf E))).isOpenMap.image_mem_nhds hN

open scoped Pointwise in
private theorem loc_fin {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ] {f : G → ℂ} (hf : HasCompactSupport f) (x : G) :
    ∃ s : Finset Γ, ∀ᶠ z in 𝓝 x, GlobalTheory.AutomorphicL2Unitary.orbitSum Γ f z = ∑ γ ∈ s, f (γ * z) := by
  obtain ⟨K, hK, hx⟩ := exists_compact_mem_nhds x
  have hS : {γ : Γ | (γ : G) ∈ tsupport f * K⁻¹}.Finite := GlobalTheory.AutomorphicL2Unitary.finite_mem_compact (hf.isCompact.mul hK.inv)
  refine ⟨hS.toFinset, Filter.mem_of_superset hx fun z hz => tsum_eq_sum fun γ hγ => ?_⟩
  by_contra h
  exact hγ (hS.mem_toFinset.2 ⟨_, subset_tsupport f h, z⁻¹, Set.inv_mem_inv.2 hz, by simp⟩)

theorem UpperTheory.V.Cj.H.orbSm :
    UpperTheory.V.Cj.H.OrbSm := by
  intro E _ _ _ a u hu
  have hm : GlobalTheory.AutomorphicL2Unitary.orbitSum (latticeGL E a) u.1 ∈ Sm E a := by
    intro g x hx
    obtain ⟨y, hy⟩ := hx
    obtain rfl : x = toL y.val := hy.symm
    obtain ⟨s, hs⟩ := loc_fin (latticeGL E a) hu.1 (g * infGL E a y)
    have hc : Continuous fun z => g * infGL E a z := continuous_const.mul (inf_cont E a)
    have h1 := val_nhds E a y (hc.continuousAt.preimage_mem_nhds hs)
    refine ((ContDiffAt.sum (s := s) fun γ _ =>
      contDiffAt_chart u.2 (γ.1 * g) (val_mem_invSet y)).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [h1]
    rintro _ ⟨z, hz, rfl⟩
    simp only [chart_val, mul_assoc]
    exact hz
  refine ⟨⟨_, hm⟩, ?_, rfl⟩
  have key : ∀ k, act (.fin k) u = u → act (.fin k) (⟨_, hm⟩ : Sm E a) = ⟨_, hm⟩ := fun k hk =>
    Subtype.ext (funext fun g => tsum_congr fun γ => by
      have h : u.1 (γ.1 * g * finGL E a k) = u.1 (γ.1 * g) := congrFun (congrArg Subtype.val hk) _
      rw [← h, mul_assoc])
  let S : ∀ φ : Sm E a, Subgroup (GL (Fin a) (Af E)) := fun φ =>
    { carrier := {k | act (.fin k) φ = φ}
      one_mem' := Subtype.ext (funext fun g => by
        change φ.1 (g * finGL E a 1) = φ.1 g
        rw [map_one, mul_one])
      mul_mem' := fun {k l} hk hl => Subtype.ext (funext fun g => by
        have h1 : φ.1 (g * finGL E a k) = φ.1 g := congrFun (congrArg Subtype.val hk) _
        have h2 : φ.1 (g * finGL E a k * finGL E a l) = φ.1 (g * finGL E a k) := congrFun (congrArg Subtype.val hl) _
        change φ.1 (g * finGL E a (k * l)) = φ.1 g
        rw [map_mul, ← mul_assoc, h2, h1])
      inv_mem' := fun {k} hk => Subtype.ext (funext fun g => by
        have h1 : φ.1 (g * finGL E a k⁻¹ * finGL E a k) = φ.1 (g * finGL E a k⁻¹) :=
          congrFun (congrArg Subtype.val hk) _
        change φ.1 (g * finGL E a k⁻¹) = φ.1 g
        rw [← h1, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]) }
  exact Subgroup.isOpen_mono (H₁ := S u) (H₂ := S ⟨_, hm⟩) key hu.2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.WigHom
section
section SlopeTestRemainingChoices
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible

private def UpperTheory.V.Cj.H.altFlip {A V M : Type} [AddCommGroup A] [Module ℝ A] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup M] [Module ℝ M] {q : ℕ} (φ : A →ₗ[ℝ] (V [⋀^Fin q]→ₗ[ℝ] M)) : V [⋀^Fin q]→ₗ[ℝ] (A →ₗ[ℝ] M) where
  toFun Y :=
    { toFun := fun X => φ X Y
      map_add' := fun X X' => by rw [map_add (f := _), AlternatingMap.add_apply]
      map_smul' := fun c X => by rw [map_smul, AlternatingMap.smul_apply, RingHom.id_apply] }
  map_update_add' Y i x y := LinearMap.ext fun X => (φ X).map_update_add Y i x y
  map_update_smul' Y i c x := LinearMap.ext fun X => (φ X).map_update_smul Y i c x
  map_eq_zero_of_eq' Y _ _ h hij := LinearMap.ext fun X => (φ X).map_eq_zero_of_eq Y h hij

private theorem UpperTheory.V.Cj.H.wigner_homomorphism : UpperTheory.V.Cj.H.WigHom := by
  intro E _ _ _ a M _ _ _ _ L α z hlie hretr
  refine ⟨fun ω h0 h1 Y => ?_, fun q ω h0 h1 => ?_⟩
  · have key : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), L (toL X) (ω Y) = 0 := by
      intro X
      let Z : Matrix (Fin a) (Fin a) (Cinf E) := (1 / 2 : ℝ) • (X - star X)
      have hZ : star Z = -Z := by
        simp only [Z]
        rw [star_smul, star_sub, star_star, star_trivial, ← smul_neg, neg_sub]
      have hX : toL X = toL (hp (toL X)).1 + toL Z := by
        have h : X = (hp (toL X)).1 + Z := by
          rw [hp_val]; simp only [Z]; module
        exact congrArg toL h
      have h3 := DFunLike.congr_fun h1 fun _ => hp (toL X)
      rw [dCo_apply, Fin.sum_univ_one, Subsingleton.elim (Fin.removeNth _ _) Y] at h3
      have h4 : L (toL (hp (toL X)).1) (ω Y) = 0 := by simpa using h3
      rw [congrArg L hX, map_add (f := _), LinearMap.add_apply, h4, h0 Z hZ Y]
      simp
    rw [← hretr (ω Y) 0 fun X => (key (Matrix.of X)).symm, map_zero]
  · let F : Herm E a [⋀^Fin q]→ₗ[ℝ] (Lie E a →ₗ[ℝ] M) := UpperTheory.V.Cj.H.altFlip (ω.curryLeft ∘ₗ hp)
    let ad : Matrix (Fin a) (Fin a) (Cinf E) → Lie E a →ₗ[ℝ] Lie E a := fun Y =>
      { toFun := fun X => toL (Y * Matrix.of X - Matrix.of X * Y)
        map_add' := fun X X' => by
          have h : Y * (Matrix.of X + Matrix.of X') - (Matrix.of X + Matrix.of X') * Y =
              (Y * Matrix.of X - Matrix.of X * Y) + (Y * Matrix.of X' - Matrix.of X' * Y) := by noncomm_ring
          exact congrArg toL h
        map_smul' := fun c X => by
          have h : Y * (c • Matrix.of X) - (c • Matrix.of X) * Y = c • (Y * Matrix.of X - Matrix.of X * Y) := by
            rw [smul_sub, mul_smul_comm, smul_mul_assoc]
          exact congrArg toL h }
    refine ⟨α.compAlternatingMap F, fun Y => ?_⟩
    let G : Fin (q + 1) → Lie E a →ₗ[ℝ] M := fun i =>
      (L (toL (Y i).1)).restrictScalars ℝ ∘ₗ F (i.removeNth Y) - F (i.removeNth Y) ∘ₗ ad (Y i).1
    have h3 : ∀ i, L (toL (Y i).1) (α (F (i.removeNth Y))) = α (G i) := fun i =>
      hlie _ _ _ fun X => (sub_add_cancel _ _).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [dCo_apply, ← hretr (ω Y) (∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • G i) fun X => ?_, map_sum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, ← h3]
      rfl
    · rw [LinearMap.sum_apply]
      exact homId E a M L q ω h1 h0 (Matrix.of X) Y

end SlopeTestRemainingChoices

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.wigHom :
    UpperTheory.V.Cj.H.WigHom :=
  UpperTheory.V.Cj.H.wigner_homomorphism
end

