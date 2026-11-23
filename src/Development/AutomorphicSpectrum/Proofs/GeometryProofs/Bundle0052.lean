module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0049
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0048
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0045
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0044
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0020
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0040
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.WeilBound.CoreStatements.AmpleLineBundles.KillsOverOfSquareZeroIdeal

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualMapOfFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.DualExt

theorem dual_ext : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V'), IsExtOver i j → Submodule.span Ω' (Set.range j) = ⊤ → ∃ jd : Module.Dual Ω V →+ Module.Dual Ω' V', ∀ w e, jd w (j e) = i (w e) := by
  intro Ω Ω' _ _ i V V' _ _ _ _ j hext hspan
  let b := Module.Basis.ofVectorSpace Ω V
  have hj : ∀ e : V, j e = (b.repr e).sum fun k a => i a • j (b k) := by
    intro e
    conv_lhs => rw [← b.linearCombination_repr e]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.sum]
    exact Finset.sum_congr rfl fun k _ => hext.1 _ _
  have hli : LinearIndependent Ω' fun k => j (b k) := by
    rw [linearIndependent_iff_finset_linearIndependent]
    intro s
    have h := hext.2 s.card (fun m => b (s.equivFin.symm m))
      (b.linearIndependent.comp (fun m => (s.equivFin.symm m : _))
        (Subtype.val_injective.comp s.equivFin.symm.injective))
    have h2 := h.comp s.equivFin s.equivFin.injective
    convert h2 using 1
    funext k
    simp
  have hsp : ⊤ ≤ Submodule.span Ω' (Set.range fun k => j (b k)) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨e, rfl⟩
    rw [hj e, Finsupp.sum]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let b' := Module.Basis.mk hli hsp
  refine ⟨AddMonoidHom.mk' (fun w => b'.constr Ω' fun k => i (w (b k))) fun w₁ w₂ => ?_, fun w e => ?_⟩
  · rw [← map_add (f := _)]
    congr 1
    funext k
    simp
  · show b'.constr Ω' (fun k => i (w (b k))) (j e) = i (w e)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hj e, Finsupp.sum, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← b.linearCombination_repr e, Finsupp.linearCombination_apply, Finsupp.sum,
      map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, show j (b k) = b' k from (Module.Basis.mk_apply hli hsp k).symm, Module.Basis.constr_basis,
      map_smul, smul_eq_mul, smul_eq_mul, map_mul]

end GlobalTheory.CompanionTheory.Ar.DualExt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualRevDualRev
section
namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeModel

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {K : Type} {ι : K → Type} {R : Type} [CommRing R]

def dualRev {r : ℕ} (Q : LocPair ι R (Fin r)) : LocPair ι R (Fin r) :=
  ⟨fun i => -Q.x (Fin.rev i), fun i => -Q.x' (Fin.rev i), fun i => Q.g (Fin.rev i), fun i => Q.f (Fin.rev i)⟩

def labelPair (D : Datum H) (T : LocPair ι R (CMType H × Fin (D.p + D.q))) :
    ∀ s : CMType H ⊕ CMType H, LocPair ι R (Fin (labelRk D s))
  | .inl τ => T.comp fun i => (τ, Fin.castAdd D.q i)
  | .inr τ => dualRev (T.comp fun i => (τ, Fin.natAdd D.p i))

def omPair (D : Datum H) (T : LocPair ι R (CMType H × Fin (D.p + D.q))) :
    ∀ s : CMType H ⊕ CMType H, LocPair ι R (Fin (labelRk D s.swap)) :=
  fun s => dualRev (labelPair D T s.swap)

def omPairM (D : Datum H) (T : LocPair ι R (CMType H × Fin (D.p + D.q))) :
    ∀ s : CMType H ⊕ CMType H, LocPair ι R (Fin (Sum.elim (fun _ : CMType H => D.q) (fun _ : CMType H => D.p) s))
  | .inl τ => omPair D T (.inl τ)
  | .inr τ => omPair D T (.inr τ)

theorem dualRev_dualRev {r : ℕ} (Q : LocPair ι R (Fin r)) : dualRev (dualRev Q) = Q := by
  obtain ⟨x, x', f, g⟩ := Q
  simp [dualRev, Fin.rev_rev]

theorem map_map {R' R'' : Type} [CommRing R'] [CommRing R''] {σ : Type} (T : LocPair ι R σ) (ψ : R →+* R')
    (ψ' : R' →+* R'') : (T.map ψ).map ψ' = T.map (ψ'.comp ψ) := by
  obtain ⟨x, x', f, g⟩ := T
  simp [LocPair.map, MvPolynomial.map_map]

end GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatricesRegularGeneric
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem exists_cell {F : Type} [Field F] (O : Subring F) [IsLocalRing O] {n r : ℕ}
    (A : Matrix (Fin n) (Fin r) F) (N : Matrix (Fin r) (Fin n) F) (hA : ∀ a b, A a b ∈ O)
    (hN : ∀ a b, N a b ∈ O) (hNA : N * A = 1) (Y : Matrix (Fin r) (Fin r) F)
    (hs : ∀ i : Fin r, ∃ J, NormAt O (A * Y) ((i : ℕ) + 1) i.2 J) :
    ∃ w : Equiv.Perm (Fin r), ∀ (k : ℕ) (hk : k ≤ r), NormAt O Y k hk (w ∘ Fin.castLE hk) := by
  refine GlobalTheory.T.exists_perm_normalized_minors O Y (fun k hk I' I => GlobalTheory.T.normalized_minor_extends O Y k hk I' I) fun k hk => ?_
  cases k with
  | zero => exact ⟨Fin.elim0, normAt_zero O Y _⟩
  | succ k =>
    obtain ⟨J, hJ⟩ := hs ⟨k, hk⟩
    exact exists_normAt O A N hA hN hNA Y _ hk J hJ

theorem big_cell_smooth : ∀ (Ω : Type) [Field Ω] (S : Type) [Fintype S] (r n : S → ℕ) (R : Subring Ω) (O : Subring (GenField Ω r)) [IsLocalRing O] (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω) (N : ∀ s, Matrix (Fin (r s)) (Fin (n s)) Ω) (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), (∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ O) → (∀ s, (T s).det ≠ 0) → (∀ s j l, M s j l ∈ R) → (∀ s l j, N s l j ∈ R) → (∀ s, N s * M s = 1) → (∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0) → (∀ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ O) → ∃ t ∈ ratioRing R (flagB M T) J, t ≠ 0 ∧ t ∈ O ∧ t⁻¹ ∈ O ∧ ∃ h : ∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ locSub (ratioRing R (flagB M T) J) t, (((algebraMap Ω (GenField Ω r)).comp R.subtype).codRestrict (locSub (ratioRing R (flagB M T) J) t) (fun a => h a a.2)).Smooth := by
  intro Ω _ S _ r n R O _ T M N J hRO hT hM hN hNM hJ0 hJr
  classical
  haveI : Finite (GenIx r) := by unfold GenIx; infer_instance
  set i := algebraMap Ω (GenField Ω r) with hi
  set A := ratioRing R (flagB M T) J with hAdef
  let Y : ∀ s, Matrix (Fin (r s)) (Fin (r s)) (GenField Ω r) := fun s => (T s).map i * genU Ω r s
  let Am : ∀ s, Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r) := fun s => (M s).map i
  let Nm : ∀ s, Matrix (Fin (r s)) (Fin (n s)) (GenField Ω r) := fun s => (N s).map i
  have hB : ∀ s, flagB M T s = Am s * Y s := fun s => by
    show (M s * T s).map i * genU Ω r s = (M s).map i * ((T s).map i * genU Ω r s)
    rw [Matrix.map_mul, Matrix.mul_assoc]
  have hNA : ∀ s, Nm s * Am s = 1 := fun s => by
    show (N s).map i * (M s).map i = 1
    rw [← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero _) (map_one _)]
  have hYN : ∀ s, Nm s * flagB M T s = Y s := fun s => by
    rw [hB, ← Matrix.mul_assoc, hNA, Matrix.one_mul]
  have hAmO : ∀ s a b, Am s a b ∈ O := fun s a b => hRO _ (hM _ _ _)
  have hNmO : ∀ s a b, Nm s a b ∈ O := fun s a b => hRO _ (hN _ _ _)

  have hw : ∀ s, ∃ w : Equiv.Perm (Fin (r s)), ∀ (k : ℕ) (hk : k ≤ r s),
      NormAt O (Y s) k hk (w ∘ Fin.castLE hk) := fun s =>
    exists_cell O (Am s) (Nm s) (hAmO s) (hNmO s) (hNA s) (Y s) fun i' => by
      refine ⟨J ⟨s, i'⟩, ?_⟩
      rw [← hB]
      exact ⟨hJ0 ⟨s, i'⟩, hJr ⟨s, i'⟩⟩
  choose w hw using hw
  have hlu := fun s => GlobalTheory.T.lu_decomposition_of_minors ((Y s).submatrix (w s) id) fun k hk => (hw s k hk).1
  choose C V hC hV0 hV1 hCV using hlu

  let v : GenIx r → GenField Ω r := fun q => V q.1 q.2.1.1 q.2.1.2
  set B := Subring.closure (((R.map i : Subring _) : Set (GenField Ω r)) ∪ Set.range v) with hBdef
  have hRB : ∀ a ∈ R, i a ∈ B := fun a ha =>
    Subring.subset_closure (Or.inl ⟨a, ha, rfl⟩)
  have hRA : ∀ a ∈ R, i a ∈ A := fun a ha =>
    Subring.subset_closure (Or.inl ⟨a, ha, rfl⟩)
  have hVB : ∀ s l k, V s l k ∈ B := fun s l k => by
    rcases lt_trichotomy l k with h | h | h
    · rw [hV0 s l k h]; exact B.zero_mem
    · rw [h, hV1]; exact B.one_mem
    · exact Subring.subset_closure (Or.inr ⟨⟨s, ⟨(l, k), h⟩⟩, rfl⟩)

  let y0 : (q : Σ s, Fin (r s)) → GenField Ω r := fun q =>
    kMinor (Y q.1) ((q.2 : ℕ) + 1) q.2.2 (w q.1 ∘ Fin.castLE q.2.2)
  have hy0 : ∀ q, y0 q ≠ 0 := fun q => (hw q.1 _ q.2.2).1
  have hrat : ∀ (s : S) (k : ℕ) (hk : k ≤ r s) (I : Fin k → Fin (r s)),
      kMinor (Y s) k hk (w s ∘ I) / kMinor (Y s) k hk (w s ∘ Fin.castLE hk) = kMinor (V s) k hk I :=
    fun s k hk I => ratio_eq_kMinor ((Y s).submatrix (w s) id) (C s) (V s) (hC s) (hV0 s) (hV1 s) (hCV s) k hk I
      (hw s k hk).1
  have hyB : ∀ (q : Σ s, Fin (r s)) I, kMinor (Y q.1) ((q.2 : ℕ) + 1) q.2.2 I / y0 q ∈ B := fun q I => by
    have e : I = w q.1 ∘ ((w q.1).symm ∘ I) := by
      ext a; simp
    rw [e]
    show kMinor (Y q.1) _ q.2.2 _ / kMinor (Y q.1) _ q.2.2 _ ∈ B
    rw [hrat]
    exact kMinor_mem B _ (hVB q.1) _ _ _
  have hPB : ∀ (q : Σ s, Fin (r s)) J', stepMinor (flagB M T q.1) q.2 J' / y0 q ∈ B := fun q J' => by
    rw [hB, stepMinor_eq_kMinor]
    exact kMinor_mul_div_mem B (Am q.1) (Y q.1) _ q.2.2 _ (fun a b => hRB _ (hM _ _ _)) (hyB q) J'
  have hPA : ∀ (q : Σ s, Fin (r s)) J', stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ A :=
    fun q J' => Subring.subset_closure (Or.inr ⟨q, J', rfl⟩)
  have hyA : ∀ (q : Σ s, Fin (r s)) I, kMinor (Y q.1) ((q.2 : ℕ) + 1) q.2.2 I /
      stepMinor (flagB M T q.1) q.2 (J q) ∈ A := fun q I => by
    rw [← hYN q.1]
    exact kMinor_mul_div_mem A (Nm q.1) (flagB M T q.1) _ q.2.2 _ (fun a b => hRA _ (hN _ _ _)) (hPA q) I
  have hAO : A ≤ O := by
    refine Subring.closure_le.2 ?_
    rintro a (⟨b, hb, rfl⟩ | ⟨q, J', rfl⟩)
    · exact hRO b hb
    · exact hJr q J'

  let tq : (Σ s, Fin (r s)) → GenField Ω r := fun q => y0 q / stepMinor (flagB M T q.1) q.2 (J q)
  have htq0 : ∀ q, tq q ≠ 0 := fun q => div_ne_zero (hy0 q) (hJ0 q)
  have htqA : ∀ q, tq q ∈ A := fun q => hyA q _
  have htqB : ∀ q, (tq q)⁻¹ ∈ B := fun q => by
    show (y0 q / _)⁻¹ ∈ B
    rw [inv_div]
    exact hPB q _
  have htqO : ∀ q, (tq q)⁻¹ ∈ O := fun q => by
    show (y0 q / _)⁻¹ ∈ O
    rw [inv_div, hB, stepMinor_eq_kMinor]
    exact kMinor_mul_div_mem O (Am q.1) (Y q.1) _ q.2.2 _ (hAmO q.1) (hw q.1 _ q.2.2).2 _
  have hAB : A ≤ Subring.closure ((B : Set (GenField Ω r)) ∪ Set.range tq) := by
    refine Subring.closure_le.2 ?_
    rintro a (⟨b, hb, rfl⟩ | ⟨q, J', rfl⟩)
    · exact Subring.subset_closure (Or.inl (hRB b hb))
    · have e : stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) =
          (stepMinor (flagB M T q.1) q.2 J' / y0 q) * tq q := by
        show _ = _ * (y0 q / _)
        have := hy0 q
        have := hJ0 q
        field_simp
      rw [SetLike.mem_coe, e]
      exact mul_mem (Subring.subset_closure (Or.inl (hPB q J'))) (Subring.subset_closure (Or.inr ⟨q, rfl⟩))
  have hBA : B ≤ Subring.closure ((A : Set (GenField Ω r)) ∪ Set.range fun q => (tq q)⁻¹) := by
    refine Subring.closure_le.2 ?_
    rintro a (⟨b, hb, rfl⟩ | ⟨q, rfl⟩)
    · exact Subring.subset_closure (Or.inl (hRA b hb))
    · obtain ⟨s, ⟨⟨l, k⟩, hlk⟩⟩ := q
      have hlk' : k < l := hlk
      have e1 : V s l k = kMinor (Y s) ((k : ℕ) + 1) k.2 (w s ∘ lastRow k l) / y0 ⟨s, k⟩ := by
        rw [← kMinor_lower_lastRow (V s) (hV0 s) (hV1 s) k l hlk', ← hrat]
      have e2 : V s l k = (kMinor (Y s) ((k : ℕ) + 1) k.2 (w s ∘ lastRow k l) /
          stepMinor (flagB M T s) k (J ⟨s, k⟩)) * (tq ⟨s, k⟩)⁻¹ := by
        rw [e1]
        show _ = _ * (y0 ⟨s, k⟩ / _)⁻¹
        have := hy0 ⟨s, k⟩
        have := hJ0 ⟨s, k⟩
        field_simp
      show V s l k ∈ _
      rw [e2]
      exact mul_mem (Subring.subset_closure (Or.inl (hyA ⟨s, k⟩ _))) (Subring.subset_closure (Or.inr ⟨_, rfl⟩))

  have hv : AlgebraicIndependent Ω v := by
    refine _root_.GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.algebraicIndependent_of_mem_adjoin_range _ v (genU_indep Ω r) fun q => ?_
    rw [← genU_gen]
    have hmem : ∀ s l k, V s l k ∈ IntermediateField.adjoin Ω (Set.range v) := fun s l k => by
      rcases lt_trichotomy l k with h | h | h
      · rw [hV0 s l k h]; exact zero_mem _
      · rw [h, hV1]; exact one_mem _
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨s, ⟨(l, k), h⟩⟩, rfl⟩
    refine entries_mem _ ((T q.1).submatrix (w q.1) id) ?_ (genU Ω r q.1) (C q.1) (V q.1)
      (genU_zero Ω r q.1) (genU_one Ω r q.1) (hC q.1) (hV0 q.1) (hV1 q.1) ?_ (hmem q.1) _ _ q.2.2
    · rw [Matrix.det_permute]
      exact mul_ne_zero (by rcases Int.units_eq_one_or (Equiv.Perm.sign (w q.1)) with h | h <;> simp [h]) (hT _)
    · rw [← hCV q.1]
      congr 1

  have hL := _root_.GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.locSub_eq_of_inverse_family A B tq htq0 htqA htqB hAB hBA
  have htA : (∏ q, tq q) ∈ A := A.prod_mem fun q _ => htqA q
  have hinv : (∏ q, tq q)⁻¹ = ∏ q, (tq q)⁻¹ := (Finset.prod_inv_distrib _).symm
  refine ⟨∏ q, tq q, htA, Finset.prod_ne_zero_iff.2 fun q _ => htq0 q, hAO htA, ?_, ?_⟩
  · rw [hinv]
    exact O.prod_mem fun q _ => htqO q
  have hR : ∀ a ∈ R, i a ∈ locSub A (∏ q, tq q) := fun a ha => le_locSub _ _ (hRA a ha)
  refine ⟨hR, ?_⟩
  have gen : ∀ (L : Subring (GenField Ω r)), L = locSub B (∏ q, tq q)⁻¹ → ∀ h : ∀ a ∈ R, i a ∈ L,
      ((i.comp R.subtype).codRestrict L (fun a => h a a.2)).Smooth := by
    rintro _ rfl h
    refine _root_.GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.smooth_locSub_closure R v hv _ ?_ (inv_ne_zero (Finset.prod_ne_zero_iff.2 fun q _ => htq0 q)) h
    rw [hinv]
    exact B.prod_mem fun q _ => htqB q
  exact gen _ hL hR

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralElementRegular
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.IntReg

theorem mem_regAt_of_isIntegral_of_stalk :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (p : Cpt ξ), IsCptGen ξ →
      IsIntegrallyClosed (X.presheaf.stalk p.1) → ∀ a : Ω, IsIntegral ℤ a → a ∈ regAt ξ p := by
  intro X Ω _ ξ p hξ hcl a ha
  have hinj : Function.Injective (genMap ξ p) := hξ.inj p
  let _ : Algebra (X.presheaf.stalk p.1) Ω := (genMap ξ p).toAlgebra
  have hmap : ∀ x, algebraMap (X.presheaf.stalk p.1) Ω x = genMap ξ p x := fun _ => rfl
  have : IsDomain (X.presheaf.stalk p.1) := hinj.isDomain _
  have : FaithfulSMul (X.presheaf.stalk p.1) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : IsFractionRing (X.presheaf.stalk p.1) Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨b, c, hc, e⟩ := exists_frac_genMap ξ hξ p z
    exact ⟨b, c, by rw [hmap, hmap, ← e, mul_div_cancel_right₀ _ hc]⟩
  have hb : _root_.IsIntegral (X.presheaf.stalk p.1) a := ha.tower_top
  obtain ⟨w, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hb
  exact ⟨w, rfl⟩

end GlobalTheory.CompanionTheory.Ar.IntReg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

def IsOver {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type}
    [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (κ : c.F →+* ℂ)
    (p : Sp ℂ ⟶ Xo.X) : Prop :=
  ∃ x : Sp ℂ ⟶ Xo.XF c, x ≫ Y.j = z ≫ 𝔐.f ∧ x ≫ pullback.fst _ _ = p ∧ x ≫ pullback.snd _ _ = spMap κ

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsCoordTie
section
noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar.Retie

open GlobalTheory.CompanionTheory.Ar.ProjCoord

section Transport

variable {X Y : Scheme.{0}} {Ω : Type} [Field Ω]

theorem specializes_of_iso (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsIso f] {y : Y}
    (h : genPt (η ≫ f) ⤳ f y) : genPt η ⤳ y := by
  have h1 := h.map (inv f).continuous
  have e : ∀ z : Y, (inv f) (f z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  have e2 : genPt (η ≫ f) = f (genPt η) := Scheme.Hom.comp_apply _ _ _
  rw [e2, e, e] at h1
  exact h1

theorem exists_push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsIso f] (q : Cpt (η ≫ f)) :
    ∃ p : Cpt η, push η f p = q := by
  obtain ⟨q, hq⟩ := q
  obtain ⟨y, rfl⟩ : ∃ y, f y = q := ⟨(inv f) q, by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
  exact ⟨⟨y, specializes_of_iso η f hq⟩, rfl⟩

theorem inChart_push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsIso f] {κ : Type} (x : κ → Ω) (c : κ)
    (p : Cpt η) : InChart (η ≫ f) x c (push η f p) ↔ InChart η x c p := by
  unfold InChart
  rw [regAt_push]

theorem coordTie_comp_iso {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsIso f] (h : CoordTie o η x) :
    CoordTie o (η ≫ f) x := by
  refine ⟨⟨?_, fun q => ?_⟩, fun q => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · rw [Scheme.stalkClosedPointTo_comp η f]
    have hb : Function.Bijective (f.stalkMap (η (IsLocalRing.closedPoint Ω))).hom :=
      ConcreteCategory.bijective_of_isIso _
    exact h.gen.bij.comp hb
  · obtain ⟨p, rfl⟩ := exists_push η f q
    exact genMap_push_injective η f p (h.gen.inj p)
  · obtain ⟨p, rfl⟩ := exists_push η f q
    obtain ⟨c, hc⟩ := h.cover p
    exact ⟨c, (inChart_push η f x c p).2 hc⟩
  · obtain ⟨U, hU, hq⟩ := h.affine c hc
    refine ⟨(inv f) ⁻¹ᵁ U, hU.preimage (inv f), fun q => ?_⟩
    obtain ⟨y, rfl⟩ : ∃ y, f y = q := ⟨(inv f) q, by
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
    have e : (inv f) (f y) = y := by
      rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
    have e1 : f y ∈ (inv f) ⁻¹ᵁ U ↔ y ∈ U := by
      change (inv f) (f y) ∈ U ↔ _
      rw [e]
    rw [e1, hq y]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(push η f ⟨y, h1⟩).2, (inChart_push η f x c ⟨y, h1⟩).2 h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨specializes_of_iso η f h1, (inChart_push η f x c ⟨y, specializes_of_iso η f h1⟩).1 h2⟩
  · rw [h.ring c hc a]
    constructor
    · intro H q hq
      obtain ⟨p, rfl⟩ := exists_push η f q
      rw [regAt_push]
      exact H p ((inChart_push η f x c p).1 hq)
    · intro H p hp
      have := H (push η f p) ((inChart_push η f x c p).2 hp)
      rwa [regAt_push] at this

end Transport

theorem dominates_id_iff {X Y : Scheme.{0}} {Ω : Type} [Field Ω] {ξ' : Spec (CommRingCat.of Ω) ⟶ Y}
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {f : Y ⟶ X} : Dominates ξ' ξ f (RingHom.id Ω) ↔ ξ' ≫ f = ξ := by
  unfold Dominates
  rw [show CommRingCat.ofHom (RingHom.id Ω) = 𝟙 (CommRingCat.of Ω) from rfl, Spec.map_id, Category.id_comp]

theorem mem_ctrSet_self {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ]
    {x : κ → Ω} (M : PModel o x) (p : Cpt M.ξ) : p ∈ ctrSet o x (RingHom.id Ω) M.ξ := by
  obtain ⟨c, hc⟩ := M.tie.cover p
  exact ⟨c, hc.1, fun a ha => (_root_.GlobalTheory.CompanionTheory.Ar.chart_regAt_localisation o Ω κ x M c p hc).1 a ha⟩

theorem mem_ctrSet_join {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ]
    {x : κ → Ω} (M : PModel o x) {κ' : Type} {w : κ' → Ω} (p : Cpt M.ξ) (hw : ∃ l, InChart M.ξ w l p) :
    p ∈ ctrSet o (joinCo (RingHom.id Ω) x w) (RingHom.id Ω) M.ξ := by
  obtain ⟨c, hc⟩ := M.tie.cover p
  obtain ⟨l, hl⟩ := hw
  refine ⟨(c, l), mul_ne_zero hc.1 hl.1, fun a ha => ?_⟩
  change a ∈ regAt M.ξ p
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨⟨j, m⟩, rfl⟩ := hy
    have e : joinCo (RingHom.id Ω) x w (j, m) / joinCo (RingHom.id Ω) x w (c, l) =
        (x j / x c) * (w m / w l) := by
      simp only [joinCo, RingHom.id_apply]
      rw [mul_div_mul_comm]
    beta_reduce
    rw [e]
    exact mul_mem (hc.2 j) (hl.2 m)
  | algebraMap r =>
    exact (_root_.GlobalTheory.CompanionTheory.Ar.chart_regAt_localisation o Ω κ x M c p hc).1 _ (Subalgebra.algebraMap_mem _ r)
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

theorem coordTie_join_of_charts : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ]
    (x : κ → Ω) (M : PModel o x) (κ' : Type) [Finite κ'] (w : κ' → Ω),
    (∀ p : Cpt M.ξ, ∃ l, InChart M.ξ w l p) → CoordTie o M.ξ (joinCo (RingHom.id Ω) x w) := by
  intro o _ Ω _ _ κ _ x M κ' _ w hw
  have hl : ∃ l, w l ≠ 0 := by
    obtain ⟨l, h⟩ := hw ⟨genPt M.ξ, specializes_rfl⟩
    exact ⟨l, h.1⟩
  obtain ⟨M', f, hf⟩ := _root_.GlobalTheory.CompanionTheory.Ar.join_exists o Ω κ x M Ω (RingHom.id Ω) κ' w (fun _ => rfl) hl
    (eq_top_iff.2 fun a _ => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
  obtain ⟨g, hg, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.ChMorph.existsUnique_dominates o Ω (κ × κ') _ M' o Ω κ x M (RingHom.id Ω)
    (fun p => mem_ctrSet_join M p (hw p))
  rw [dominates_id_iff] at hf hg
  have u1 := _root_.GlobalTheory.CompanionTheory.Ar.ChMorph.existsUnique_dominates o Ω κ x M o Ω κ x M (RingHom.id Ω) (mem_ctrSet_self M)
  have u2 := _root_.GlobalTheory.CompanionTheory.Ar.ChMorph.existsUnique_dominates o Ω (κ × κ') _ M' o Ω (κ × κ') _ M' (RingHom.id Ω) (mem_ctrSet_self M')
  have e1 : g ≫ f = 𝟙 _ := u1.unique (dominates_id_iff.2 (by rw [← Category.assoc, hg, hf]))
    (dominates_id_iff.2 (Category.comp_id _))
  have e2 : f ≫ g = 𝟙 _ := u2.unique (dominates_id_iff.2 (by rw [← Category.assoc, hf, hg]))
    (dominates_id_iff.2 (Category.comp_id _))
  haveI : IsIso f := ⟨g, e2, e1⟩
  have := coordTie_comp_iso M'.ξ f M'.tie
  rwa [hf] at this

end GlobalTheory.CompanionTheory.Ar.Retie
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KillsOverSquareZeroLift
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem killsOver_of_sq_zero : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] (u : splitTorus S X ⟶ G) [IsMonHom u] (Y : AddSubgroup X) (B : Type) [CommRing B] [IsLocalRing B] (b : Sp B ⟶ S) (I : Ideal B), I ^ 2 = ⊥ → KillsOver u Y (spMap (Ideal.Quotient.mk I) ≫ b) → KillsOver u Y b :=
  @CoverDenseAlt.kills_over_of_square_zero_ideal

end GlobalTheory.CompanionTheory.Ar
end

