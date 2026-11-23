module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0344
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0247

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBdRPlusLatticeGeneratorsDdR
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BdRLatticeGens

variable {l : ℕ} [Fact l.Prime]

theorem iota_sigma {K : FinExt l} {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) (g : ↥(GK K)) (b : Per.Bcris l) :
    C.ι (Per.σB (g : GQ l) b) = Per.σD (g : GQ l) (C.ι b) := by
  obtain ⟨b0, rfl⟩ := T.eB.surjective b
  have h1 := (P.PD K).ι_comm g b0
  rw [P.PD_ι, P.PD_ι, P.PD_actB, P.PD_actdR] at h1
  rw [← T.actB, ← hF.ι, ← hF.ι, h1, T.actD]

theorem iota_zB {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) (a : ℤ_[l]) : C.ι (Per.zB l a) = Per.zD l a := by
  rw [← T.zB, ← hF.ι, AlgHom.commutes, T.zD]

theorem sigma_U' {d : ℕ} {K : FinExt l} (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l]))
    (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)) (hUU : U * U' = 1)
    (hU : ∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) (g : ↥(GK K)) :
    U'.map (Per.σB (g : GQ l)) = U' * (ρ g).map (Per.zB l) := by
  have h1 : U.map (Per.σB (g : GQ l)) * U'.map (Per.σB (g : GQ l)) = 1 := by
    rw [← Matrix.map_mul, hUU, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (ρ g).map (Per.zB l) = U * U'.map (Per.σB (g : GQ l)) := by
    conv_rhs => rw [← hU g]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have h3 : U' * U = 1 := mul_eq_one_comm.1 hUU
  rw [h2, ← Matrix.mul_assoc, h3, Matrix.one_mul]

theorem inv_vec {K : FinExt l} {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) {d : ℕ} (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l]))
    (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)) (hUU : U * U' = 1)
    (hU : ∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U)
    (v : Fin d → Per.BdR l)
    (hv : ∀ g : ↥(GK K), ((ρ g).map (Per.zD l)).mulVec (fun r => Per.σD (g : GQ l) (v r)) = v)
    (g : ↥(GK K)) (r : Fin d) :
    Per.σD (g : GQ l) ((U'.map C.ι).mulVec v r) = (U'.map C.ι).mulVec v r := by
  rw [RingHom.map_mulVec]
  have e1 : (U'.map C.ι).map (Per.σD (g : GQ l)) = U'.map C.ι * (ρ g).map (Per.zD l) := by
    have : (U'.map C.ι).map (Per.σD (g : GQ l)) = (U'.map (Per.σB (g : GQ l))).map C.ι := by
      ext a b; simp [iota_sigma hF g]
    rw [this, sigma_U' ρ U U' hUU hU g, Matrix.map_mul]
    congr 1
    ext a b; simp [iota_zB hF]
  rw [e1, ← Matrix.mulVec_mulVec]
  exact congrFun (congrArg _ (hv g)) r

theorem isUnit_aDp_zA {y : ℤ_[l]} (hy : y ≠ 0) : IsUnit (aDp l (Per.zA l y)) := by
  rw [PadicInt.unitCoeff_spec hy, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]
  exact ((PadicInt.unitCoeff hy).isUnit.map _).map _ |>.mul ((isUnit_l_BdRp l).pow _)

theorem oD_int (C : Core l) (y : ℤ_[l]) (x : Om l) :
    C.oD (algebraMap ℚ_[l] (Om l) (y : ℚ_[l]) * x) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l y)) * C.oD x := by
  rw [map_mul]
  congr 1
  simp only [Core.oD, RingHom.comp_apply, C.o_sec.z]

theorem descend {K : FinExt l} (C : Core l) (hI : C.InvdR) {d : ℕ} (w : Fin d → Per.BdR l)
    (hw : ∀ (g : ↥(GK K)) r, Per.σD (g : GQ l) (w r) = w r) :
    ∃ (y : ℤ_[l]) (z : Fin d → ↥(OL K)), y ≠ 0 ∧
      ∀ r, C.oD (K.1.val.toRingHom ((OL K).val.toRingHom (z r))) =
        algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l y)) * w r := by
  have hx : ∀ r, ∃ x ∈ K.1, C.oD x = w r := fun r => hI K (w r) (fun g hg => hw ⟨g, hg⟩ r)
  choose x hxK hxw using hx
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  classical
  obtain ⟨y, hy0, hint⟩ := exists_integral_multiples ℤ_[l] ℚ_[l]
    (Finset.univ.image fun r => (⟨x r, hxK r⟩ : ↥K.1))
  refine ⟨y, fun r => ⟨y • ⟨x r, hxK r⟩, hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ r))⟩, hy0, fun r => ?_⟩
  rw [← hxw r, ← oD_int]
  congr 1
  change ((y • (⟨x r, hxK r⟩ : ↥K.1) : ↥K.1) : Om l) = _
  rw [← algebraMap_smul ℚ_[l] y, Algebra.smul_def]
  simp

theorem exists_lattice_generators : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → C.InvdR → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)), U * U' = 1 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) → (∀ j : Fin d, ∃ (m : ℕ) (k : Fin m → ℤ) (c : Fin m → Per.BdR l) (v : Fin m → Fin d → Per.BdR l), (∀ i (g : ↥(GK K)), ((ρ g).map (Per.zD l)).mulVec (fun r => Per.σD (g : GQ l) (v i r)) = v i) ∧ (∀ i r, v i r ∈ Per.FilD l (k i)) ∧ (∀ i, c i ∈ Per.FilD l (-k i)) ∧ (Pi.single j 1 : Fin d → Per.BdR l) = ∑ i, c i • v i) → ∀ N₀ : ℕ, ∃ (N m : ℕ) (k : Fin m → ℤ) (c : Matrix (Fin d) (Fin m) (↥(OL K))) (β : Matrix (Fin m) (Fin d) (Per.BdR l)), N₀ ≤ N ∧ (∀ i, |k i| ≤ N) ∧ (∀ r s, C.ι (U r s) ∈ Per.FilD l (-(N : ℤ))) ∧ (∀ r i, (U.map C.ι * c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom))) r i ∈ Per.FilD l (k i)) ∧ (∀ i j, β i j ∈ Per.FilD l (-k i)) ∧ U.map C.ι * c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) * β = 1 := by
  intro l _ K P AI T C hF hI d ρ U U' hUU hU hfam N₀
  have hfil := _root_.GlobalTheory.MemLoc.seed_fil l C (xi C.ε) C.ker_theta.symm
  obtain ⟨-, -, hmono, -, hbd, -, -⟩ := hfil
  choose m k c v hv hvF hcF hsum using hfam
  have hUι : U.map C.ι * U'.map C.ι = 1 := by
    rw [← Matrix.map_mul, hUU, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcol : ∀ (j : Fin d) (a : Fin (m j)), ∃ (y : ℤ_[l]) (z : Fin d → ↥(OL K)), y ≠ 0 ∧
      ∀ r, (U.map C.ι).mulVec (fun s => C.oD (K.1.val.toRingHom ((OL K).val.toRingHom (z s)))) r =
        algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l y)) * v j a r := by
    intro j a
    obtain ⟨y, z, hy0, hz⟩ := descend (K := K) C hI ((U'.map C.ι).mulVec (v j a))
      (inv_vec hF ρ U U' hUU hU (v j a) (hv j a))
    refine ⟨y, z, hy0, fun r => ?_⟩
    have : (fun s => C.oD (K.1.val.toRingHom ((OL K).val.toRingHom (z s)))) =
        (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l y))) • (U'.map C.ι).mulVec (v j a) := by
      ext s; rw [hz s]; rfl
    rw [this, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hUι, Matrix.one_mulVec]
    rfl
  choose y z hy0 hz using hcol
  choose n hn using hbd

  classical
  let e : Fin (∑ j, m j) ≃ (Σ j : Fin d, Fin (m j)) := finSigmaFinEquiv.symm
  let inv : (p : Σ j : Fin d, Fin (m j)) → Per.BdRp l := fun p => ((isUnit_aDp_zA (hy0 p.1 p.2)).unit⁻¹ : (Per.BdRp l)ˣ)
  let kk : Fin (∑ j, m j) → ℤ := fun i => k (e i).1 (e i).2
  let cc : Matrix (Fin d) (Fin (∑ j, m j)) ↥(OL K) := fun r i => z (e i).1 (e i).2 r
  let β : Matrix (Fin (∑ j, m j)) (Fin d) (Per.BdR l) := fun i j' =>
    if (e i).1 = j' then algebraMap (Per.BdRp l) (Per.BdR l) (inv (e i)) * c (e i).1 (e i).2 else 0
  let N : ℕ := max N₀ (max (Finset.univ.sup fun i => (kk i).natAbs) (Finset.univ.sup fun q : Fin d × Fin d => n (C.ι (U q.1 q.2))))
  have hA : ∀ r i, (U.map C.ι * cc.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom))) r i =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (y (e i).1 (e i).2))) * v (e i).1 (e i).2 r := by
    intro r i
    rw [← hz]
    rfl
  refine ⟨N, ∑ j, m j, kk, cc, β, le_max_left _ _, fun i => ?_, fun r s => ?_, fun r i => ?_, fun i j' => ?_, ?_⟩
  · have h1 : (kk i).natAbs ≤ N :=
      le_trans (Finset.le_sup (f := fun i => (kk i).natAbs) (Finset.mem_univ i))
        (le_trans (le_max_left _ _) (le_max_right _ _))
    rw [Int.abs_eq_natAbs]; exact_mod_cast h1
  · have h1 : n (C.ι (U r s)) ≤ N :=
      le_trans (Finset.le_sup (f := fun q : Fin d × Fin d => n (C.ι (U q.1 q.2))) (Finset.mem_univ (r, s)))
        (le_trans (le_max_right _ _) (le_max_right _ _))
    exact hmono _ _ (by simpa using h1) (hn _)
  · rw [hA, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hvF _ _ _)
  · simp only [β]
    split_ifs
    · rw [← Algebra.smul_def]; exact Submodule.smul_mem _ _ (hcF _ _)
    · exact Submodule.zero_mem _
  · ext r j'
    rw [Matrix.mul_apply]
    simp_rw [hA]
    let G : (Σ j : Fin d, Fin (m j)) → Per.BdR l := fun p =>
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (y p.1 p.2))) * v p.1 p.2 r *
        (if p.1 = j' then algebraMap (Per.BdRp l) (Per.BdR l) (inv p) * c p.1 p.2 else 0)
    have e1 : ∀ i, algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (y (e i).1 (e i).2))) * v (e i).1 (e i).2 r * β i j' = G (e i) := fun i => rfl
    simp_rw [e1]
    rw [Equiv.sum_comp e G, Fintype.sum_sigma, Finset.sum_eq_single j']
    · have hs : ∀ a : Fin (m j'), G ⟨j', a⟩ = c j' a * v j' a r := by
        intro a
        show algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (y j' a))) * v j' a r *
          (if j' = j' then algebraMap (Per.BdRp l) (Per.BdR l) (inv ⟨j', a⟩) * c j' a else 0) = _
        rw [if_pos rfl]
        have hu : algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (y j' a))) *
            algebraMap (Per.BdRp l) (Per.BdR l) (inv ⟨j', a⟩) = 1 := by
          rw [← map_mul, show aDp l (Per.zA l (y j' a)) * inv ⟨j', a⟩ = 1 from
            (isUnit_aDp_zA (hy0 j' a)).mul_val_inv, map_one]
        calc _ = (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (y j' a))) *
            algebraMap (Per.BdRp l) (Per.BdR l) (inv ⟨j', a⟩)) * (c j' a * v j' a r) := by ring
          _ = _ := by rw [hu, one_mul]
      simp_rw [hs]
      have h2 := congrFun (hsum j') r
      rw [Finset.sum_apply] at h2
      simp only [Pi.smul_apply, smul_eq_mul] at h2
      rw [← h2, Pi.single_apply, Matrix.one_apply]
    · intro j _ hj
      exact Finset.sum_eq_zero fun a _ => by simp [G, hj]
    · intro h; exact absurd (Finset.mem_univ j') h

end GlobalTheory.BdRLatticeGens
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinEisensteinLatticeBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.LocalizedLatticeBasis

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem l_ne_zero : (l : bk.S) ≠ 0 := by
  intro h
  have h2 := congrArg (fun x => bk.str.symm (Ideal.Quotient.mk _ x)) h
  simp only [map_natCast, map_zero] at h2
  exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h2

theorem isDomain_loc : IsDomain (Localization.Away (l : bk.S)) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (l_ne_zero bk))

theorem inj_loc : Function.Injective (algebraMap bk.S (Localization.Away (l : bk.S))) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors (l_ne_zero bk))

theorem clear {α β : Type} [Fintype α] [Fintype β]
    (A : Matrix α β (Localization.Away (l : bk.S))) :
    ∃ k : ℕ, ∀ j, k ≤ j → ∃ A₀ : Matrix α β bk.S,
      A₀.map (algebraMap bk.S (Localization.Away (l : bk.S))) =
        (algebraMap bk.S (Localization.Away (l : bk.S)) (l : bk.S)) ^ j • A := by
  obtain ⟨⟨b, hb⟩, h⟩ := IsLocalization.exist_integer_multiples (Submonoid.powers (l : bk.S))
    (Finset.univ : Finset (α × β)) (fun p => A p.1 p.2)
  obtain ⟨k, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.1 hb
  refine ⟨k, fun j hj => ?_⟩
  have h' : ∀ p : α × β, ∃ s : bk.S, algebraMap bk.S _ s = ((l : bk.S) ^ k) • A p.1 p.2 := by
    intro p
    obtain ⟨s, hs⟩ := h p (Finset.mem_univ _)
    exact ⟨s, hs⟩
  choose s hs using h'
  refine ⟨Matrix.of fun i i' => (l : bk.S) ^ (j - k) * s (i, i'), ?_⟩
  ext i i'
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, map_mul, map_pow, hs, smul_eq_mul,
    Algebra.smul_def]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hj]

end GlobalTheory.BSP.LocalizedLatticeBasis

namespace GlobalTheory.BSP.LocalizedLatticeBasis

theorem pid_basis {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (d m : ℕ)
    (Y : Matrix (Fin d) (Fin m) R) (e : R) (he : e ≠ 0) :
    ∃ (X X' Rm : Matrix (Fin d) (Fin d) R) (Q : Matrix (Fin m) (Fin d) R) (Q' : Matrix (Fin d) (Fin m) R),
      X = Y * Q + e • Rm ∧ Y = X * Q' ∧ X * X' = e • (1 : Matrix (Fin d) (Fin d) R) := by
  classical
  let g : Fin m ⊕ Fin d → (Fin d → R) := fun s => Sum.elim (fun k i => Y i k) (fun j => e • Pi.single j 1) s
  let N : Submodule R (Fin d → R) := Submodule.span R (Set.range g)
  obtain ⟨k, bN⟩ := Submodule.basisOfPid (Pi.basisFun R (Fin d)) N
  have gmem : ∀ s, g s ∈ N := fun s => Submodule.subset_span ⟨s, rfl⟩
  have hk : k = d := by
    apply le_antisymm
    · have h1 := Submodule.finrank_le N
      rw [Module.finrank_eq_card_basis bN, Module.finrank_fin_fun] at h1
      simpa using h1
    · have hli : LinearIndependent R (fun j : Fin d => (⟨g (Sum.inr j), gmem _⟩ : N)) := by
        apply LinearIndependent.of_comp N.subtype
        change LinearIndependent R (fun j : Fin d => e • (Pi.single j (1 : R) : Fin d → R))
        rw [Fintype.linearIndependent_iff]
        intro c hc i
        have := congrFun hc i
        simp [Finset.sum_apply, Pi.single_apply] at this
        exact (this.resolve_right he)
      have h1 := hli.fintype_card_le_finrank
      rw [Module.finrank_eq_card_basis bN] at h1
      simpa using h1
  subst hk
  have hc : ∀ j, ∃ c : Fin m ⊕ Fin k → R, ∑ s, c s • g s = (bN j : Fin k → R) :=
    fun j => (Submodule.mem_span_range_iff_exists_fun R).1 (bN j).2
  choose c hc using hc
  have hr : ∀ s (i : Fin k), g s i = ∑ j, bN.repr ⟨g s, gmem s⟩ j * (bN j : Fin k → R) i := by
    intro s i
    have h := congrArg (fun x : N => (x : Fin k → R) i) (bN.sum_repr ⟨g s, gmem s⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h.symm
  refine ⟨Matrix.of fun i j => (bN j : Fin k → R) i, Matrix.of fun j i => bN.repr ⟨g (Sum.inr i), gmem _⟩ j,
    Matrix.of fun i j => c j (Sum.inr i), Matrix.of fun i j => c j (Sum.inl i),
    Matrix.of fun j i => bN.repr ⟨g (Sum.inl i), gmem _⟩ j, ?_, ?_, ?_⟩
  · ext i j
    have h := congrFun (hc j) i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_sum_type, g, Sum.elim_inl,
      Sum.elim_inr, Pi.single_apply] at h
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, ← h]
    simp [mul_comm]
  · ext i i'
    simp only [Matrix.of_apply, Matrix.mul_apply]
    rw [show Y i i' = g (Sum.inl i') i from rfl, hr]
    simp [mul_comm]
  · ext i i'
    simp only [Matrix.of_apply, Matrix.mul_apply]
    have h := hr (Sum.inr i') i
    simp only [g, Sum.elim_inr, Pi.smul_apply, Pi.single_apply, smul_eq_mul] at h
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    rw [h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end GlobalTheory.BSP.LocalizedLatticeBasis

namespace GlobalTheory.BSP.LocalizedLatticeBasis

theorem matMapSmul {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) {α β : Type} (s : S) (M : Matrix α β S) :
    (s • M).map f = f s • M.map f := by
  ext i j; simp


open Matrix in
theorem exists_lattice_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d m n : ℕ)
    (Y : Matrix (Fin d) (Fin m) (bk.S)), ∃ (c : ℕ) (X X' R : Matrix (Fin d) (Fin d) (bk.S))
    (Q : Matrix (Fin m) (Fin d) (bk.S)) (Q' : Matrix (Fin d) (Fin m) (bk.S)),
    X * X' = ((l : bk.S) ^ c * bk.E ^ n) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ X = Y * Q + bk.E ^ n • R ∧
      (l : bk.S) ^ c • Y = X * Q' := by
  intro l _ K bk d m n Y
  haveI := isDomain_loc bk
  haveI := _root_.GlobalTheory.BSP.isPrincipalIdealRing_away_l l K bk
  set φ := algebraMap bk.S (Localization.Away (l : bk.S)) with hφ
  have hE : φ (bk.E ^ n) ≠ 0 := by
    rw [map_ne_zero_iff _ (inj_loc bk)]; exact pow_ne_zero _ bk.E_ne_zero
  obtain ⟨Xb, X'b, Rb, Qb, Q'b, h1, h2, h3⟩ := pid_basis d m (Y.map φ) (φ (bk.E ^ n)) hE
  obtain ⟨k1, c1⟩ := clear bk Qb
  obtain ⟨k2, c2⟩ := clear bk Rb
  obtain ⟨k3, c3⟩ := clear bk Q'b
  obtain ⟨k4, c4⟩ := clear bk X'b
  obtain ⟨Q0, hQ0⟩ := c1 (k1 + k2 + k3 + k4) (by omega)
  obtain ⟨R0, hR0⟩ := c2 (k1 + k2 + k3 + k4) (by omega)
  obtain ⟨Q'0, hQ'0⟩ := c3 (k1 + k2 + k3 + k4) (by omega)
  obtain ⟨X'0, hX'0⟩ := c4 (k1 + k2 + k3 + k4) (by omega)
  rw [← hφ] at hQ0 hR0 hQ'0 hX'0
  set c0 := k1 + k2 + k3 + k4
  have hinj : Function.Injective fun M : Matrix (Fin d) (Fin d) bk.S => M.map φ := Matrix.map_injective (inj_loc bk)
  have hinj' : Function.Injective fun M : Matrix (Fin d) (Fin m) bk.S => M.map φ := Matrix.map_injective (inj_loc bk)
  have hX : (Y * Q0 + bk.E ^ n • R0).map φ = φ (l : bk.S) ^ c0 • Xb := by
    rw [Matrix.map_add φ (map_add φ), Matrix.map_mul, matMapSmul, hQ0, hR0, h1, smul_add, Matrix.mul_smul, smul_comm]
  refine ⟨2 * c0, Y * Q0 + bk.E ^ n • R0, X'0, R0, Q0, Q'0, ?_, rfl, ?_⟩
  · apply hinj
    simp only
    rw [Matrix.map_mul, hX, hX'0, Matrix.smul_mul, Matrix.mul_smul, h3, matMapSmul, Matrix.map_one _ (map_zero φ) (map_one φ),
      smul_smul, smul_smul]
    congr 1
    simp only [map_mul, map_pow]
    ring
  · apply hinj'
    simp only
    rw [Matrix.map_mul, hX, hQ'0, Matrix.smul_mul, Matrix.mul_smul, ← h2, matMapSmul, smul_smul, map_pow, two_mul, pow_add]

end GlobalTheory.BSP.LocalizedLatticeBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureLocalization
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem W2.isUnit_of_fst_gh {l : ℕ} [Fact l.Prime] {L : Type} [CommRing L] (x : W2 l L) (h0 : IsUnit x.fst)
    (h1 : IsUnit (W2.gh x)) : IsUnit x := by
  obtain ⟨u, hu⟩ := h0
  obtain ⟨v, hv⟩ := h1
  refine isUnit_iff_exists_inv.2 ⟨⟨(↑u⁻¹ : L), -(↑u⁻¹ : L) ^ l * x.snd * ↑v⁻¹⟩, ?_⟩
  refine W2.ext ?_ ?_
  · change x.fst * (↑u⁻¹ : L) = 1
    rw [← hu]; simp
  · change x.fst ^ l * (-(↑u⁻¹ : L) ^ l * x.snd * ↑v⁻¹) + (↑u⁻¹ : L) ^ l * x.snd +
      (l : L) * x.snd * (-(↑u⁻¹ : L) ^ l * x.snd * ↑v⁻¹) = 0
    have hg : (↑v⁻¹ : L) * (x.fst ^ l + (l : L) * x.snd) = 1 := by
      change (↑v⁻¹ : L) * W2.gh x = 1
      rw [← hv]; simp
    linear_combination (-(↑u⁻¹ : L) ^ l * x.snd) * hg

theorem delta_localization (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A)
    (M : Submonoid A) (hM : ∀ x ∈ M, D.φ x ∈ M) :
    ∃ D' : Delta l (Localization M), IsδMap D D' (algebraMap A (Localization M)) := by
  let s0 : A →+* W2 l (Localization M) := (W2.map (algebraMap A (Localization M))).comp (deltaSectionToWittLengthTwo D)
  have hs0 : ∀ m : M, IsUnit (s0 m) := fun m => by
    apply W2.isUnit_of_fst_gh
    · exact IsLocalization.map_units (Localization M) m
    · have : W2.gh (s0 m) = algebraMap A (Localization M) (D.φ m) := by
        rw [D.φ_eq]; change (algebraMap A _ m) ^ l + (l : Localization M) * algebraMap A _ (D.δ m) = _
        simp
      rw [this]
      exact IsLocalization.map_units (Localization M) (⟨D.φ m, hM m m.2⟩ : M)
  let s : Localization M →+* W2 l (Localization M) := IsLocalization.lift hs0
  have hsa : ∀ a : A, s (algebraMap A _ a) = s0 a := fun a => IsLocalization.lift_eq hs0 a
  have hsec : ∀ y, (s y).fst = y := fun y => by
    have : (W2.fstHom.comp s : Localization M →+* Localization M) = RingHom.id _ :=
      IsLocalization.ringHom_ext M (RingHom.ext fun a => by
        simp only [RingHom.comp_apply, RingHom.id_apply]
        rw [hsa]; rfl)
    exact RingHom.congr_fun this y
  refine ⟨deltaStructureOfWittLengthTwoSection s hsec, fun a => ?_⟩
  change algebraMap A _ (D.δ a) = (s (algebraMap A _ a)).snd
  rw [hsa]; rfl

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDvdBound
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.BetaBd

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem θ_σA_ev (bk : BK K) (g : ↥(GK K)) (s : bk.S) :
    Per.θ l (Per.σA (g : GQ l) (bk.ev s)) = Per.θ l (bk.ev s) := by
  obtain ⟨r, hr⟩ := bk.str.surjective (Ideal.Quotient.mk _ s)
  rw [GlobalTheory.RingBasics.θ_σA, bk.θ_ev r s hr.symm]
  apply Subtype.ext
  rw [GlobalTheory.RingIface.sigO_coe]
  change Per.σC (g : GQ l) (((r : ↥K.1) : Om l) : ℂ_[l]) = (((r : ↥K.1) : Om l) : ℂ_[l])
  rw [GlobalTheory.RingBasics.σC_coe, (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (r : ↥K.1).2]

theorem dvd_σA_ev_sub (bk : BK K) (g : ↥(GK K)) (s : bk.S) :
    bk.ev bk.E ∣ Per.σA (g : GQ l) (bk.ev s) - bk.ev s := by
  rw [← Ideal.mem_span_singleton, bk.span_ev, RingHom.mem_ker, map_sub, θ_σA_ev, sub_self]

theorem exists_dvd_bound (u : OC l) (hu : u ≠ 0) : ∃ a : ℕ, ∀ (x y : OC l) (n : ℕ),
    x * u = (l : OC l) ^ n * y → a ≤ n → ∃ y' : OC l, x = (l : OC l) ^ (n - a) * y' := by
  have hu' : 0 < ‖(u : ℂ_[l])‖ := norm_pos_iff.2 (fun h => hu (Subtype.ext h))
  obtain ⟨a, ha⟩ : ∃ a : ℕ, ‖(l : ℂ_[l])‖ ^ a < ‖(u : ℂ_[l])‖ :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) GlobalTheory.RingBasics.norm_p_lt).eventually
      (gt_mem_nhds hu')).exists
  refine ⟨a, fun x y n h han => ?_⟩
  have hl0 : 0 < ‖(l : ℂ_[l])‖ := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  have hy : ‖(y : ℂ_[l])‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 y.2
  have h1 : ‖(x : ℂ_[l])‖ * ‖(u : ℂ_[l])‖ = ‖(l : ℂ_[l])‖ ^ n * ‖(y : ℂ_[l])‖ := by
    have := congrArg (fun t : OC l => ‖(t : ℂ_[l])‖) h
    simpa [norm_mul, norm_pow] using this
  have hn : ‖(l : ℂ_[l])‖ ^ n = ‖(l : ℂ_[l])‖ ^ (n - a) * ‖(l : ℂ_[l])‖ ^ a := by
    rw [← pow_add, Nat.sub_add_cancel han]
  have hx : ‖(x : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ ^ (n - a) := by
    have hpa : 0 < ‖(l : ℂ_[l])‖ ^ a := pow_pos hl0 a
    have hpn : 0 ≤ ‖(l : ℂ_[l])‖ ^ (n - a) := pow_nonneg hl0.le _
    by_contra hc
    push_neg at hc
    have : ‖(l : ℂ_[l])‖ ^ (n - a) * ‖(l : ℂ_[l])‖ ^ a < ‖(x : ℂ_[l])‖ * ‖(u : ℂ_[l])‖ :=
      mul_lt_mul'' hc ha hpn hpa.le
    have h2 : ‖(l : ℂ_[l])‖ ^ n * ‖(y : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ ^ n := mul_le_of_le_one_right (pow_nonneg hl0.le n) hy
    linarith
  have hm := (GlobalTheory.RingBasics.mem_span_pow_OC (n - a) x).2 hx
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hm
  obtain ⟨b, hb⟩ := hm
  exact ⟨b, by rw [← hb, mul_comm]⟩

end GlobalTheory.BKLim.BetaBd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetPrimePowTorsionQuotient
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.GoodCoeff

theorem exists_finset_pow_torsion : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ k : ℕ, ∃ Es : Finset (LL ⧸ LinearMap.range (Algebra.linearMap O LL)), ∀ e, ((l : ℕ) : O) ^ k • e = 0 → e ∈ Es := by
  intro l _ LL _ _ _ O _ _ hG k
  classical
  haveI hfin : Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ k}) :=
    (good_coeff_integers l LL O hG).2.2.1 k
  have hl : (l : LL) ≠ 0 := by
    have := (algebraMap ℚ_[l] LL).injective.ne
      (show (l : ℚ_[l]) ≠ 0 from Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
    simpa using this
  have hlk : (l : LL) ^ k ≠ 0 := pow_ne_zero _ hl
  let f : O ⧸ Ideal.span {((l : ℕ) : O) ^ k} → LL ⧸ LinearMap.range (Algebra.linearMap O LL) :=
    fun q => Submodule.Quotient.mk (((l : LL) ^ k)⁻¹ * algebraMap O LL q.out)
  refine ⟨(Set.finite_range f).toFinset, fun e he => ?_⟩
  rw [Set.Finite.mem_toFinset]
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ e
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at he
  obtain ⟨a, ha⟩ := he
  rw [Algebra.linearMap_apply, Algebra.smul_def, map_pow, map_natCast] at ha
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  have h1 : (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : O) ^ k}) a).out - a ∈
      Ideal.span {((l : ℕ) : O) ^ k} :=
    Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out _)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
  have hc' := congrArg (algebraMap O LL) hc
  rw [map_mul, map_pow, map_natCast, RingHom.map_sub, ha] at hc'
  refine (Submodule.Quotient.eq _).2 ⟨c, ?_⟩
  rw [Algebra.linearMap_apply]
  field_simp
  linear_combination hc'

end GlobalTheory.GoodCoeff
end

