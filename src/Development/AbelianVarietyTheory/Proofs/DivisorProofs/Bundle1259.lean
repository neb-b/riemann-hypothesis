module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingMapDetFiltrationWithSymbols
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.FiltDet

theorem alt_linComb {E A' : Type} [Field E] [AddCommGroup A'] [Module E A'] {d : ℕ}
    (ω : A' [⋀^Fin d]→ₗ[E] E) (z : Fin d → A') (N : Fin d → Fin d → E) :
    ω (fun j => Fintype.linearCombination E z (N j)) = (Matrix.of N).det * ω z := by
  classical
  have h := AlternatingMap.eq_smul_basis_det (Pi.basisFun E (Fin d))
    (ω.compLinearMap (Fintype.linearCombination E z))
  have e1 : (fun i => Fintype.linearCombination E z (Pi.basisFun E (Fin d) i)) = z := by
    funext i; simp [Fintype.linearCombination_apply_single]
  have h2 : ω (fun j => Fintype.linearCombination E z (N j)) =
      (ω.compLinearMap (Fintype.linearCombination E z)) N := rfl
  rw [h2, h, AlternatingMap.smul_apply, Pi.basisFun_det,
    AlternatingMap.compLinearMap_apply, e1, smul_eq_mul, mul_comm]
  rfl

theorem det_filtration_symbols : ∀ (E A' : Type) [Field E] [AddCommGroup A'] [Module E A'] (r d : ℕ) (I : Fin r → Type) [∀ a, Fintype (I a)] [∀ a, DecidableEq (I a)] (U : ℕ → Submodule E A') (sym : ∀ a : Fin r, U a →ₗ[E] (I a → E)), (∀ a < r, U (a + 1) ≤ U a) → (∀ (a : Fin r) (x : U a), sym a x = 0 ↔ x.1 ∈ U (a + 1)) → ∀ (ix : (Σ a, I a) ↪ Fin d) (J : Finset (Fin d)) (v : Fin d → A') (hv : ∀ q, v (ix q) ∈ U q.1), (∀ k ∈ J, k ∉ Set.range ix ∧ v k ∈ U r) → ∀ [FiniteDimensional E (U r)], Module.finrank E (U r) ≤ J.card → ∀ (z : Fin d → A') (hz : ∀ q, z (ix q) ∈ U q.1), (∀ q, sym q.1 ⟨z (ix q), hz q⟩ = Pi.single q.2 1) → (∀ k, k ∉ Set.range ix → z k = v k) → ∀ ω : A' [⋀^Fin d]→ₗ[E] E, ω v = (∏ a, (Matrix.of fun i i' : I a => sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i).det) * ω z := by
  intro E A' _ _ _ r d I _ _ U sym hdec hsym ix J v hv hJ _ hcard z hz hzs hzv ω
  classical

  have step : ∀ (a : Fin r) (x : A') (hx : x ∈ U a),
      x - ∑ i, sym a ⟨x, hx⟩ i • z (ix ⟨a, i⟩) ∈ U (a + 1) := by
    intro a x hx
    have hzs' : ∀ i, sym a ⟨z (ix ⟨a, i⟩), hz ⟨a, i⟩⟩ = Pi.single i 1 := fun i => hzs ⟨a, i⟩
    have hmem : ∑ i, sym a ⟨x, hx⟩ i • z (ix ⟨a, i⟩) ∈ U a :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hz ⟨a, i⟩)
    have hy : x - ∑ i, sym a ⟨x, hx⟩ i • z (ix ⟨a, i⟩) ∈ U a := Submodule.sub_mem _ hx hmem
    refine (hsym a ⟨_, hy⟩).1 ?_
    have : (⟨_, hy⟩ : U a) = ⟨x, hx⟩ - ∑ i, sym a ⟨x, hx⟩ i • ⟨z (ix ⟨a, i⟩), hz ⟨a, i⟩⟩ := by
      ext; simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sub, map_sum]
    simp only [map_smul, hzs']
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  obtain ⟨β, hβix, hβout⟩ : ∃ β : Fin d → ℕ, (∀ q, β (ix q) = q.1) ∧
      (∀ k, k ∉ Set.range ix → β k = r) := by
    refine ⟨fun k => if h : k ∈ Set.range ix then ((Classical.choose h).1 : ℕ) else r, ?_, ?_⟩
    · intro q
      have h : ix q ∈ Set.range ix := ⟨q, rfl⟩
      simp only [dif_pos h]
      rw [ix.injective (Classical.choose_spec h)]
    · intro k hk; simp only [dif_neg hk]
  have hβle : ∀ k, β k ≤ r := by
    intro k
    by_cases hk : k ∈ Set.range ix
    · obtain ⟨q, rfl⟩ := hk; rw [hβix]; exact q.1.isLt.le
    · rw [hβout k hk]
  have conv : ∀ (S : Set (Fin d)) (x : A'), x ∈ Submodule.span E (z '' S) →
      ∃ c : Fin d → E, (∀ k ∉ S, c k = 0) ∧ Fintype.linearCombination E z c = x := by
    intro S x hx
    obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination E).1 hx
    refine ⟨l, fun k hk => (Finsupp.mem_supported' E l).1 hl k hk, ?_⟩
    rw [Fintype.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; simp
  by_cases hli : LinearIndependent E (fun k : J => v k)
  swap
  · have h1 : ¬ LinearIndependent E v := fun h => hli (h.comp _ Subtype.val_injective)
    have h2 : ¬ LinearIndependent E z := by
      intro h; apply hli
      have : (fun k : J => v k) = z ∘ Subtype.val := by
        funext k; exact (hzv k.1 (hJ k.1 k.2).1).symm
      rw [this]; exact h.comp _ Subtype.val_injective
    rw [ω.map_linearDependent v h1, ω.map_linearDependent z h2, mul_zero]
  have hspan : U r ≤ Submodule.span E (Set.range fun k : J => v k) := by
    have hle : Submodule.span E (Set.range fun k : J => v k) ≤ U r := by
      rw [Submodule.span_le]; rintro _ ⟨k, rfl⟩; exact (hJ k.1 k.2).2
    refine (Submodule.eq_of_le_of_finrank_le hle ?_).ge
    rw [finrank_span_eq_card hli, Fintype.card_coe]; exact hcard
  have hdown : ∀ n a, a + n = r → U a ≤ Submodule.span E (z '' {k | a ≤ β k}) := by
    intro n
    induction n with
    | zero =>
      intro a ha
      obtain rfl : a = r := by omega
      refine hspan.trans (Submodule.span_mono ?_)
      rintro _ ⟨k, rfl⟩
      refine ⟨k.1, ?_, hzv k.1 (hJ k.1 k.2).1⟩
      simp [hβout k.1 (hJ k.1 k.2).1]
    | succ n ih =>
      intro a ha x hx
      have har : a < r := by omega
      have key := step ⟨a, har⟩ x hx
      have hy := ih (a + 1) (by omega) key
      have hmono : Submodule.span E (z '' {k | a + 1 ≤ β k}) ≤
          Submodule.span E (z '' {k | a ≤ β k}) :=
        Submodule.span_mono (Set.image_mono fun k hk => by
          simp only [Set.mem_setOf_eq] at hk ⊢; omega)
      have hsum : ∑ i, sym ⟨a, har⟩ ⟨x, hx⟩ i • z (ix ⟨⟨a, har⟩, i⟩) ∈
          Submodule.span E (z '' {k | a ≤ β k}) := by
        refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
          (Submodule.subset_span ⟨ix ⟨⟨a, har⟩, i⟩, ?_, rfl⟩)
        simp [hβix]
      have := Submodule.add_mem _ (hmono hy) hsum
      simpa using this
  have hcol : ∀ q : (Σ a, I a), ∃ col : Fin d → E, Fintype.linearCombination E z col = v (ix q) ∧
      (∀ k, β k < q.1 → col k = 0) ∧
      ∀ i, col (ix ⟨q.1, i⟩) = sym q.1 ⟨v (ix q), hv q⟩ i := by
    rintro ⟨a, i'⟩
    have key := step a (v (ix ⟨a, i'⟩)) (hv ⟨a, i'⟩)
    have hy := hdown (r - (a + 1)) (a + 1) (by omega) key
    obtain ⟨c, hc0, hcL⟩ := conv _ _ hy
    refine ⟨c + ∑ i, sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i • Pi.single (ix ⟨a, i⟩) 1, ?_, ?_, ?_⟩
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), map_sum, hcL]
      simp only [map_smul, Fintype.linearCombination_apply_single, one_smul, sub_add_cancel]
    · intro k hk
      have hk' : β k < a := hk
      have h1 : c k = 0 := hc0 k (by simp only [Set.mem_setOf_eq, not_le]; omega)
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, h1, zero_add]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hne : k ≠ ix ⟨a, i⟩ := by
        rintro rfl; rw [hβix] at hk'; exact lt_irrefl _ hk'
      simp [Pi.single_apply, hne]
    · intro i
      have h1 : c (ix ⟨a, i⟩) = 0 := hc0 _ (by simp [hβix])
      simp [h1, Finset.sum_apply, Pi.single_apply, Sigma.mk.inj_iff]
  choose col hcolL hcol0 hcoldiag using hcol
  obtain ⟨N, hNix, hNout⟩ : ∃ N : Matrix (Fin d) (Fin d) E, (∀ q, N (ix q) = col q) ∧
      (∀ k, k ∉ Set.range ix → N k = Pi.single k 1) := by
    refine ⟨Matrix.of fun k => if h : k ∈ Set.range ix then col (Classical.choose (Set.mem_range.1 h))
      else Pi.single k 1, ?_, ?_⟩
    · intro q
      have h : ix q ∈ Set.range ix := ⟨q, rfl⟩
      funext j
      simp only [Matrix.of_apply, dif_pos h]
      rw [ix.injective (Classical.choose_spec (Set.mem_range.1 h))]
    · intro k hk; funext j; simp only [Matrix.of_apply, dif_neg hk]
  have hNL : ∀ j, Fintype.linearCombination E z (N j) = v j := by
    intro j
    by_cases hj : j ∈ Set.range ix
    · obtain ⟨q, rfl⟩ := hj; rw [hNix]; exact hcolL q
    · rw [hNout j hj, Fintype.linearCombination_apply_single, one_smul]; exact hzv j hj
  have hBT : N.BlockTriangular β := by
    intro i j hij
    by_cases hi : i ∈ Set.range ix
    · obtain ⟨q, rfl⟩ := hi; rw [hNix]; exact hcol0 q j (by rw [hβix] at hij; exact hij)
    · rw [hNout i hi, Pi.single_apply, if_neg]; rintro rfl; exact lt_irrefl _ hij
  have hdet : N.det = ∏ a : Fin r,
      (Matrix.of fun i i' : I a => sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i).det := by
    rw [hBT.det]
    have himg : Finset.image β Finset.univ ⊆ Finset.range (r + 1) := by
      intro b hb
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hb
      simp only [Finset.mem_range]; have := hβle k; omega
    rw [Finset.prod_subset himg ?_]
    · rw [Finset.prod_range_succ]
      have hlast : (N.toSquareBlock β r).det = 1 := by
        have : N.toSquareBlock β r = 1 := by
          ext ⟨i, hi⟩ ⟨j, hj⟩
          have hi' : i ∉ Set.range ix := by
            rintro ⟨q, rfl⟩; rw [hβix] at hi; have := q.1.isLt; omega
          rw [Matrix.toSquareBlock_def, Matrix.of_apply, hNout i hi', Pi.single_apply,
            Matrix.one_apply]
          simp only [Subtype.mk.injEq, eq_comm]
        rw [this, Matrix.det_one]
      rw [hlast, mul_one, ← Fin.prod_univ_eq_prod_range (fun x => (N.toSquareBlock β x).det) r]
      refine Finset.prod_congr rfl fun a _ => ?_
      have hinj : Function.Injective
          (fun i : I a => (⟨ix ⟨a, i⟩, hβix _⟩ : {k // β k = (a : ℕ)})) := by
        intro i i' h
        simp only [Subtype.mk.injEq, ix.apply_eq_iff_eq, Sigma.mk.inj_iff, heq_eq_eq,
          true_and] at h
        exact h
      have hsurj : Function.Surjective
          (fun i : I a => (⟨ix ⟨a, i⟩, hβix _⟩ : {k // β k = (a : ℕ)})) := by
        rintro ⟨k, hk⟩
        by_cases hkr : k ∈ Set.range ix
        · obtain ⟨⟨b, i⟩, rfl⟩ := hkr
          rw [hβix] at hk
          have hab : b = a := Fin.ext hk
          subst hab
          exact ⟨i, rfl⟩
        · rw [hβout k hkr] at hk; have := a.isLt; omega
      let e := Equiv.ofBijective _ ⟨hinj, hsurj⟩
      show (N.toSquareBlock β a).det = _
      rw [← Matrix.det_submatrix_equiv_self e, ← Matrix.det_transpose]
      congr 1
      ext i i'
      show N (ix ⟨a, i'⟩) (ix ⟨a, i⟩) = _
      rw [hNix]
      exact hcoldiag ⟨a, i'⟩ i
    · intro b _ hb
      haveI : IsEmpty {i // β i = b} :=
        ⟨fun ⟨i, hi⟩ => hb (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩)⟩
      exact Matrix.det_isEmpty
  have hv' : v = fun j => Fintype.linearCombination E z (N j) := funext fun j => (hNL j).symm
  rw [show ω v = ω (fun j => Fintype.linearCombination E z (N j)) from congrArg _ hv']
  refine (alt_linComb ω z N).trans ?_
  rw [← hdet]
  rfl

end GlobalTheory.FiltDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanIwasawaMajorantFrame
section
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

namespace GlobalTheory.IwArchLine

theorem form_map_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {m k l : Type} [Fintype m] (M : Matrix m k E) (J : Matrix m m E) (N : Matrix m l E) :
    cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) (M.map (inclR (F := F) R)) * J.map (inclR (F := F) R) * N.map (inclR (F := F) R) =
      (cT (σ : E →+* E) M * J * N).map (inclR (F := F) R) := by
  have h1 : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) (M.map (inclR (F := F) R)) = (cT (σ : E →+* E) M).map (inclR (F := F) R) := by
    ext i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
    rfl
  rw [h1, Matrix.map_mul, Matrix.map_mul]

theorem exists_q_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x y : Matrix (Fin n) (Fin 1) E), cT (σ : E →+* E) x * J * x = 0 → cT (σ : E →+* E) y * J * x = 1 → ∀ (a : GL (Fin n) (AF F ⊗[F] E)), IsMajorantFrame σ J a → ∀ (w : InfinitePlace F) (g : GArch σ J w), ∃ q k : GArch σ J w, k ∈ stabArch σ J w (bc (compInf F E w) a) ∧ g = q * k ∧ ∃ β : GL (Fin 1) (w.Completion ⊗[F] E), (matHom _ σ J q).1 * x.map (inclR (F := F) w.Completion) = x.map (inclR (F := F) w.Completion) * β.1 := by
  intro F E _ _ _ _ _ σ hcm n J _ x y hx hxy a ha w g
  obtain ⟨τ⟩ : Nonempty (GlobalTheory.AdelicU.EmbOver E w) := inferInstance
  obtain ⟨ε, hε⟩ := ha w
  have hXiso := form_map_inclR (F := F) w.Completion σ x J x
  rw [hx, Matrix.map_zero _ (map_zero _)] at hXiso
  obtain ⟨K, hK, hK1, β, hβ⟩ := GlobalTheory.Core.Rk.IwArch.iw_iso_cols (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ)
    (GlobalTheory.AdelicU.infEmb τ) (GlobalTheory.AdelicU.infEmb_bijective hcm τ) (fun z => (GlobalTheory.AdelicU.infEmb_sigR hcm τ z).symm)
    (bc (compInf F E w) a) ε hε _ hXiso (GlobalTheory.AdelicU.matHom w.Completion σ J g) g.2
  let kk : GArch σ J w := ⟨K, hK⟩
  have hPX := form_map_inclR (F := F) w.Completion σ y J x
  rw [hxy, Matrix.map_one _ (map_zero _) (map_one _)] at hPX
  set X := x.map (inclR (F := F) w.Completion) with hXdef
  set P := cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (y.map (inclR (F := F) w.Completion)) *
    J.map (inclR (F := F) w.Completion) with hPdef
  set Q : GL (Fin n) (w.Completion ⊗[F] E) := GlobalTheory.AdelicU.matHom w.Completion σ J g * K⁻¹ with hQ
  have hQX : Q.1 * X = X * β := hβ
  have hX' : X = (Q⁻¹).1 * X * β := by
    rw [Matrix.mul_assoc, ← hQX, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have hleft : (P * (Q⁻¹).1 * X) * β = 1 := by
    rw [← hPX]; conv_rhs => rw [hX']
    simp only [Matrix.mul_assoc]
  let βu : GL (Fin 1) (w.Completion ⊗[F] E) := ⟨β, P * (Q⁻¹).1 * X, mul_eq_one_comm.1 hleft, hleft⟩
  refine ⟨g * kk⁻¹, kk, GlobalTheory.AdelicU.mem_stabArch.2 hK1, by group, βu, ?_⟩
  have : (GlobalTheory.AdelicU.matHom w.Completion σ J (g * kk⁻¹)) = Q := by
    rw [map_mul, map_inv]; rfl
  rw [this]; exact hQX

end GlobalTheory.IwArchLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanNormSquareExists
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Matrix

namespace GlobalTheory.FlatDegreeCompare.ArchExists

theorem linearIndependent_of_indep {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A] {L : LB A.left} {g n : ℕ}
    (u : HolUnif A L g) (hu : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) {v : Fin n → (epsR ℂ ⟶ A)} (hv : Indep v)
    {W : Fin n → Fin g → ℂ} (hW : ∀ i, u.IsDiff (W i) (v i)) : LinearIndependent ℂ W := by
  have key : ∀ c : Fin n → ℂ, ∃ w, IsTangent w ∧ IsLieComb c v w ∧ u.IsDiff (∑ i, c i • W i) w := fun c => by
    have h := UnifDifferential.isDiff_prod u (fun i => c i • W i) _
      (fun i => Chart.isTan_scale (c i) ((Chart.isTan_iff _).2 (hv.1 i)))
      (fun i => UnifDifferential.isDiff_scale u (hW i) (c i))
    exact ⟨_, (Chart.isTan_iff _).1 h.1, (Chart.isLieComb_iff c v _).2 rfl, h.2⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  obtain ⟨w, h1, h2, h3⟩ := key c
  obtain ⟨w', h1', h2', h3'⟩ := key 0
  rw [hc] at h3
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at h3'
  obtain rfl := (hu 0).unique ⟨h1, h3⟩ ⟨h1', h3'⟩
  exact congrFun (hv.2 _ _ w h2 h2')

end GlobalTheory.FlatDegreeCompare.ArchExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisDetIntegralSpanEqOne
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

theorem basis_det_integral_span_eq_one : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (d : ℕ) (β : Module.Basis (Fin d) F V), Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ Submodule.span (𝓞 F) (Set.range β)) ∧ y = β.det w} = 1 := by
  intro F V _ _ _ _ _ _ d β
  have key : ∀ v ∈ Submodule.span (𝓞 F) (Set.range β), ∀ i, ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = β.repr v i := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i
      refine ⟨if j = i then 1 else 0, ?_⟩
      rw [Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs <;> simp
    | zero => intro i; exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro i
      obtain ⟨a, ha⟩ := hx i
      obtain ⟨b, hb⟩ := hy i
      exact ⟨a + b, by simp [ha, hb]⟩
    | smul r x _ hx =>
      intro i
      obtain ⟨a, ha⟩ := hx i
      refine ⟨r * a, ?_⟩
      rw [← algebraMap_smul F r x, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, ha]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨w, hw, rfl⟩
    choose a ha using fun i => key (w i) (hw i)
    rw [SetLike.mem_coe, Submodule.mem_one, Module.Basis.det_apply]
    have hm : β.toMatrix w = (Matrix.of fun j i => a i j).map (algebraMap (𝓞 F) F) := by
      ext j i
      simp [Module.Basis.toMatrix_apply, ha]
    rw [hm]
    exact ⟨(Matrix.of fun j i => a i j).det, by rw [RingHom.map_det]; rfl⟩
  · rw [Submodule.one_le]
    exact Submodule.subset_span ⟨β, fun i => Submodule.subset_span ⟨i, rfl⟩, (β.det_self).symm⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnipotentConjConeDiagonalBound
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem unip_mul_diag_cone : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (t : ℝ), 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → r j / r i ≤ C ∧ ∀ z : BlockIx a j → Cinf E, ∃ z' : BlockIx a j → Cinf E, ‖z'‖ ≤ C * (r j / r i) * ‖z‖ ∧ ∀ τ : ℝ, unip (τ • z) * d = d * unip (τ • z') := by
  intro E _ _ _ a t ht i j hij
  obtain ⟨C0, hC0, hb⟩ := GlobalTheory.T.cone_coordinate_ratio_bounded a t ht
  refine ⟨C0 * C0 + C0, by positivity, ?_⟩
  intro r d hr hcone hd
  have hij' : i ≤ j := by rw [Fin.le_def]; omega
  have hji : r j / r i ≤ C0 := hb r hr hcone i j hij'
  have hji0 : 0 ≤ r j / r i := (div_pos (hr j) (hr i)).le
  refine ⟨by nlinarith, fun z => ?_⟩
  refine ⟨fun p => (r p.1.2 / r p.1.1) • z p, ?_, ?_⟩
  · have hX : 0 ≤ (C0 * C0 + C0) * (r j / r i) := by positivity
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun p => ?_
    have hk : p.1.1 ≤ i := by rw [Fin.le_def]; have := p.2.1; omega
    have hl : j ≤ p.1.2 := by rw [Fin.le_def]; exact p.2.2
    have h1 : r p.1.2 / r j ≤ C0 := hb r hr hcone j p.1.2 hl
    have h3 : r i / r p.1.1 ≤ C0 := hb r hr hcone p.1.1 i hk
    have hpos : 0 < r p.1.2 / r p.1.1 := div_pos (hr _) (hr _)
    have heq : r p.1.2 / r p.1.1 = (r p.1.2 / r j) * (r j / r i) * (r i / r p.1.1) := by
      have := hr j; have := hr i; have := hr p.1.1
      field_simp
    have hbd : r p.1.2 / r p.1.1 ≤ (C0 * C0 + C0) * (r j / r i) := by
      rw [heq]
      have e1 : 0 ≤ r p.1.2 / r j := (div_pos (hr _) (hr _)).le
      have e3 : 0 ≤ r i / r p.1.1 := (div_pos (hr _) (hr _)).le
      calc r p.1.2 / r j * (r j / r i) * (r i / r p.1.1) ≤ C0 * (r j / r i) * C0 := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right h1 hji0) h3 e3 (by positivity)
        _ ≤ (C0 * C0 + C0) * (r j / r i) := by nlinarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    exact mul_le_mul hbd (norm_le_pi_norm z p) (norm_nonneg _) hX
  · intro τ
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hd]
    change (1 + nilM (τ • z)) * _ = _ * (1 + nilM (τ • fun p => (r p.1.2 / r p.1.1) • z p))
    ext k l w
    rw [add_mul, mul_add, one_mul, mul_one, Matrix.add_apply, Matrix.add_apply, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    congr 1
    simp only [nilM, Matrix.of_apply]
    split_ifs with h
    · simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul, add_right_inj]
      have := hr k
      have hk0 : (r k : ℂ) ≠ 0 := by exact_mod_cast this.ne'
      push_cast
      field_simp
    · simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CayleyTransformMemUnitaryLatticeStabilizer
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.CayleyStab

theorem cayley_mem_KAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl (F := F)) (Y : Matrix (Fin d) (Fin d) (AE F E)), At (evFin F v) Y →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 →
    (∃ M : Matrix (Fin d) (Fin d) (AE F E), (1 + Y) * M = 1 ∧ M * (1 + Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    (∃ M : Matrix (Fin d) (Fin d) (AE F E), (1 - Y) * M = 1 ∧ M * (1 - Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ h ∈ GlobalTheory.InertSph.KAt σ W v, mat h * (1 + Y) = 1 - Y := by
  intro F E _ _ _ _ _ σ d W v Y hY hYL hskew ⟨Np, hP1, hP2, hPL⟩ ⟨Nm, hM1, hM2, hML⟩
  set J := incM F W.J with hJ
  have hmap : ∀ A B : Matrix (Fin d) (Fin d) (AE F E), (A * B).map (cA σ) = A.map (cA σ) * B.map (cA σ) :=
    fun A B => Matrix.map_mul (f := (cA σ).toRingHom)
  have hmap1 : (1 : Matrix (Fin d) (Fin d) (AE F E)).map (cA σ) = 1 :=
    Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))
  have hGP : (1 - Y) * Np * (1 + Y) = 1 - Y := by rw [Matrix.mul_assoc, hP2, Matrix.mul_one]
  have h1 : (1 - Y) * Np * ((1 + Y) * Nm) = 1 := by
    rw [← Matrix.mul_assoc, hGP, hM1]
  have h2 : (1 + Y) * Nm * ((1 - Y) * Np) = 1 := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc (1 + Y), hM2, Matrix.mul_one, hP1]

  have hQP : (1 - Y)ᵀ * J * (1 - Y).map (cA σ) = (1 + Y)ᵀ * J * (1 + Y).map (cA σ) := by
    rw [Matrix.map_sub _ (map_sub (cA σ)), Matrix.map_add _ (map_add (cA σ)), hmap1, Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one]
    have e : ∀ A B : Matrix (Fin d) (Fin d) (AE F E), (1 - A) * J * (1 - B) = (1 + A) * J * (1 + B) - 2 * (A * J + J * B) := by
      intro A B; noncomm_ring
    rw [e, hskew, mul_zero, sub_zero]
  have hU : ((1 - Y) * Np)ᵀ * J * ((1 - Y) * Np).map (cA σ) = J := by
    have eT : Npᵀ * (1 + Y)ᵀ = 1 := by rw [← Matrix.transpose_mul, hP1, Matrix.transpose_one]
    have eM : (1 + Y).map (cA σ) * Np.map (cA σ) = 1 := by rw [← hmap, hP1, hmap1]
    calc ((1 - Y) * Np)ᵀ * J * ((1 - Y) * Np).map (cA σ)
        = (Npᵀ * (1 + Y)ᵀ) * (((1 - Y) * Np)ᵀ * J * ((1 - Y) * Np).map (cA σ)) * ((1 + Y).map (cA σ) * Np.map (cA σ)) := by
          rw [eT, eM, Matrix.one_mul, Matrix.mul_one]
      _ = Npᵀ * (((1 - Y) * Np * (1 + Y))ᵀ * J * ((1 - Y) * Np * (1 + Y)).map (cA σ)) * Np.map (cA σ) := by
          rw [hmap ((1 - Y) * Np), Matrix.transpose_mul ((1 - Y) * Np)]
          simp only [Matrix.mul_assoc]
      _ = Npᵀ * ((1 + Y)ᵀ * J * (1 + Y).map (cA σ)) * Np.map (cA σ) := by rw [hGP, hQP]
      _ = (Npᵀ * (1 + Y)ᵀ) * J * ((1 + Y).map (cA σ) * Np.map (cA σ)) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [eT, eM, Matrix.one_mul, Matrix.mul_one]
  let g : GL (Fin d) (AE F E) := ⟨(1 - Y) * Np, (1 + Y) * Nm, h1, h2⟩
  have hg : g ∈ UG (cA σ) (incM F W.J) := hU
  let h : UA σ W.J := ⟨g, hg⟩
  have hmat : mat h = (1 - Y) * Np := rfl
  have hmatinv : mat h⁻¹ = (1 + Y) * Nm := rfl
  refine ⟨h, ⟨?_, ?_⟩, ?_⟩
  · intro u hu
    have e : mat h - 1 = -(Y * Np) - Y * Np := by
      rw [hmat]
      calc (1 - Y) * Np - 1 = (1 - Y) * Np - (1 + Y) * Np := by rw [hP1]
        _ = -(Y * Np) - Y * Np := by noncomm_ring
    have hYu : u • Y = 0 := hY u hu
    rw [e, smul_sub, smul_neg, ← Matrix.smul_mul, hYu, Matrix.zero_mul, neg_zero, sub_zero]
  · intro z hz
    refine ⟨?_, ?_⟩
    · rw [hmat, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact sub_mem (hPL z hz) (hYL _ (hPL z hz))
    · rw [hmatinv, ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
      exact add_mem (hML z hz) (hYL _ (hML z hz))
  · rw [hmat, hGP]

end GlobalTheory.CayleyStab
end

