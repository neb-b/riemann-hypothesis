module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import ReciprocityTheory.DualLattices.Bundle0030
public import ReciprocityTheory.DualLattices.UpSmith
public import ReciprocityTheory.DualLattices.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsZpRingHomIntegers
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section
open Polynomial

private theorem zpMap_map_aeval {R' R : Type} [CommRing R'] [CommRing R] (π : R' →+* R)
    (f : ℤ[X]) (x : R') : π (Polynomial.aeval x f) = Polynomial.aeval (π x) f :=
  (Polynomial.aeval_algHom_apply π.toIntAlgHom x f).symm

private theorem zpMap_general {B R : Type} [CommRing B] [CommRing R]
    (f : ℤ[X]) (ζ : B) (S : Submonoid ℕ) (h0 : Polynomial.aeval ζ f = 0)
    (hinj : ∀ g : ℤ[X], Polynomial.aeval ζ g = 0 → f ∣ g)
    (hS : ∀ n ∈ S, IsUnit (n : B))
    (hsurj : ∀ b : B, ∃ n ∈ S, ∃ g : ℤ[X], b * (n : B) = Polynomial.aeval ζ g)
    (hS' : ∀ n ∈ S, IsUnit (n : R)) (z : R) (hz : Polynomial.aeval z f = 0) :
    ∃ β : B →+* R, β ζ = z := by
  let φ : AdjoinRoot f →+* B := AdjoinRoot.lift (algebraMap ℤ B) ζ h0
  let α : AdjoinRoot f →+* R := AdjoinRoot.lift (algebraMap ℤ R) z hz
  have hφ : ∀ g : ℤ[X], φ (AdjoinRoot.mk f g) = Polynomial.aeval ζ g := fun g =>
    AdjoinRoot.lift_mk _ _
  have hα : ∀ g : ℤ[X], α (AdjoinRoot.mk f g) = Polynomial.aeval z g := fun g =>
    AdjoinRoot.lift_mk _ _
  letI : Algebra (AdjoinRoot f) B := φ.toAlgebra
  have halg : algebraMap (AdjoinRoot f) B = φ := rfl
  let S' : Submonoid (AdjoinRoot f) := S.map (Nat.castRingHom (AdjoinRoot f))
  haveI : IsLocalization S' B := by
    refine (isLocalization_iff _ _).mpr ⟨?_, fun b => ?_, fun {a c} h => ⟨1, ?_⟩⟩
    · rintro ⟨_, n, hn, rfl⟩
      simpa using hS n hn
    · obtain ⟨n, hn, g, hg⟩ := hsurj b
      refine ⟨(AdjoinRoot.mk f g, ⟨_, n, hn, rfl⟩), ?_⟩
      simp only [halg, hφ]
      simpa using hg
    · obtain ⟨a, rfl⟩ := AdjoinRoot.mk_surjective a
      obtain ⟨c, rfl⟩ := AdjoinRoot.mk_surjective c
      rw [halg, hφ, hφ, ← sub_eq_zero, ← map_sub] at h
      rw [AdjoinRoot.mk_eq_mk.mpr (hinj _ h)]
  have hu : ∀ y : S', IsUnit (α y) := by
    rintro ⟨_, n, hn, rfl⟩
    simpa using hS' n hn
  refine ⟨IsLocalization.lift hu, ?_⟩
  have h1 : ζ = algebraMap (AdjoinRoot f) B (AdjoinRoot.mk f Polynomial.X) := by
    rw [halg, hφ, Polynomial.aeval_X]
  rw [h1, IsLocalization.lift_eq, hα, Polynomial.aeval_X]

private def zpMap_S (p : ℕ) : Submonoid ℕ where
  carrier := {n | n ≠ 0 ∧ n.Coprime p}
  mul_mem' := fun ha hb => ⟨mul_ne_zero ha.1 hb.1, Nat.Coprime.mul_left ha.2 hb.2⟩
  one_mem' := ⟨one_ne_zero, Nat.coprime_one_left p⟩

private theorem zpMap_isUnit (p M n : ℕ) (hn : n ∈ zpMap_S p) : IsUnit (n : Geo.Tor.ZP p M) := by
  have hmem : (n : ℂ)⁻¹ ∈ Geo.Tor.ZP p M := Subring.subset_closure (Or.inr ⟨n, hn.2, rfl⟩)
  refine IsUnit.of_mul_eq_one (⟨_, hmem⟩ : Geo.Tor.ZP p M) (Subtype.ext ?_)
  have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.1
  simp [this]

private theorem zpMap_surj (p M : ℕ) (x : ℂ) (hx : x ∈ Geo.Tor.ZP p M) :
    ∃ n ∈ zpMap_S p, ∃ g : ℤ[X],
      x * (n : ℂ) = Polynomial.aeval ((Geo.Tor.zetaZP p M : Geo.Tor.ZP p M) : ℂ) g := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with hx | ⟨n, hn, rfl⟩
    · exact ⟨1, one_mem _, Polynomial.X, by simpa [Geo.Tor.zetaZP] using hx⟩
    · by_cases h : n = 0
      · exact ⟨1, one_mem _, 0, by simp [h]⟩
      · have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h
        exact ⟨n, ⟨h, hn⟩, 1, by simp [this]⟩
  | zero => exact ⟨1, one_mem _, 0, by simp⟩
  | one => exact ⟨1, one_mem _, 1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, g, hg⟩ := hx
    obtain ⟨m, hm, k, hk⟩ := hy
    refine ⟨n * m, mul_mem hn hm, g * (m : ℤ[X]) + k * (n : ℤ[X]), ?_⟩
    simp only [map_add (f := _), map_mul, map_natCast, Nat.cast_mul, ← hg, ← hk]
    ring
  | neg x _ hx =>
    obtain ⟨n, hn, g, hg⟩ := hx
    exact ⟨n, hn, -g, by rw [map_neg, ← hg, neg_mul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, g, hg⟩ := hx
    obtain ⟨m, hm, k, hk⟩ := hy
    refine ⟨n * m, mul_mem hn hm, g * k, ?_⟩
    simp only [map_mul, Nat.cast_mul, ← hg, ← hk]
    ring

private theorem zpMap_unit (p : ℕ) (O : Type) [CommRing O]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (n : ℕ) (hn : n.Coprime p) : IsUnit (n : O) := by
  have hp : (p : O) ∈ Ideal.jacobson (⊥ : Ideal O) :=
    IsAdicComplete.le_jacobson_bot (Ideal.span {(p : O)}) (Ideal.subset_span rfl)
  have hc : IsCoprime (n : O) (p : O) := Nat.Coprime.cast hn
  obtain ⟨a, b, hab⟩ := hc
  have hu := Ideal.mem_jacobson_bot.mp hp (-b)
  have : (p : O) * -b + 1 = a * n := by rw [← hab]; ring
  rw [this] at hu
  exact isUnit_of_mul_isUnit_right hu

private theorem zpMap_main (p : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O)
    [IsAdicComplete (Ideal.span {(p : O)}) O] (M : ℕ) (hM : M ≠ 0) (hMp : M.Coprime p) :
    ∃ β : Geo.Tor.ZP p M →+* O, Function.Injective β ∧ IsUnit (M : O) ∧
      ∀ (k : Type) [Field k] (gk : O →+* k), IsPrimitiveRoot (gk (β (Geo.Tor.zetaZP p M))) M := by
  have hpos : 0 < M := Nat.pos_of_ne_zero hM
  haveI : NeZero M := ⟨hM⟩
  have hprim : IsPrimitiveRoot ((Geo.Tor.zetaZP p M : Geo.Tor.ZP p M) : ℂ) M :=
    Complex.isPrimitiveRoot_exp M hM
  have hmin := cyclotomic_eq_minpoly hprim hpos
  have hcoe : ∀ g : ℤ[X], ((Polynomial.aeval (Geo.Tor.zetaZP p M) g : Geo.Tor.ZP p M) : ℂ)
      = Polynomial.aeval ((Geo.Tor.zetaZP p M : Geo.Tor.ZP p M) : ℂ) g :=
    fun g => zpMap_map_aeval (Geo.Tor.ZP p M).subtype g _
  have h0 : Polynomial.aeval (Geo.Tor.zetaZP p M) (cyclotomic M ℤ) = 0 := by
    apply Subtype.ext
    rw [hcoe, hmin]
    exact minpoly.aeval _ _
  obtain ⟨w, hw⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C M
  have hvw : v w ≤ 1 := by
    have h1 : v w ^ M = 1 := by rw [← map_pow, hw.pow_eq_one, map_one]
    exact ((pow_eq_one_iff_of_nonneg zero_le hM).mp h1).le
  obtain ⟨z, rfl⟩ := hv.exists_of_le_one hvw
  have hminw := cyclotomic_eq_minpoly hw hpos
  have hz : Polynomial.aeval z (cyclotomic M ℤ) = 0 := by
    apply hv.hom_inj
    rw [zpMap_map_aeval, map_zero, hminw]
    exact minpoly.aeval _ _
  have hsurj : ∀ b : Geo.Tor.ZP p M, ∃ n ∈ zpMap_S p, ∃ g : ℤ[X],
      b * (n : Geo.Tor.ZP p M) = Polynomial.aeval (Geo.Tor.zetaZP p M) g := by
    intro b
    obtain ⟨n, hn, g, hg⟩ := zpMap_surj p M b b.2
    exact ⟨n, hn, g, Subtype.ext (by rw [hcoe, ← hg]; simp)⟩
  obtain ⟨β, hβ⟩ := zpMap_general (cyclotomic M ℤ) (Geo.Tor.zetaZP p M) (zpMap_S p) h0
    (fun g hg => by
      rw [hmin]
      refine minpoly.isIntegrallyClosed_dvd (hprim.isIntegral hpos) ?_
      rw [← hcoe, hg]
      rfl)
    (zpMap_isUnit p M) hsurj (fun n hn => zpMap_unit p O n hn.2) z hz
  have hMu : IsUnit (M : O) := zpMap_unit p O M hMp
  refine ⟨β, ?_, hMu, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨n, hn, g, hg⟩ := hsurj b
    have h1 : Polynomial.aeval (algebraMap O C z) g = 0 := by
      rw [← zpMap_map_aeval, ← hβ, ← zpMap_map_aeval, ← hg, map_mul, hb, zero_mul, map_zero]
    have h2 : cyclotomic M ℤ ∣ g := by
      rw [hminw]
      exact minpoly.isIntegrallyClosed_dvd (hw.isIntegral hpos) h1
    obtain ⟨q, rfl⟩ := h2
    rw [map_mul, h0, zero_mul] at hg
    exact ((zpMap_isUnit p M n hn).mul_left_eq_zero).mp hg
  · intro k _ gk
    haveI : NeZero (M : k) := ⟨by simpa using (hMu.map gk).ne_zero⟩
    rw [← isRoot_cyclotomic_iff, hβ, IsRoot.def, ← map_cyclotomic_int, ← algebraMap_int_eq,
      eval_map_algebraMap, ← zpMap_map_aeval, hz, map_zero]

end

theorem exists_zp_ringHom_integers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (M : ℕ), M ≠ 0 → M.Coprime p → ∃ β : Geo.Tor.ZP p M →+* O, Function.Injective β ∧ IsUnit (M : O) ∧ ∀ (k : Type) [Field k] (gk : O →+* k), IsPrimitiveRoot (gk (β (Geo.Tor.zetaZP p M))) M := by
  intro p _ C _ _ _ v O _ _ hv _ _ M hM hMp
  exact zpMap_main p C v O hv M hM hMp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasLenExistsMonoFp
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem hasLen_of_fp {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) (M : Type) [AddCommGroup M] [Module O M]
    (h : Module.FinitePresentation O M) : ∃ x, HasLen v O M x := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O M
  have hk : (LinearMap.ker f).FG := Module.FinitePresentation.fg_ker f hf
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hk
  have hsmith : ∀ (b : ℕ) {idx : Type} [Fintype idx] (g : idx → Fin b → O),
      ∃ c : Fin b → O, Nonempty (((Fin b → O) ⧸ Submodule.span O (Set.range g)) ≃ₗ[O]
        ((i : Fin b) → O ⧸ Ideal.span {c i})) := by
    intro b
    induction b with
    | zero =>
      intro idx _ g
      exact ⟨Fin.elim0, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
    | succ b ih =>
      intro idx _ g
      obtain ⟨i0, a, u, s, hu, hau, hs, -, -⟩ := Smith.exists_pivot hv g
      obtain ⟨e1⟩ := Smith.pivot_equiv g i0 a u s hu hau hs
      obtain ⟨c, ⟨e2⟩⟩ := ih (fun j => Fin.removeNth i0 (g j - s j • a • u))
      exact ⟨Fin.cons a c, ⟨(e1.trans ((LinearEquiv.refl O _).prodCongr e2)).trans
        (Smith.consEquiv a c)⟩⟩
  obtain ⟨c, e⟩ := hsmith n g
  have hc : HasLen v O ((Fin n → O) ⧸ Submodule.span O (Set.range g))
      (∏ i, v (algebraMap O C (c i))) := ⟨n, c, e, rfl⟩
  exact ⟨_, hasLen_of_equiv ((Submodule.quotEquivOfEq _ _ hg).trans
    (f.quotKerEquivOfSurjective hf)).symm hc⟩

private theorem hasLen_mono {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) {M M' : Type} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') {z z' : NNReal} (hf : Function.Surjective f)
    (hz : HasLen v R M z) (hz' : HasLen v R M' z') : z ≤ z' := by
  have := isLocal_of_integers hv
  obtain ⟨m, c, ⟨e⟩, hzc⟩ := hz
  obtain ⟨r, q, ⟨e'⟩, hzq⟩ := hz'
  let π : M →ₗ[R] ((t : Fin r) → R ⧸ Ideal.span {q t}) := e'.toLinearMap ∘ₗ f
  have hπ : Function.Surjective π := e'.surjective.comp hf
  let y : Fin m → ((t : Fin r) → R ⧸ Ideal.span {q t}) :=
    fun i => π (e.symm (Pi.single i 1))
  have hspan : Submodule.span R (Set.range y) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨x, rfl⟩ := hπ w
    have hx := eq_sum_single c (e x)
    have : x = ∑ i, (Quotient.out (e x i) : R) • e.symm (Pi.single i 1) := by
      calc x = e.symm (e x) := (e.symm_apply_apply x).symm
        _ = e.symm (∑ i, (Quotient.out (e x i) : R) • (Pi.single i (1 : R ⧸ Ideal.span {c i}) :
            (i : Fin m) → R ⧸ Ideal.span {c i})) := congrArg e.symm hx
        _ = _ := by simp only [map_sum, map_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hT : ∀ k, ∑ i, (Matrix.diagonal c) k i • y i = 0 := by
    intro k
    rw [Finset.sum_eq_single k]
    · simp only [Matrix.diagonal_apply_eq, y]
      rw [← map_smul, ← map_smul, single_smul_self, map_zero, map_zero]
    · intro b _ hb; rw [Matrix.diagonal_apply_ne _ (Ne.symm hb), zero_smul]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hdet := det_mem_span_prod r q m y hspan (Matrix.diagonal c) hT
  rw [Matrix.det_diagonal] at hdet
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hdet
  have hle := hv.le_of_dvd (⟨w, by rw [← hw, mul_comm]⟩ : ∏ t : Fin r, q t ∣ ∏ i, c i)
  rw [map_prod, map_prod, map_prod, map_prod] at hle
  rw [← hzc, ← hzq]
  exact hle

private theorem fp_quot {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) (n : ℕ) (M N : Submodule O (Fin n → O)) (hM : M.FG)
    (hN : N.FG) (hle : N ≤ M) : Module.FinitePresentation O (M ⧸ N.comap M.subtype) := by
  have : IsDomain O := hv.hom_inj.isDomain
  have : IsFractionRing O C := hv.isFractionRing
  have : ValuationRing O := ValuationRing.of_integers v hv
  have : Module.Finite O M := Module.Finite.iff_fg.2 hM
  have : Module.Flat O M := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
    infer_instance
  have : Module.Free O M := Module.free_of_flat_of_isLocalRing
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  refine Module.finitePresentation_of_surjective (N.comap M.subtype).mkQ
    (Submodule.mkQ_surjective _) ?_
  rw [Submodule.ker_mkQ]
  refine Submodule.fg_of_fg_map_injective M.subtype M.injective_subtype ?_
  rwa [Submodule.map_comap_subtype, inf_eq_right.2 hle]

theorem hasLen_exists_mono_fp : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → (∀ (M : Type) [AddCommGroup M] [Module O M], Module.FinitePresentation O M → ∃ x, HasLen v O M x) ∧ (∀ (M M' : Type) [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M'] (f : M →ₗ[O] M') (x x' : NNReal), Function.Surjective f → HasLen v O M x → HasLen v O M' x' → x ≤ x') ∧ ∀ (n : ℕ) (M N : Submodule O (Fin n → O)), M.FG → N.FG → N ≤ M → Module.FinitePresentation O (M ⧸ N.comap M.subtype) :=
  fun _ _ _ _ _ _ hv => ⟨fun M _ _ h => hasLen_of_fp hv M h,
    fun _ _ _ _ _ _ f _ _ hf hx hx' => hasLen_mono hv f hf hx hx',
    fun n M N hM hN hle => fp_quot hv n M N hM hN hle⟩

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HopfPointMem
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem hopfPoint_mem {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]
    (N : Type) [Unique N] (f : N → C) (hf : f ∈ L2.intFun (C := C) R N) :
    ∃ r : R, f = r • (1 : N → C) := by
  obtain ⟨r, hr⟩ := hf default
  refine ⟨r, funext fun x => ?_⟩
  rw [Subsingleton.elim x default, ← hr]
  simp [Algebra.smul_def]

private theorem hopfPoint_one {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]
    (N : Type) : (1 : N → C) ∈ L2.intFun (C := C) R N := fun _ => ⟨1, by simp⟩

private def hopfPoint {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]
    (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] [Unique N] :
    L2.HopfOrder (C := C) R N where
  carrier := L2.intFun R N
  lat := by
    refine ⟨1, by simp, le_antisymm ?_ ?_⟩
    · intro f hf
      obtain ⟨r, rfl⟩ := hopfPoint_mem R N f hf
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨default, ?_⟩)
      funext x
      rw [Subsingleton.elim x default]
      simp
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩ x
      refine ⟨1, ?_⟩
      rw [Subsingleton.elim x j]
      simp
  le_int := le_rfl
  one_mem := hopfPoint_one R N
  mul_mem := by
    intro f g hf hg x
    obtain ⟨r, hr⟩ := hf x
    obtain ⟨s, hs⟩ := hg x
    exact ⟨r * s, by simp [hr, hs]⟩
  comul := by
    intro f hf
    refine Submodule.subset_span ⟨f, hf, 1, hopfPoint_one R N, ?_⟩
    funext q
    change f (q.1 + q.2) = f q.1 * 1
    rw [_root_.mul_one, Subsingleton.elim (q.1 + q.2) q.1]
  antipode := fun f hf x => hf (-x)

theorem htd_dim_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [StarRing OE] (cp : O), Nonempty (HodgeTateDatum p 0 v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ OE _ _ cp
  let _ : Unique (Nb p 0) := Pi.uniqueOfIsEmpty _
  have hS : Subsingleton (LieDualModP p O 0) :=
    (Submodule.Quotient.mk_surjective _).subsingleton
  refine ⟨{
    ρ :=
      { toFun := fun _ => 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ => Subsingleton.elim _ _
        map_zero' := Subsingleton.elim _ _
        map_add' := fun _ _ => Subsingleton.elim _ _
        commutes' := fun _ => Subsingleton.elim _ _ }
    ρL :=
      { toFun := fun _ => 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ => Subsingleton.elim _ _
        map_zero' := Subsingleton.elim _ _
        map_add' := fun _ _ => Subsingleton.elim _ _ }
    P := 0
    PL := 0
    E := 0
    E_alternating := ⟨Subsingleton.elim _ _, fun _ => rfl⟩
    isUnit_det_E := by simp
    E_equivariant := fun _ => Subsingleton.elim _ _
    projectors := ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _,
      fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
    Ht := 0
    Bt := 0
    Ht_equivariant := ⟨fun _ => Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    form_eq_alt := Subsingleton.elim _ _
    AA := hopfPoint O (Nb p 0)
    h3 := fun a f hf => ⟨f, hf, fun t => congrArg f (Subsingleton.elim _ _)⟩
    h4 := fun k => k.elim0
    h5 := fun _ s => ⟨1, hopfPoint_one O _, fun t => by
      have h0 : Up.pair p 0 0 s t = 0 := by simp [Up.pair]
      rw [h0, map_zero, ZMod.val_zero, pow_zero, Pi.one_apply]⟩
    φ := 0
    cotangent_surjective := fun y => ⟨0, Subsingleton.elim _ _⟩
    cotangent_ker_eq := ?_
    cotangent_linear := fun _ _ _ _ _ _ => Subsingleton.elim _ _ }⟩
  rw [LinearMap.ker_zero, eq_comm, eq_top_iff]
  intro f _
  have : f = 0 := by
    apply Subtype.ext
    funext x
    rw [Subsingleton.elim x 0]
    exact f.2.2
  rw [this]
  exact Submodule.zero_mem _

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearPartPairingSeriesEqHeight
section
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

theorem dl_pairSer_eq_height : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (p : ℕ) (Tw : ATowerL R₀ p) (Dt : DualTower Tw) (g : ℕ) (Y : ∀ R : LAlg R₀, LHom Tw.O R → (Fin g → (R : Type)) → B.G R) (gb : Module.Basis (Fin g) R₀ B.gg) (S : Matrix (Fin g) (Fin g) (Tw.O : Type)), TanMat B Tw.O Y gb S → ∀ (τ : ℕ → B.G Tw.O) (u : PS (Tw.O : Type) 1 g), MvPowerSeries.constantCoeff u = 1 → PairSer B Tw.O Y p τ u → ∀ ht : B.gg →ₗ[R₀] (Tw.O : Type), (∀ n, B.IsHeight (Dt.Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ n)) ((Tw.q n).1.toLinearMap ∘ₗ ht)) → Sᵀ *ᵥ dl u = fun l => ht (gb l) := by
  intro R₀ _ B p Tw Dt g Y gb S hS τ u hu hP ht hH
  funext l
  rw [← sub_eq_zero]
  refine Tw.sep _ fun n => (Dt.Dp n).free _ ?_
  set Dp := Dt.Dp n
  obtain ⟨z, hz, hz'⟩ := hH n (gb l)
  let s : LHom Tw.O Dp.D := Dp.σ.comp (Tw.q n)
  have hs : ∀ x, s.1 x = Dp.σ.1 ((Tw.q n).1 x) := fun _ => rfl
  have hc : ((p ^ (n + 1) : ℕ) : (Tw.R n : Type)) = 0 := by
    rw [← map_natCast (Tw.π n).1, Tw.char n, map_zero]
  have hp : IsNilpotent (p : (Dp.D : Type)) :=
    ⟨n + 1, by rw [← Nat.cast_pow, ← map_natCast Dp.σ.1, hc, map_zero]⟩
  have hsq : ∀ x y : (Dp.D : Type), x * Dp.η * (y * Dp.η) = 0 := fun x y => by
    rw [_root_.mul_mul_mul_comm, Dp.η_sq, mul_zero]
  have ha : ∀ k, IsNilpotent (s.1 (S k l) * Dp.η) := fun k => ⟨2, by rw [pow_two, hsq]⟩
  rw [hS Dp.D _ s Dp.π Dp.sqZero l Dp.ηk, ← B.map_comp] at hz
  have h1 := hP Dp.D s (fun k => s.1 (S k l) * Dp.η) n z hp ha hz
  have h2 := (nv_calculus _ _ s.1.toRingHom 1 g ![fun k => s.1 (S k l) * Dp.η]
    (fun i j => by simpa using ha j)).2.2.2.2.2 (fun i j i' j' => by simpa using hsq _ _) u
  rw [h2, hz', hu, map_one, add_right_inj, Fintype.sum_prod_type, Fin.sum_univ_one] at h1
  rw [← hs, map_sub, sub_mul, sub_eq_zero]
  refine Eq.trans ?_ h1.symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulVec, dotProduct, transpose_apply, dl, map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.cons_val_fin_one, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  ring

end GlobalTheory.ChF
end
end

