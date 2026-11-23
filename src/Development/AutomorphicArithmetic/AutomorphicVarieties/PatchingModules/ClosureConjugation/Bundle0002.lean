module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0009
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.HatRange
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem hr_span {A F : Type} [CommRing A] [IsDomain A] [Field F] [Algebra A F] [IsFractionRing A F] {n a : ℕ}
    (t : A) (ht : t ≠ 0) (T : Set (Matrix (Fin n) (Fin n) A))
    (hT : ∀ Z ∈ Ev A A n a, ∃ s : ℕ, t ^ s • Z ∈ Submodule.span A T)
    (S : Submodule F (Matrix (Fin n) (Fin n) F)) (hS : ∀ Y ∈ T, Y.map (algebraMap A F) ∈ S) :
    Ev F F n a ≤ S := by
  have h1 : ∀ Y ∈ Submodule.span A T, Y.map (algebraMap A F) ∈ S := by
    intro Y hY
    induction hY using Submodule.span_induction with
    | mem y hy => exact hS y hy
    | zero => simp
    | add y z _ _ hy hz =>
      have : (y + z).map (algebraMap A F) = y.map (algebraMap A F) + z.map (algebraMap A F) := by
        ext i j; simp
      rw [this]; exact S.add_mem hy hz
    | smul c y _ hy =>
      have : (c • y).map (algebraMap A F) = algebraMap A F c • y.map (algebraMap A F) := by
        ext i j; simp
      rw [this]; exact S.smul_mem _ hy
  intro Z hZ
  have hZ' : Z = ∑ i, ∑ j, single i j (Z i j) := matrix_eq_sum_single Z
  rw [hZ']
  refine S.sum_mem fun i _ => S.sum_mem fun j _ => ?_
  by_cases e : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
  · obtain ⟨s, hs⟩ := hT (single i j 1) (fun p q => ⟨fun _ => trivial, fun e' => by
      rw [Submodule.mem_bot, Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact e' e⟩)
    have h2 := S.smul_mem (Z i j * (algebraMap A F (t ^ s))⁻¹) (h1 _ hs)
    have hne : algebraMap A F (t ^ s) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective A F)]
      exact pow_ne_zero _ ht
    convert h2 using 1
    ext p q
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one, mul_assoc, inv_mul_cancel₀ hne, mul_one]
    · simp
  · have : Z i j = 0 := (hZ i j).2 e
    simp [this]

theorem UpperTheory.V.Pa.hat_range :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)], Function.Surjective (algebraMap Bh (FractionRing x.A)) → ∀ H : Hat h x u.D P.ker Bh (G.frame.eps O B), ∀ Z, Z ∈ Ev (FractionRing x.A) (FractionRing x.A) n x.a ↔ ∃ y, H.r y = Z := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ _ hs H Z
  have hsm : ∀ (b : Bh) (Y : Matrix (Fin n) (Fin n) (FractionRing x.A)),
      b • Y = algebraMap Bh (FractionRing x.A) b • Y := by
    intro b Y
    ext i j
    simp [Algebra.smul_def]
  constructor
  · let S : Submodule (FractionRing x.A) (Matrix (Fin n) (Fin n) (FractionRing x.A)) :=
      { carrier := {Z | ∃ y, H.r y = Z}
        add_mem' := by
          rintro _ _ ⟨y, rfl⟩ ⟨z, rfl⟩
          exact ⟨y + z, map_add _ _ _⟩
        zero_mem' := ⟨0, map_zero _⟩
        smul_mem' := by
          rintro c _ ⟨y, rfl⟩
          obtain ⟨b, rfl⟩ := hs c
          exact ⟨b • y, by rw [map_smul, hsm]⟩ }
    intro hZ
    refine hr_span (A := x.A) x.t PowerSeries.X_ne_zero _ x.span S ?_ hZ
    rintro _ ⟨g, -, rfl⟩
    obtain ⟨g', hg'⟩ := h.surj g.1
    have hm : g' ∈ G.η.ker := by
      have h1 := h.η g'
      rw [hg'] at h1
      rw [MonoidHom.mem_ker, ← h1]
      exact g.2
    have : h.p₀ ⟨g', hm⟩ = g := Subtype.ext hg'
    exact ⟨_, by rw [← this]; exact H.r_ι ⟨g', hm⟩⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := H.surj y
    induction z using MonoidAlgebra.induction_on with
    | of g =>
      have := H.r_ι g
      rw [MonoidAlgebra.of_apply, this]
      intro i j
      refine ⟨fun _ => trivial, fun e => ?_⟩
      have h0 : mat x.ρ (h.p₀ g) i j = 0 := (x.blk (h.p₀ g) i j).2 e
      rw [Submodule.mem_bot, Matrix.map_apply, h0, map_zero]
    | add f g hf hg =>
      rw [map_add (f := _), map_add (f := _)]
      exact Submodule.add_mem _ hf hg
    | smul b f hf =>
      rw [map_smul, map_smul, hsm]
      exact Submodule.smul_mem _ _ hf
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.IdemNil
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem charpoly_single {F : Type} [CommRing F] {m : ℕ} (i : Fin (m + 1)) :
    (single i i (1 : F)).charpoly = X ^ (m + 1) - X ^ m := by
  rw [← Matrix.diagonal_single, Matrix.charpoly_diagonal, Fin.prod_univ_succAbove _ i]
  simp [Pi.single_apply, Fin.succAbove_ne]
  ring

theorem UpperTheory.V.Pa.idem_nil :
    ∀ {B E F : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field F] [Algebra B F] {n : ℕ} (D : Det n B E) (r : E →ₐ[B] Matrix (Fin n) (Fin n) F), D.IsCH → RingHom.ker (algebraMap B F) = maximalIdeal B → (∀ y, (D.chi y).map (algebraMap B F) = (r y).charpoly) → (∀ y, r y = 0 → ∃ M : ℕ, y ^ M ∈ maximalIdeal B • (⊤ : Submodule B E)) ∧ ∀ (e : E) (i : Fin n), IsIdempotentElem e → r e = single i i 1 → D.D B[X] (1 + X ⊗ₜ e) = 1 + X := by
  intro B E F _ _ _ _ _ _ n D r hch hker hchi
  refine ⟨fun y hy => ⟨n, ?_⟩, fun e i he hre => ?_⟩
  · have h0 := ((d_chS D B).2.2 hch).2 y
    have h1 : (X ^ n - D.chi y).map (algebraMap B F) = 0 := by
      rw [Polynomial.map_sub, hchi, hy, Matrix.charpoly_zero]; simp
    have h2 : y ^ n = aeval y (X ^ n - D.chi y) := by simp [h0]
    rw [h2, aeval_eq_sum_range]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [← hker, RingHom.mem_ker, ← coeff_map, h1, coeff_zero]
  · obtain ⟨k, -, hk⟩ := d_idem_rank D e he
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
    have hc := hchi e
    rw [hre, charpoly_single] at hc
    have hl : ∀ j, algebraMap B F (D.lam j e) = (-1) ^ j * (X ^ (m + 1) - X ^ m : F[X]).coeff (m + 1 - j) := by
      intro j
      rw [← hc, coeff_map, Det.lam]; simp
    have h3 : (D.D B[X] (1 + X ⊗ₜ e)).map (algebraMap B F) = 1 + X := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [(d_chi D e).2.2.1, Polynomial.map_sum, Finset.sum_range_succ', Finset.sum_range_succ',
        Finset.sum_eq_zero]
      · simp [hl, coeff_X_pow, add_comm]
      · intro j hj
        rw [Finset.mem_range] at hj
        have a1 : ¬ (m - (j + 1) = m + 1) := by omega
        have a2 : ¬ (m - (j + 1) = m) := by omega
        simp [hl, coeff_X_pow, a1, a2]
    rw [hk] at h3 ⊢
    have h4 := congrArg natDegree h3
    have h5 : natDegree (1 + X : F[X]) = 1 := by rw [add_comm]; exact natDegree_X_add_C 1
    have h6 : Monic (1 + X : F[X]) := by rw [add_comm]; exact monic_X_add_C 1
    rw [Polynomial.map_pow, Polynomial.map_add (f := _), Polynomial.map_one, map_X, h6.natDegree_pow, h5, mul_one] at h4
    rw [h4, pow_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.PairMf
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.pair_mf :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] {r : Resid F O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B), PhiCond F.G₀ l → Finite (ResidueField B) ∧ (l : B) ∈ maximalIdeal B ∧ ∃ (h : ℕ) (χ : Fin n → F.G₀ →* (ResidueField B)ˣ), u.D.map (residue B) = GDet.ofChars χ ∧ MultFree χ h := by
  intro l _ F n O _ _ _ hc _ r B _ _ _ u hΦ
  haveI := hc.finite
  haveI := hc.char
  let e : ResidueField O ≃+* ResidueField B := RingEquiv.ofBijective _ (resMap_bijective O B)
  haveI hfin : Finite (ResidueField B) := Finite.of_equiv _ e.toEquiv
  haveI hch : CharP (ResidueField B) l := charP_of_injective_ringHom (f := e.toRingHom) e.injective l
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.1 (F.η.ker.isClosed_of_isOpen F.η_open).isCompact
  let χ : Fin n → F.G₀ →* (ResidueField B)ˣ := fun i => pushCh e.toRingHom (r.chib i)
  have hU : Function.Injective (Units.map (e.toRingHom : ResidueField O →* ResidueField B)) :=
    Units.map_injective e.injective
  have hop : ∀ i, IsOpen ((χ i).ker : Set F.G₀) := fun i => by
    have : (χ i).ker = (r.chib i).ker := MonoidHom.ker_comp_of_injective _ _ hU
    rw [this]
    exact r.chib_open i
  have hinj : Function.Injective χ := fun i j hij =>
    r.chib_inj (MonoidHom.ext fun g => hU (DFunLike.congr_fun hij g))
  obtain ⟨h, hh⟩ := exists_multFree_of_phiCond_of_injective_chars l χ hΦ hop hinj
  refine ⟨hfin, ?_, h, χ, ?_, hh⟩
  · rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  · have h1 : residue B = e.toRingHom.comp (res O B : B →+* ResidueField O) :=
      RingHom.ext fun b => (e.apply_symm_apply (residue B b)).symm
    rw [h1, ← (d_gmap u.D).2.1, u.red, Resid.Dbar, (d_gmap r.Dbar).2.2.2]
    unfold GDet.ofChars
    congr 1
    refine MonoidHom.ext fun g => ?_
    change (Matrix.diagonal fun i => ((r.chib i g : (ResidueField O)ˣ) : ResidueField O)).map e.toRingHom = _
    rw [Matrix.diagonal_map (map_zero _)]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.PhiFg
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem finite_open_homs_to_finite_group (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (h : TopFG G)
    (Z : Type) [Group Z] [Finite Z] : Finite {φ : G →* Z // IsOpen (φ.ker : Set G)} := by
  obtain ⟨s, hs, hgen⟩ := h
  rw [topGen_iff] at hgen
  have : Finite s := hs.to_subtype
  let f : {φ : G →* Z // IsOpen (φ.ker : Set G)} → (s → Z) := fun φ x => φ.1 x
  apply Finite.of_injective f
  intro φ ψ hφψ
  apply Subtype.ext
  have hK : IsOpen ((φ.1.ker ⊓ ψ.1.ker : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]
    exact φ.2.inter ψ.2
  have hle : φ.1.ker ⊓ ψ.1.ker ≤ MonoidHom.eqLocus φ.1 ψ.1 := by
    intro g hg
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hg
    show φ.1 g = ψ.1 g
    rw [hg.1, hg.2]
  have hopen := Subgroup.isOpen_mono hle hK
  have hcl := Subgroup.isClosed_of_isOpen _ hopen
  have hs' : Subgroup.closure (s : Set G) ≤ MonoidHom.eqLocus φ.1 ψ.1 := by
    rw [Subgroup.closure_le]
    intro x hx
    exact congrFun hφψ ⟨x, hx⟩
  have htop := Subgroup.topologicalClosure_minimal _ hs' hcl
  rw [hgen] at htop
  ext g
  exact htop (Subgroup.mem_top g)

theorem UpperTheory.V.Pa.phi_fg :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l),
      (∃ s : Finset F.Γ, (Subgroup.closure (s : Set F.Γ)).topologicalClosure = ⊤) →
        PhiCond (Γ := F.G₀) l := by
  intro l _ F hF
  obtain ⟨s, hs⟩ := hF
  have hΓ : TopFG F.Γ := ⟨(s : Set F.Γ), s.finite_toSet, (topGen_iff _).mpr hs⟩
  have hopen : IsOpen ((F.η.ker : Subgroup F.Γ) : Set F.Γ) := F.η_open
  have hG : TopFG F.G₀ := ((TopFG.subgroup_quot F.Γ hΓ).1 _ hopen)
  have : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ hopen).isCompact
  intro H hH
  have hH' : TopFG H := (TopFG.subgroup_quot F.G₀ hG).1 H hH
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  exact finite_open_homs_to_finite_group H hH' (Multiplicative (ZMod l))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.StarBasic
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem conj_conj_of_isQuad {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) : F.conj (F.conj g) = g := by
  have h : F.c⁻¹ = F.c := (eq_inv_of_mul_eq_one_left F.c_sq).symm
  apply Subtype.ext
  simp only [GFrame.conj, MonoidHom.coe_mk, OneHom.coe_mk, h]
  simp only [← mul_assoc, F.c_sq, one_mul]
  rw [mul_assoc, F.c_sq, mul_one]

private theorem eps_conj_eq_eps {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (g : F.G₀) : F.eps O R (F.conj g) = F.eps O R g := by
  simp only [GFrame.eps, pushCh, MonoidHom.comp_apply, Subgroup.coe_subtype, GFrame.conj, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, map_inv]
  rw [mul_right_comm, mul_inv_cancel, one_mul]

private theorem star_single_eq_single_conj_inv_mul_eps_zpow' {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) (b : R) : F.star O R n (MonoidAlgebra.single g b) = MonoidAlgebra.single (F.conj g)⁻¹ (b * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
  simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]

theorem UpperTheory.V.Pa.star_basic :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (n : ℕ) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R], (∀ y, F.star O R n (F.star O R n y) = y) ∧ (∀ y z, F.star O R n (y * z) = F.star O R n z * F.star O R n y) ∧ (∀ y z, F.star O R n (y + z) = F.star O R n y + F.star O R n z) ∧ (∀ (b : R) y, F.star O R n (b • y) = b • F.star O R n y) ∧ F.star O R n 1 = 1 ∧ (∀ y z, F.star O R n (y - z) = F.star O R n y - F.star O R n z) ∧ ∀ g b, F.star O R n (MonoidAlgebra.single g b) = MonoidAlgebra.single (F.conj g)⁻¹ (b * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
  intro l _ F n O _ _ R _ _
  have hadd : ∀ y z, F.star O R n (y + z) = F.star O R n y + F.star O R n z := by
    intro y z
    simp [GFrame.star, map_add (f := _)]
  refine ⟨?_, ?_, hadd, ?_, ?_, ?_, star_single_eq_single_conj_inv_mul_eps_zpow' F O R n⟩
  · intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp [GFrame.star]
    | add y z hy hz => rw [hadd, hadd, hy, hz]
    | single g b =>
      rw [star_single_eq_single_conj_inv_mul_eps_zpow', star_single_eq_single_conj_inv_mul_eps_zpow', map_inv, inv_inv, conj_conj_of_isQuad, map_inv, eps_conj_eq_eps, _root_.inv_zpow', mul_assoc, ← Units.val_mul, ← _root_.zpow_add]
      simp
  · intro y z
    simp [GFrame.star, map_mul]
  · intro b y
    simp [GFrame.star, map_smul]
  · simp [GFrame.star, map_one]
  · intro y z
    simp [GFrame.star, map_sub]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.StarClosure
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

section
variable {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R]
  [Algebra O R] (n : ℕ)

private theorem star_closure_conj_cont : Continuous F.conj := by
  apply Continuous.subtype_mk
  fun_prop

end

private theorem exists_unit_valuation_le_subset_nhds {l : ℕ} [Fact l.Prime] (F : GFrame l) (N : ℕ) (H : OpenNormalSubgroup F.G₀) :
    ∃ H' : OpenNormalSubgroup F.G₀, ∀ h ∈ H', (F.conj h)⁻¹ ∈ H ∧ ((F.ε h : ℤ_[l]) - 1) ∈ Ideal.span {(l : ℤ_[l]) ^ N} := by
  let φ : F.G₀ →* (ZMod (l ^ N))ˣ :=
    (Units.map (PadicInt.toZModPow N : ℤ_[l] →+* ZMod (l ^ N)).toMonoidHom).comp (F.ε.comp F.η.ker.subtype)
  have hK : ∀ h : F.G₀, h ∈ φ.ker ↔ ((F.ε h : ℤ_[l]) - 1) ∈ Ideal.span {(l : ℤ_[l]) ^ N} := by
    intro h
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero, MonoidHom.mem_ker, Units.ext_iff]
    rfl
  let S0 : Subgroup F.G₀ := φ.ker ⊓ Subgroup.comap F.conj (H : Subgroup F.G₀)
  have hN : S0.Normal := by
    haveI : (Subgroup.comap F.conj (H : Subgroup F.G₀)).Normal := Subgroup.Normal.comap H.isNormal' F.conj
    exact Subgroup.normal_inf_normal _ _
  have hcont : Continuous (fun g : F.G₀ => ((F.ε g : ℤ_[l]ˣ) : ℤ_[l])) :=
    Units.continuous_val.comp (F.ε_cont.comp continuous_subtype_val)
  have hopen : IsOpen (S0 : Set F.G₀) := by
    apply Subgroup.isOpen_of_mem_nhds S0 (g := 1)
    apply Filter.inter_mem
    · have hb : (fun g : F.G₀ => ((F.ε g : ℤ_[l]ˣ) : ℤ_[l])) ⁻¹' Metric.ball 1 ((l : ℝ) ^ (-(N : ℤ))) ∈ nhds (1 : F.G₀) := by
        apply hcont.continuousAt.preimage_mem_nhds
        have h1 : ((F.ε ((1 : F.G₀) : F.Γ) : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by simp
        rw [h1]
        apply Metric.ball_mem_nhds
        have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
        positivity
      apply Filter.mem_of_superset hb
      intro g hg
      simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hg
      show g ∈ φ.ker
      rw [hK, ← PadicInt.norm_le_pow_iff_mem_span_pow]
      exact hg.le
    · apply (H.isOpen'.preimage (star_closure_conj_cont F)).mem_nhds
      show F.conj 1 ∈ (H : Subgroup F.G₀)
      rw [map_one]
      exact one_mem _
  refine ⟨⟨⟨S0, hopen⟩, hN⟩, ?_⟩
  intro h hh
  have hh' : h ∈ S0 := hh
  refine ⟨inv_mem hh'.2, (hK h).1 hh'.1⟩

theorem UpperTheory.V.Pa.star_closure :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (n : ℕ) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (I : Ideal R) (S : Set (MonoidAlgebra R F.G₀)), (l : R) ∈ I → (∀ z ∈ S, F.star O R n z ∈ TwoSidedIdeal.span S) → ∀ y ∈ closureIdeal I S, F.star O R n y ∈ closureIdeal I S := by
  intro l _ F n O _ _ R _ _ I S hl hS y hy
  have hadd : ∀ y z, F.star O R n (y + z) = F.star O R n y + F.star O R n z := by
    intro y z
    simp [GFrame.star, map_add (f := _)]
  have hneg : ∀ y, F.star O R n (-y) = -F.star O R n y := by
    intro y
    simp [GFrame.star, map_neg]
  have hsub : ∀ y z, F.star O R n (y - z) = F.star O R n y - F.star O R n z := by
    intro y z
    simp [GFrame.star, map_sub]
  have hzero : F.star O R n 0 = 0 := by simp [GFrame.star]
  have hmul : ∀ y z, F.star O R n (y * z) = F.star O R n z * F.star O R n y := by
    intro y z
    simp [GFrame.star, map_mul]
  have hsingle : ∀ (g : F.G₀) (b : R), F.star O R n (MonoidAlgebra.single g b) =
      MonoidAlgebra.single (F.conj g)⁻¹ (b * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
    intro g b
    simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]
  have h1 : F.star O R n 1 = 1 := by simp [GFrame.star, map_one]
  simp only [closureIdeal, TwoSidedIdeal.mem_iInf] at hy ⊢
  intro N H
  obtain ⟨H', hH'⟩ := exists_unit_valuation_le_subset_nhds F N H
  set T := TwoSidedIdeal.span (S ∪ {z : MonoidAlgebra R F.G₀ | ∃ a ∈ I ^ N, z = MonoidAlgebra.single 1 a} ∪
    {z : MonoidAlgebra R F.G₀ | ∃ h ∈ H, z = MonoidAlgebra.single h 1 - 1}) with hT
  have hJ : ∀ a ∈ I ^ N, MonoidAlgebra.single (1 : F.G₀) a ∈ T := by
    intro a ha
    apply TwoSidedIdeal.subset_span
    exact Or.inl (Or.inr ⟨a, ha, rfl⟩)
  have hKH : ∀ h ∈ H, MonoidAlgebra.single h (1 : R) - 1 ∈ T := by
    intro h hh
    apply TwoSidedIdeal.subset_span
    exact Or.inr ⟨h, hh, rfl⟩
  have hST : TwoSidedIdeal.span S ≤ T := by
    rw [TwoSidedIdeal.span_le]
    exact (Set.subset_union_left.trans Set.subset_union_left).trans TwoSidedIdeal.subset_span
  have heps : ∀ h ∈ H', ((F.eps O R h : Rˣ) : R) - 1 ∈ I ^ N := by
    intro h hh
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (hH' h hh).2
    have hv : ((F.eps O R h : Rˣ) : R) = algebraMap O R (algebraMap ℤ_[l] O ((F.ε h : ℤ_[l]ˣ) : ℤ_[l])) := by
      simp [GFrame.eps, pushCh]
    rw [hv, eq_add_of_sub_eq' ht.symm]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast, map_one, add_sub_cancel_left]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hl N)
  refine TwoSidedIdeal.span_induction (p := fun x _ => F.star O R n x ∈ T) ?_ ?_ ?_ ?_ ?_ ?_ (hy N H')
  · rintro x ((hx | ⟨a, ha, rfl⟩) | ⟨h, hh, rfl⟩)
    · exact hST (hS x hx)
    · rw [hsingle]
      simpa using hJ a ha
    · have hk : (h ^ (1 - (n : ℤ))) ∈ H' := zpow_mem hh _
      have hu := heps _ hk
      rw [map_zpow] at hu
      rw [hsub, hsingle, one_mul, h1]
      set u : R := ((F.eps O R h ^ (1 - (n : ℤ)) : Rˣ) : R)
      have hsplit : MonoidAlgebra.single (F.conj h)⁻¹ u - 1 =
          MonoidAlgebra.single (F.conj h)⁻¹ (1 : R) * MonoidAlgebra.single 1 (u - 1) +
            (MonoidAlgebra.single (F.conj h)⁻¹ (1 : R) - 1) := by
        rw [MonoidAlgebra.single_mul_single, mul_one, one_mul, MonoidAlgebra.single_sub]
        abel
      rw [hsplit]
      exact T.add_mem (T.mul_mem_left _ _ (hJ _ hu)) (hKH _ (hH' h hh).1)
  · rw [hzero]
    exact T.zero_mem
  · intro x z _ _ hx hz
    rw [hadd]
    exact T.add_mem hx hz
  · intro x _ hx
    rw [hneg]
    exact T.neg_mem hx
  · intro a x _ hx
    rw [hmul]
    exact T.mul_mem_right _ _ hx
  · intro b x _ hx
    rw [hmul]
    exact T.mul_mem_left _ _ hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.ToTMap
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem toT_map {B G : Type} [CommRing B] [Group G] (C : Type) [CommRing C] [Algebra B C]
    (y : MonoidAlgebra B G) : toT B G C (MonoidAlgebra.mapRingHom G (algebraMap B C) y) = 1 ⊗ₜ y := by
  have h := toT_ofT (A := B) (S := C) (1 ⊗ₜ y)
  rwa [ofT_tmul, one_smul] at h

theorem UpperTheory.V.Pa.tens :
    ∀ {n : ℕ} {B G E : Type} [CommRing B] [Group G] [Ring E] [Algebra B E] (D : GDet n B G) (DE : Det n B E) (π : MonoidAlgebra B G →ₐ[B] E) (C : Type) [CommRing C] [Algebra B C], Function.Surjective π → DE.pull π = D.toDet → ∃ ι : MonoidAlgebra C G →ₐ[C] C ⊗[B] E, Function.Surjective ι ∧ (∀ y, ι (MonoidAlgebra.mapRingHom G (algebraMap B C) y) = 1 ⊗ₜ π y) ∧ (∀ y, ι y = 0 ↔ y ∈ TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G (algebraMap B C) '' {z | π z = 0})) ∧ (DE.baseChange C).pull ι = (D.map (algebraMap B C)).toDet := by
  intro n B G E _ _ _ _ D DE π C _ _ hπ hD
  let m : C ⊗[B] MonoidAlgebra B G →ₐ[C] C ⊗[B] E := Algebra.TensorProduct.map (AlgHom.id C C) π
  have hm : ∀ x, m x = π.toLinearMap.lTensor C x := fun x => by
    induction x with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul s y => rfl
  have h2 : ∀ y, m (toT B G C (MonoidAlgebra.mapRingHom G (algebraMap B C) y)) = 1 ⊗ₜ π y := fun y => by
    rw [toT_map]; rfl
  refine ⟨m.comp (toT B G C), fun w => ?_, h2, fun y => ⟨fun hy => ?_, fun hy => ?_⟩, ?_⟩
  · obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective C (g := π.toLinearMap) hπ w
    exact ⟨ofT B G C x, by rw [AlgHom.comp_apply, toT_ofT, hm, hx]⟩
  · rw [AlgHom.comp_apply, hm] at hy
    obtain ⟨x, hx⟩ := (lTensor_exact C (LinearMap.exact_subtype_ker_map π.toLinearMap) hπ _).1 hy
    rw [← ofT_toT (A := B) y, ← hx]
    clear hx
    induction x with
    | add a b ha hb => rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
    | tmul s z =>
      rw [LinearMap.lTensor_tmul, ofT_tmul, Algebra.smul_def]
      exact TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.subset_span ⟨z, z.2, rfl⟩)
  · have hle : TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G (algebraMap B C) '' {z | π z = 0}) ≤
        TwoSidedIdeal.ker (m.comp (toT B G C)) := by
      rw [TwoSidedIdeal.span_le]
      rintro _ ⟨z, hz, rfl⟩
      refine (TwoSidedIdeal.mem_ker _).2 ((h2 z).trans ?_)
      rw [show π z = 0 from hz, TensorProduct.tmul_zero]
    exact (TwoSidedIdeal.mem_ker _).1 (hle hy)
  · rw [d_toDet_map, ← hD]
    refine Det.ext' fun S _ _ x => ?_
    letI : Algebra B S := ((algebraMap C S).comp (algebraMap B C)).toAlgebra
    haveI : IsScalarTower B C S := .of_algebraMap_eq fun _ => rfl
    have h : Det.cancel B E C S (Algebra.TensorProduct.map (AlgHom.id S S) (m.comp (toT B G C)) x) =
        Algebra.TensorProduct.map (AlgHom.id S S) π (Det.cancel B (MonoidAlgebra B G) C S
          (Algebra.TensorProduct.map (AlgHom.id S S) (toT B G C) x)) := by
      induction x with
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | tmul s y =>
        rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.comp_apply]
        generalize toT B G C y = w
        induction w with
        | add a b ha hb => simp only [TensorProduct.tmul_add, map_add (f := _), ha, hb]
        | tmul c z => simp [m, Det.cancel_tmul]
    exact congrArg (DE.D S) h
end

