module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Derivation.ToSquareZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DChKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CayleyHamiltonSymmetric
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoCaten
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.CocExt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem cocExt_mem {l : ℕ} [Fact l.Prime] (F : W.GFrame l) {x : F.Γ} (hx : x ∉ F.η.ker) : x * F.c ∈ F.η.ker := by
  rw [MonoidHom.mem_ker] at hx ⊢
  rw [map_mul, F.η_c]
  rcases Int.units_eq_one_or (F.η x) with h | h
  · exact absurd h hx
  · rw [h]
    rfl

private theorem cocycle_extends_to_conj_group {l : ℕ} [Fact l.Prime] (F : W.GFrame l) {K M : Type} [CommRing K] [AddCommGroup M] [Module K M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] (R : Representation K F.Γ M) (y : F.G₀ → M) (w : M)
    (hy : Continuous y) (hyc : ∀ g h : F.G₀, y (g * h) = y g + R g (y h))
    (hw : Continuous fun g : F.G₀ => R g w) (hcw : R F.c w = -w)
    (hrel : ∀ g : F.G₀, y (F.conj g) = R F.c (y g) + (w - R (F.conj g) w)) :
    ∃ z : F.Γ → M, Continuous z ∧ (∀ g h, z (g * h) = z g + R g (z h)) ∧ ∀ g : F.G₀, z g = y g := by
  have hcc : F.c * F.c = 1 := F.c_sq
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hcc
  have hc2 : ∀ x : F.Γ, x * F.c * F.c = x := fun x => by rw [mul_assoc, hcc, mul_one]
  have I1 : ∀ g h : F.Γ, g * F.c * (F.c * h * F.c) = g * h * F.c := fun g h => by
    simp only [mul_assoc]
    rw [← mul_assoc F.c F.c, hcc, one_mul]
  have I2 : ∀ g h : F.Γ, g * F.c * (F.c * (h * F.c) * F.c) = g * h := fun g h => by
    simp only [mul_assoc]
    rw [hcc, mul_one, ← mul_assoc F.c F.c, hcc, one_mul]
  have hker : IsOpen (F.η.ker : Set F.Γ) := F.η_open
  have hkerc : IsOpen (F.η.ker : Set F.Γ)ᶜ := (Subgroup.isClosed_of_isOpen _ hker).isOpen_compl
  have Rm : ∀ (a b : F.Γ) (v : M), R (a * b) v = R a (R b v) := fun a b v => by rw [map_mul]; rfl
  have hconj : ∀ k : F.G₀, ((F.conj k : F.G₀) : F.Γ) = F.c * k * F.c := fun k => by
    simp [W.GFrame.conj, hci]
  have hneg : ∀ x : F.Γ, x ∉ F.η.ker → F.η x = -1 := fun x hx => by
    rcases Int.units_eq_one_or (F.η x) with h | h
    · exact absurd (MonoidHom.mem_ker.mpr h) hx
    · exact h
  let z : F.Γ → M := fun x =>
    if hx : x ∈ F.η.ker then y ⟨x, hx⟩ else y ⟨x * F.c, cocExt_mem F hx⟩ + R (x * F.c) w
  have zin : ∀ x (hx : x ∈ F.η.ker), z x = y ⟨x, hx⟩ := fun x hx => dif_pos hx
  have zout : ∀ x (hx : x ∉ F.η.ker), z x = y ⟨x * F.c, cocExt_mem F hx⟩ + R (x * F.c) w :=
    fun x hx => dif_neg hx
  refine ⟨z, ?_, ?_, fun g => zin g g.2⟩
  · rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ F.η.ker
    · apply ContinuousOn.continuousAt _ (hker.mem_nhds hx)
      rw [continuousOn_iff_continuous_restrict]
      have hm : Continuous fun p : (F.η.ker : Set F.Γ) => (⟨p.1, p.2⟩ : F.G₀) :=
        continuous_subtype_val.subtype_mk fun p => p.2
      refine (hy.comp hm).congr fun p => ?_
      exact (zin p.1 p.2).symm
    · apply ContinuousOn.continuousAt _ (hkerc.mem_nhds hx)
      rw [continuousOn_iff_continuous_restrict]
      have hm : Continuous fun p : ((F.η.ker : Set F.Γ)ᶜ : Set F.Γ) => (⟨p.1 * F.c, cocExt_mem F p.2⟩ : F.G₀) :=
        (continuous_subtype_val.mul continuous_const).subtype_mk _
      refine ((hy.comp hm).add (hw.comp hm)).congr fun p => ?_
      exact (zout p.1 p.2).symm
  · intro g h
    by_cases hg : g ∈ F.η.ker <;> by_cases hh : h ∈ F.η.ker
    · rw [zin _ (mul_mem hg hh), zin _ hg, zin _ hh]
      exact hyc ⟨g, hg⟩ ⟨h, hh⟩
    · have hgh : g * h ∉ F.η.ker := fun H => hh (by simpa using mul_mem (inv_mem hg) H)
      rw [zout _ hgh, zin _ hg, zout _ hh]
      have e : (⟨g * h * F.c, cocExt_mem F hgh⟩ : F.G₀) = ⟨g, hg⟩ * ⟨h * F.c, cocExt_mem F hh⟩ :=
        Subtype.ext (mul_assoc _ _ _)
      rw [e, hyc, map_add (f := _), ← Rm, ← mul_assoc]
      exact add_assoc _ _ _
    · have hgh : g * h ∉ F.η.ker := fun H => hg (by simpa using mul_mem H (inv_mem hh))
      rw [zout _ hgh, zout _ hg, zin _ hh]
      have e : (⟨g * h * F.c, cocExt_mem F hgh⟩ : F.G₀) = ⟨g * F.c, cocExt_mem F hg⟩ * F.conj ⟨h, hh⟩ := by
        apply Subtype.ext
        show g * h * F.c = g * F.c * ((F.conj ⟨h, hh⟩ : F.G₀) : F.Γ)
        rw [hconj]
        exact (I1 g h).symm
      rw [e, hyc, hrel, map_add (f := _), map_sub]
      have e1 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R F.c (y ⟨h, hh⟩)) = R g (y ⟨h, hh⟩) := by
        rw [← Rm]
        show R (g * F.c * F.c) _ = _
        rw [hc2]
      have e2 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R (↑(F.conj ⟨h, hh⟩)) w) = R (g * h * F.c) w := by
        rw [← Rm, hconj]
        show R (g * F.c * (F.c * h * F.c)) w = _
        rw [I1]
      rw [e1, e2]
      show y _ + (R g _ + (R (g * F.c) w - R (g * h * F.c) w)) + R (g * h * F.c) w = y _ + R (g * F.c) w + R g _
      abel
    · have hgh : g * h ∈ F.η.ker := by
        rw [MonoidHom.mem_ker, map_mul, hneg g hg, hneg h hh]
        decide
      rw [zin _ hgh, zout _ hg, zout _ hh]
      have e : (⟨g * h, hgh⟩ : F.G₀) = ⟨g * F.c, cocExt_mem F hg⟩ * F.conj ⟨h * F.c, cocExt_mem F hh⟩ := by
        apply Subtype.ext
        show g * h = g * F.c * ((F.conj ⟨h * F.c, cocExt_mem F hh⟩ : F.G₀) : F.Γ)
        rw [hconj]
        exact (I2 g h).symm
      rw [e, hyc, hrel, map_add (f := _), map_sub, map_add (f := _)]
      have e1 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R F.c (y ⟨h * F.c, cocExt_mem F hh⟩)) =
          R g (y ⟨h * F.c, cocExt_mem F hh⟩) := by
        rw [← Rm]
        show R (g * F.c * F.c) _ = _
        rw [hc2]
      have e2 : R (↑(⟨g * F.c, cocExt_mem F hg⟩ : F.G₀)) (R (↑(F.conj ⟨h * F.c, cocExt_mem F hh⟩)) w) =
          -R g (R (h * F.c) w) := by
        rw [← Rm, hconj]
        show R (g * F.c * (F.c * (h * F.c) * F.c)) w = _
        rw [I2, ← Rm, ← mul_assoc, Rm (g * h) F.c, hcw, map_neg, neg_neg]
      rw [e1, e2]
      show y _ + (R g _ + (R (g * F.c) w - -R g (R (h * F.c) w))) = y _ + R (g * F.c) w + (R g _ + R g (R (h * F.c) w))
      abel

theorem UpperTheory.V.Ws.Eb.cocExt :
    ∀ {l : ℕ} [Fact l.Prime] (F : W.GFrame l) {K : Type} [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ} (ρ : F.G₀ →* GL (Fin n) K) (P : GL (Fin n) K) (R : Representation K F.Γ (Matrix (Fin n) (Fin n) K)), Full ρ → Continuous ρ → IsAdExt F ρ P R →
        ∀ y ∈ Z1 (Loc.adGL ρ), ∀ Z, (∀ g, y (F.conj g) = R F.c (y g) + (R (F.conj g) Z - Z)) → ∃ z ∈ Z1 R, ∀ g : F.G₀, z g = y g := by
  intro l _ F K _ _ _ _ n ρ P R hF hρ hA y hy Z hZ
  obtain ⟨hy0, hycoc⟩ := hy
  have hcc : F.c * F.c = 1 := F.c_sq
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hcc
  have Rm : ∀ (a b : F.Γ) (v : Matrix (Fin n) (Fin n) K), R (a * b) v = R a (R b v) :=
    fun a b v => by rw [map_mul]; rfl
  have Rcc : ∀ v, R F.c (R F.c v) = v := fun v => by rw [← Rm, hcc, map_one]; rfl
  have hconj : ∀ k : F.G₀, ((F.conj k : F.G₀) : F.Γ) = F.c * k * F.c := fun k => by
    simp [W.GFrame.conj, hci]
  have cc : ∀ g : F.G₀, F.conj (F.conj g) = g := fun g => by
    apply Subtype.ext
    rw [hconj, hconj]
    simp only [← mul_assoc, hcc, one_mul]
    rw [mul_assoc, hcc, mul_one]
  have hyc : ∀ g h : F.G₀, y (g * h) = y g + R g (y h) := fun g h => by
    rw [hycoc g h, hA.ad]
  have hinv : ∀ g : F.G₀, R g (Z + R F.c Z) = Z + R F.c Z := by
    intro g
    have e2 := hZ (F.conj g)
    rw [cc, hZ g, map_add (f := _), Rcc, map_sub, ← Rm, hconj] at e2
    have ec : F.c * (F.c * (g : F.Γ) * F.c) = g * F.c := by
      rw [← mul_assoc, ← mul_assoc, hcc, one_mul]
    rw [ec, Rm] at e2
    rw [map_add (f := _), ← sub_eq_zero, ← neg_eq_zero]
    rw [← sub_eq_zero] at e2
    rw [← e2]
    abel
  set w : Matrix (Fin n) (Fin n) K := (2 : K)⁻¹ • (R F.c Z - Z) with hwdef
  have hcw : R F.c w = -w := by
    rw [hwdef, map_smul, map_sub, Rcc, ← smul_neg, neg_sub]
  have hrel : ∀ g : F.G₀, y (F.conj g) = R F.c (y g) + (w - R (F.conj g) w) := by
    intro g
    rw [hZ g]
    congr 1
    have hi := hinv (F.conj g)
    rw [map_add (f := _)] at hi
    rw [hwdef, map_smul, map_sub, ← smul_sub]
    have hb : R (F.conj g) (R F.c Z) = Z + R F.c Z - R (F.conj g) Z := by
      rw [← hi]
      abel
    rw [hb]
    have e : R F.c Z - Z - (Z + R F.c Z - R (↑(F.conj g)) Z - R (↑(F.conj g)) Z) =
        (2 : K) • (R (↑(F.conj g)) Z - Z) := by
      rw [two_smul]
      abel
    rw [e, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  have hw : Continuous fun g : F.G₀ => R g w := by
    have e : (fun g : F.G₀ => R g w) =
        fun g => (↑(ρ g) : Matrix (Fin n) (Fin n) K) * w * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K) :=
      funext fun g => by rw [hA.ad]; rfl
    rw [e]
    exact ((Units.continuous_val.comp hρ).matrix_mul continuous_const).matrix_mul (Units.continuous_coe_inv.comp hρ)
  obtain ⟨z, hz, hzc, hzy⟩ := cocycle_extends_to_conj_group F R y w hy0 hyc hw hcw hrel
  exact ⟨z, ⟨hz, hzc⟩, hzy⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.ConjOf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private def dmk {K : Type} [CommRing K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) (DualNumber K) := Matrix.of fun i j => (⟨A i j, B i j⟩ : DualNumber K)

private theorem dmk_mul {K : Type} [CommRing K] {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) K) :
    dmk A B * dmk C D = dmk (A * C) (A * D + B * C) := by
  have hf : ∀ (P Q : Matrix (Fin n) (Fin n) K) i j, TrivSqZeroExt.fst (dmk P Q i j) = P i j := fun _ _ _ _ => rfl
  have hs : ∀ (P Q : Matrix (Fin n) (Fin n) K) i j, TrivSqZeroExt.snd (dmk P Q i j) = Q i j := fun _ _ _ _ => rfl
  ext i j
  · rw [hf, Matrix.mul_apply, TrivSqZeroExt.fst_sum, Matrix.mul_apply]
    simp only [TrivSqZeroExt.fst_mul, hf]
  · rw [hs, Matrix.mul_apply, TrivSqZeroExt.snd_sum, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [TrivSqZeroExt.snd_mul, hf, hs, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]

private theorem dmk_one {K : Type} [CommRing K] {n : ℕ} :
    dmk (1 : Matrix (Fin n) (Fin n) K) 0 = 1 := by
  have hf : ∀ (P Q : Matrix (Fin n) (Fin n) K) i j, TrivSqZeroExt.fst (dmk P Q i j) = P i j := fun _ _ _ _ => rfl
  have hs : ∀ (P Q : Matrix (Fin n) (Fin n) K) i j, TrivSqZeroExt.snd (dmk P Q i j) = Q i j := fun _ _ _ _ => rfl
  ext i j
  · rw [hf, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · rw [hs, Matrix.one_apply, Matrix.zero_apply]
    split_ifs <;> simp

theorem UpperTheory.V.Ws.Eb.conjOf :
    ∀ {K H : Type} [CommRing K] [Group H] {n : ℕ} (ρ : H →* GL (Fin n) K) (y : H → Matrix (Fin n) (Fin n) K) (ρ' : H →* GL (Fin n) (DualNumber K)) (X : Matrix (Fin n) (Fin n) K), IsTan ρ y ρ' → (∀ g, y g = Loc.adGL ρ g X - X) →
        ∃ Q : GL (Fin n) (DualNumber K), ∀ g, ρ' g = Q * W.pushRep (algebraMap K (DualNumber K)) ρ g * Q⁻¹ := by
  intro K H _ _ n ρ y ρ' X hT hy
  unfold IsTan at hT
  have hinv : dmk (1 : Matrix (Fin n) (Fin n) K) (-X) * dmk 1 X = 1 := by
    rw [dmk_mul]
    simp [dmk_one]
  have hinv' : dmk (1 : Matrix (Fin n) (Fin n) K) X * dmk 1 (-X) = 1 := by
    rw [dmk_mul]
    simp [dmk_one]
  refine ⟨⟨dmk 1 (-X), dmk 1 X, hinv, hinv'⟩, fun g => ?_⟩
  have hp : ((W.pushRep (algebraMap K (DualNumber K)) ρ g : GL (Fin n) (DualNumber K)) : Matrix (Fin n) (Fin n) (DualNumber K)) = dmk (ρ g : Matrix (Fin n) (Fin n) K) 0 := by
    ext i j
    · simp [W.pushRep, TrivSqZeroExt.algebraMap_eq_inl]
      rfl
    · simp [W.pushRep, TrivSqZeroExt.algebraMap_eq_inl]
      rfl
  have hyg : y g * (ρ g : Matrix (Fin n) (Fin n) K) = 1 * (ρ g : Matrix (Fin n) (Fin n) K) * X + (1 * 0 + -X * (ρ g : Matrix (Fin n) (Fin n) K)) * 1 := by
    rw [hy g]
    simp only [Loc.adGL, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, sub_mul, mul_assoc, ← Matrix.coe_units_inv, Units.inv_mul, mul_one, one_mul, mul_zero, zero_add, neg_mul, sub_eq_add_neg]
    rw [add_mul, mul_assoc, mul_assoc, Units.inv_mul, mul_one, neg_mul]
  ext i j : 2
  rw [Units.val_mul, Units.val_mul, hp, Units.inv_mk]
  rw [dmk_mul, dmk_mul, hT g i j, ← hyg]
  simp only [one_mul, mul_one]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.CotDer
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Eb.cotDer :
    ∀ (O R : Type) [CommRing O] [IsDomain O] [CharZero O] [CommRing R] [IsLocalRing R] [Algebra O R], Function.Injective (algebraMap O (ResidueField R)) → Algebra.IsAlgebraic O (ResidueField R) →
        ∃ d : Derivation O R (CotangentSpace R), ∀ a : maximalIdeal R, d a = (maximalIdeal R).toCotangent a := by
  intro O R _ _ _ _ _ _ hinj halg
  haveI : FaithfulSMul O (ResidueField R) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  letI : Algebra (FractionRing O) (ResidueField R) := FractionRing.liftAlgebra O _
  haveI := FractionRing.isScalarTower_liftAlgebra O (ResidueField R)
  haveI := halg
  haveI : Algebra.IsAlgebraic (FractionRing O) (ResidueField R) :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective O (FractionRing O))
  haveI : Algebra.FormallyEtale (FractionRing O) (ResidueField R) := Algebra.FormallyEtale.of_isSeparable _ _
  haveI : Algebra.FormallyEtale O (FractionRing O) := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors O)
  haveI : Algebra.FormallyEtale O (ResidueField R) := Algebra.FormallyEtale.comp O (FractionRing O) _
  have hle : maximalIdeal R ^ 2 ≤ maximalIdeal R := Ideal.pow_le_self two_ne_zero
  let g : R ⧸ maximalIdeal R ^ 2 →ₐ[O] ResidueField R := Ideal.Quotient.factorₐ O hle
  have hgmk : ∀ a : R, g (Ideal.Quotient.mk _ a) = residue R a := fun a => rfl
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨a, rfl⟩ := residue_surjective x
    exact ⟨_, hgmk a⟩
  have hker : ∀ x, g x = 0 → x ∈ (maximalIdeal R).cotangentIdeal := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hgmk, residue_eq_zero_iff] at hx
    exact Ideal.mk_mem_cotangentIdeal.mpr hx
  have hnil : IsNilpotent (RingHom.ker (g : R ⧸ maximalIdeal R ^ 2 →+* ResidueField R)) := by
    refine ⟨2, le_bot_iff.mp ?_⟩
    refine (Ideal.pow_right_mono (fun x hx => hker x hx) 2).trans ?_
    rw [Ideal.cotangentIdeal_square]
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id O (ResidueField R)) g hg hnil
  have hs : ∀ x, g (s x) = x := fun x => Algebra.FormallySmooth.liftOfSurjective_apply _ g hg hnil x
  let φ := s.comp (IsScalarTower.toAlgHom O R (ResidueField R))
  have e : (Ideal.Quotient.mkₐ O (maximalIdeal R).cotangentIdeal).comp φ
      = IsScalarTower.toAlgHom O R ((R ⧸ maximalIdeal R ^ 2) ⧸ (maximalIdeal R).cotangentIdeal) := by
    ext r
    show Ideal.Quotient.mk _ (s (algebraMap R (ResidueField R) r))
      = Ideal.Quotient.mk _ (Ideal.Quotient.mk (maximalIdeal R ^ 2) r)
    rw [Ideal.Quotient.eq]
    apply hker
    rw [map_sub, hs, hgmk, ResidueField.algebraMap_eq, sub_self]
  let D := derivationToSquareZeroOfLift (maximalIdeal R).cotangentIdeal
    (Ideal.cotangentIdeal_square _) φ e
  refine ⟨-(((maximalIdeal R).cotangentEquivIdeal.symm :
      (maximalIdeal R).cotangentIdeal →ₗ[R] (maximalIdeal R).Cotangent).compDer D), fun a => ?_⟩
  have hφ : φ a = 0 := by
    show s (algebraMap R (ResidueField R) a) = 0
    rw [ResidueField.algebraMap_eq, (residue_eq_zero_iff _).mpr a.2, map_zero]
  show -((maximalIdeal R).cotangentEquivIdeal.symm (D a)) = _
  rw [neg_eq_iff_eq_neg, ← map_neg, LinearEquiv.symm_apply_eq]
  ext
  simp only [D, derivationToSquareZeroOfLift_apply, hφ, zero_sub, Ideal.cotangentEquivIdeal_apply, map_neg,
    Submodule.coe_neg, Ideal.toCotangent_to_quotient_square]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DblRep
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private def dblMat {K H : Type} [Field K] [TopologicalSpace K] [Group H] [TopologicalSpace H] {n : ℕ}
    (ρ : H →* GL (Fin n) K) (y : H → Matrix (Fin n) (Fin n) K)
    (hy : ∀ g h, y (g * h) = y g + Loc.adGL ρ g (y h)) : H →* Matrix (Fin (n + n)) (Fin (n + n)) K where
  toFun g := Matrix.reindexAlgEquiv K K finSumFinEquiv
    (Matrix.fromBlocks (ρ g : Matrix (Fin n) (Fin n) K) (y g * (ρ g : Matrix (Fin n) (Fin n) K)) 0 (ρ g : Matrix (Fin n) (Fin n) K))
  map_one' := by
    have h1 : y 1 = 0 := by
      have := hy 1 1
      simpa using this
    simp only [map_one, Units.val_one, h1, Matrix.zero_mul, Matrix.fromBlocks_one]
  map_mul' g h := by
    rw [← map_mul, Matrix.fromBlocks_multiply, hy]
    congr 2
    · simp
    · simp only [Loc.adGL, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, map_mul, Units.val_mul,
        Matrix.add_mul, Matrix.mul_assoc, Units.inv_mul_cancel_left]
      exact add_comm _ _
    · simp
    · simp

theorem UpperTheory.V.Ws.Eb.dblRep :
    ∀ {K H : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {n : ℕ} (ρ : H →* GL (Fin n) K), Continuous ρ → ∀ y ∈ Z1 (Loc.adGL ρ),
        ∃ ρ₂ : H →* GL (Fin (n + n)) K, Continuous ρ₂ ∧ (∀ g, (W.mat ρ₂ g).charpoly = (W.mat ρ g).charpoly ^ 2) ∧ ∀ g, ρ₂ g = 1 → y g = 0 := by
  intro K H _ _ _ _ _ _ n ρ hρ y hy
  obtain ⟨hyc, hyco⟩ := hy
  let D := dblMat ρ y hyco
  have hρv : Continuous (fun g => (ρ g : Matrix (Fin n) (Fin n) K)) := Units.continuous_val.comp hρ
  have hblk : Continuous (fun g => Matrix.fromBlocks (ρ g : Matrix (Fin n) (Fin n) K)
      (y g * (ρ g : Matrix (Fin n) (Fin n) K)) 0 (ρ g : Matrix (Fin n) (Fin n) K)) :=
    Continuous.matrix_fromBlocks hρv (hyc.matrix_mul hρv) continuous_const hρv
  have hDc : Continuous (fun g => D g) := by
    have e : (fun g => D g) = fun g => (Matrix.fromBlocks (ρ g : Matrix (Fin n) (Fin n) K)
        (y g * (ρ g : Matrix (Fin n) (Fin n) K)) 0 (ρ g : Matrix (Fin n) (Fin n) K)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := by
      funext g
      rfl
    rw [e]
    exact hblk.matrix_submatrix _ _
  refine ⟨D.toHomUnits, ?_, ?_, ?_⟩
  · refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact hDc
    · have e : (fun g => ((D.toHomUnits g)⁻¹ : GL (Fin (n + n)) K).val) = fun g => D g⁻¹ := by
        funext g
        rw [← map_inv, MonoidHom.coe_toHomUnits]
      rw [e]
      exact hDc.comp continuous_inv
  · intro g
    show (D g).charpoly = ((ρ g : Matrix (Fin n) (Fin n) K)).charpoly ^ 2
    simp only [D, dblMat, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindexAlgEquiv_apply,
      Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₂₁, pow_two]
  · intro g hg
    have h1 : D g = 1 := by
      rw [← MonoidHom.coe_toHomUnits D g, hg, Units.val_one]
    have h2 : Matrix.fromBlocks (ρ g : Matrix (Fin n) (Fin n) K) (y g * (ρ g : Matrix (Fin n) (Fin n) K))
        0 (ρ g : Matrix (Fin n) (Fin n) K) = Matrix.fromBlocks 1 0 0 1 := by
      rw [Matrix.fromBlocks_one]
      apply (Matrix.reindexAlgEquiv K K finSumFinEquiv).injective
      rw [map_one]
      exact h1
    obtain ⟨-, hB, -, -⟩ := Matrix.fromBlocks_inj.mp h2
    calc y g = y g * (ρ g : Matrix (Fin n) (Fin n) K) * ((ρ g)⁻¹ : GL (Fin n) K) := by
          rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = 0 := by rw [hB, Matrix.zero_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DetRep
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Eb.detRep :
    ∀ {A k G : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [Field k] (f : A →+* k) [IsLocalHom f] [Group G] {n : ℕ} (D : W.GDet n A G) (ρ : G →* GL (Fin n) k), 1 ≤ n → Function.Surjective f → Full ρ → D.map f = W.GDet.ofRep (W.mat ρ) →
        ∃ ρ' : G →* GL (Fin n) A, D = W.GDet.ofRep (W.mat ρ') ∧ W.pushRep f ρ' = ρ ∧ Full ρ' :=
  _root_.UpperTheory.Reformulated.B.CayleyHamiltonSymmetric.detRep
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DimLeOfInt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem dim_le_of_int (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A] :
    ringKrullDim A ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R A)) fun _ _ h =>
    Ideal.IsIntegral.comap_lt_comap (R := R) h

theorem UpperTheory.V.Ws.Eb.htLow :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (N : ℕ) (T : Type) [CommRing T] [IsDomain T] [Algebra c.O T] [IsCO c.O T] (f : MvPowerSeries (Fin N) c.O →ₐ[c.O] T), Function.Injective f → (f : MvPowerSeries (Fin N) c.O →+* T).Finite → ∀ x : T →ₐ[c.O] PadicAlgCl l, (N : ℕ∞) ≤ (RingHom.ker x).height := by
  intro l _ c N T _ _ _ _ f hinj hfin x
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1
  haveI : Algebra.IsAlgebraic ℤ_[l] (PadicAlgCl l) :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ_[l]) (K := ℚ_[l])).2 inferInstance
  haveI : Algebra.IsAlgebraic c.O (PadicAlgCl l) :=
    Algebra.IsAlgebraic.extendScalars (R := ℤ_[l]) (UpperTheory.V.Base.dvrFacts l c.O).1
  haveI : FaithfulSMul c.O (PadicAlgCl l) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  haveI := UpperTheory.V.W.exists_algebraicPoint_of_groupDeterminant c.O T (PadicAlgCl l) x
  haveI : (RingHom.ker x).IsPrime := RingHom.ker_isPrime _
  have h1 := UpperTheory.V.Alg.co_caten c.O T (RingHom.ker x)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have h2 := (UpperTheory.V.AlgebraTools.mvPowerSeries_cotInd c.O ϖ hϖ (Fin N)).2.1
  have h3 : ringKrullDim T = ringKrullDim (MvPowerSeries (Fin N) c.O) := by
    letI : Algebra (MvPowerSeries (Fin N) c.O) T := (f : MvPowerSeries (Fin N) c.O →+* T).toAlgebra
    haveI : Module.Finite (MvPowerSeries (Fin N) c.O) T := hfin
    exact ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj
  have h4 : ringKrullDim (T ⧸ RingHom.ker x) ≤ 1 := by
    rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange x).toRingEquiv,
      ← IsDiscreteValuationRing.ringKrullDim_eq_one c.O]
    exact dim_le_of_int c.O x.range
  rw [h3, h2, Fintype.card_fin] at h1
  have h5 : ((N + 1 : ℕ) : WithBot ℕ∞) ≤ ((RingHom.ker x).height : WithBot ℕ∞) + 1 := by
    rw [← h1]; exact add_le_add le_rfl h4
  have h6 : (N : ℕ∞) + 1 ≤ (RingHom.ker x).height + 1 := by exact_mod_cast h5
  exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 h6
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.LamIso
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem pushCh_comp_alg {H O A B C : Type} [Group H] [CommRing O] [CommRing A] [CommRing B] [CommRing C]
    [Algebra O A] [Algebra O B] [Algebra O C] (f : A →ₐ[O] B) (g : B →ₐ[O] C) (χ : H →* Aˣ) :
    W.pushCh ((g.comp f : A →ₐ[O] C) : A →+* C) χ = W.pushCh (g : B →+* C) (W.pushCh (f : A →+* B) χ) := by
  ext s
  rfl

private theorem pushCh_id_alg {H O A : Type} [Group H] [CommRing O] [CommRing A] [Algebra O A] (χ : H →* Aˣ) :
    W.pushCh ((AlgHom.id O A : A →ₐ[O] A) : A →+* A) χ = χ := by
  ext s
  rfl

theorem UpperTheory.V.Ws.Eb.lamIso :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : W.Resid F O n} (Λ Λ' : W.LamObj r), Nonempty (Λ.Λ ≃ₐ[O] Λ'.Λ) := by
  intro l _ F O _ _ _ n r Λ Λ'
  obtain ⟨f, hf, -⟩ := Λ.univ Λ'.Λ Λ'.κ Λ'.inert
  obtain ⟨g, hg, -⟩ := Λ'.univ Λ.Λ Λ.κ Λ.inert
  refine ⟨AlgEquiv.ofAlgHom f g ?_ ?_⟩
  · exact (Λ'.univ Λ'.Λ Λ'.κ Λ'.inert).unique
      (fun v i => by rw [pushCh_comp_alg, hg, hf]) (fun v i => pushCh_id_alg _)
  · exact (Λ.univ Λ.Λ Λ.κ Λ.inert).unique
      (fun v i => by rw [pushCh_comp_alg, hf, hg]) (fun v i => pushCh_id_alg _)
end

