module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0116
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0117
public import Formalism.RealPlaceAnalysis.FinalF

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryOfFiniteSupport
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem exists_adelic_of_finset {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hh : ∀ v, h v ∈ UPts σ J (v.adicCompletion F)) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ x ∈ UPts σ J (Ad F), (∀ v ∈ S, bc (prV (E := E) v) x = h v) ∧
      ∀ v ∉ S, bc (prV (E := E) v) x = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp, fun v _ => map_one _⟩
  | insert w S hw ih =>
    obtain ⟨x, hx, h1, h2⟩ := ih
    have hne : ∀ v, v ≠ w →
        bc (prV (E := E) v) (Formalism.UG.P.afsplitU w (h w) x) = bc (prV (E := E) v) x := fun v hv =>
      Units.ext (Formalism.UG.P.afsplitC_prV_ne w v hv _ _)
    refine ⟨Formalism.UG.P.afsplitU w (h w) x, Formalism.UG.P.afsplitU_mem w σ J _ _ (hh w) hx, ?_, ?_⟩
    · intro v hv
      by_cases e : v = w
      · subst e
        exact Units.ext (Formalism.UG.P.afsplitC_prV v _ _)
      · rw [hne v e]
        exact h1 v ((Finset.mem_insert.1 hv).resolve_left e)
    · intro v hv
      rw [Finset.mem_insert, not_or] at hv
      rw [hne v hv.1]
      exact h2 v hv.2

theorem exists_adelic_of_finite_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (h : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (E ⊗[F] v.adicCompletion F)), (∀ v, h v ∈ UPts σ J (v.adicCompletion F)) → {v | h v ≠ 1}.Finite → ∃ x ∈ UPts σ J (Ad F), ∀ v, bc (prV (E := E) v) x = h v := by
  intro F E _ _ _ _ _ n σ J h hh hf
  obtain ⟨x, hx, h1, h2⟩ := exists_adelic_of_finset σ J h hh hf.toFinset
  refine ⟨x, hx, fun v => ?_⟩
  by_cases hv : v ∈ hf.toFinset
  · exact h1 v hv
  · rw [h2 v hv]
    by_contra e
    exact hv (hf.mem_toFinset.2 fun e' => e e'.symm)

end GlobalTheory.St.G
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjRenumber
section
noncomputable section

namespace GlobalTheory.GLm

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq
open scoped Classical

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {N : ℕ} in
private lemma traceOnCharacter_averagedSingles_eq (g N : ℕ) [Fact g.Prime]
    (Φ : Matrix (Fin N) (Fin N) (ZMod g) → Prop) (E : Matrix (Fin N) (Fin N) (ZMod g) → ZMod g)
    (ψ : AddChar (ZMod g) ℂ) (χ : GL (Fin N) (ZMod g) → ℂ) :
    _root_.GlobalTheory.GLq.tr (_root_.Formalism.MainNotions.ArithmeticCylinders.eDat g N Φ E ψ) χ =
      ((Finset.univ.filter
          (fun u : GL (Fin N) (ZMod g) => Φ (u : Matrix (Fin N) (Fin N) (ZMod g)))).card : ℂ)⁻¹ *
        ∑ u ∈ Finset.univ.filter
            (fun u : GL (Fin N) (ZMod g) => Φ (u : Matrix (Fin N) (Fin N) (ZMod g))),
          (ψ (E u))⁻¹ * χ u := by
  unfold _root_.GlobalTheory.GLq.tr _root_.Formalism.MainNotions.ArithmeticCylinders.eDat
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, Finsupp.smul_apply,
    Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring


open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {N : ℕ} in
theorem _root_.GlobalTheory.GLm.tr_ePat_renumber : ∀ (g : ℕ) [Fact g.Prime]
    (ψ : AddChar (ZMod g) ℂ) (N : ℕ) (Φ E : Fin N → Fin N → Prop)
    (σ : Equiv.Perm (Fin N)) (χ : _root_.GlobalTheory.GLq.Gn g N → ℂ), _root_.GlobalTheory.GLq.IsClass χ →
    _root_.GlobalTheory.GLq.tr (_root_.GlobalTheory.GLm.ePat g N (fun a b => Φ (σ a) (σ b))
      (fun a b => E (σ a) (σ b)) ψ) χ =
      _root_.GlobalTheory.GLq.tr (_root_.GlobalTheory.GLm.ePat g N Φ E ψ) χ := by
  intro g _ ψ N Φ E σ χ hχ
  unfold _root_.GlobalTheory.GLm.ePat
  rw [traceOnCharacter_averagedSingles_eq, traceOnCharacter_averagedSingles_eq]
  set Q : GL (Fin N) (ZMod g) := (Matrix.permMatrixHom (R := ZMod g)).toHomUnits σ⁻¹ with hQdef
  have hQ : ∀ (u : GL (Fin N) (ZMod g)) (x y : Fin N),
      ((Q⁻¹ * u * Q : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) x y =
        (u : Matrix (Fin N) (Fin N) (ZMod g)) (σ.symm x) (σ.symm y) := by
    intro u x y
    have hinv : ((Q⁻¹ : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) =
        (σ⁻¹ : Equiv.Perm (Fin N)).toPEquiv.toMatrix := by
      rw [hQdef]
      show (((σ⁻¹)⁻¹)⁻¹ : Equiv.Perm (Fin N)).toPEquiv.toMatrix = _
      rw [inv_inv]
    have hval : ((Q : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) =
        σ.toPEquiv.toMatrix := by
      rw [hQdef]
      show ((σ⁻¹)⁻¹ : Equiv.Perm (Fin N)).toPEquiv.toMatrix = _
      rw [inv_inv]
    rw [Units.val_mul, Units.val_mul, hinv, hval, PEquiv.toMatrix_toPEquiv_mul,
      PEquiv.mul_toMatrix_toPEquiv]
    rfl
  let e : GL (Fin N) (ZMod g) ≃ GL (Fin N) (ZMod g) := (MulAut.conj Q⁻¹).toEquiv
  have he : ∀ u, e u = Q⁻¹ * u * Q := by
    intro u
    simp [e, MulAut.conj_apply]
  have hmem : ∀ u : GL (Fin N) (ZMod g),
      _root_.GlobalTheory.GLm.InPat (fun a b => Φ (σ a) (σ b)) (u : Matrix (Fin N) (Fin N) (ZMod g)) ↔
        _root_.GlobalTheory.GLm.InPat Φ (e u : Matrix (Fin N) (Fin N) (ZMod g)) := by
    intro u
    unfold _root_.GlobalTheory.GLm.InPat
    simp only [he, hQ]
    constructor
    · intro h x y hxy
      have hxy' := h (σ.symm x) (σ.symm y) (by simpa using hxy)
      rw [hxy', Matrix.one_apply, Matrix.one_apply]
      simp
    · intro h a b hab
      have hab' := h (σ a) (σ b) hab
      simp only [Equiv.symm_apply_apply] at hab'
      rw [hab', Matrix.one_apply, Matrix.one_apply]
      simp
  have hsum : ∀ u : GL (Fin N) (ZMod g),
      _root_.GlobalTheory.GLm.sumAt (fun a b => E (σ a) (σ b)) (u : Matrix (Fin N) (Fin N) (ZMod g)) =
        _root_.GlobalTheory.GLm.sumAt E (e u : Matrix (Fin N) (Fin N) (ZMod g)) := by
    intro u
    unfold _root_.GlobalTheory.GLm.sumAt
    simp only [he, hQ]
    conv_rhs => rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_rhs => rw [← Equiv.sum_comp σ]
    simp only [Equiv.symm_apply_apply]
  congr 1
  · congr 2
    exact Finset.card_equiv e (fun u => by simp [hmem])
  · refine Finset.sum_equiv e (fun u => by simp [hmem]) (fun u _ => ?_)
    rw [hsum, he]
    congr 1
    have hconj := hχ u Q⁻¹
    simpa using hconj.symm

end GlobalTheory.GLm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGLConjLatticePairsCovByDvr
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem exists_equiv_ker_prod {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (ψ : M →ₗ[O] O) (hψ : Function.Surjective ψ) :
    ∃ E : M ≃ₗ[O] (LinearMap.ker ψ × O), ∀ x, (E x).2 = ψ x := by
  obtain ⟨x₀, hx₀⟩ := hψ 1
  let p : M →ₗ[O] LinearMap.ker ψ :=
    LinearMap.codRestrict _ (LinearMap.id - LinearMap.toSpanSingleton O M x₀ ∘ₗ ψ)
      (fun x => by simp [hx₀])
  refine ⟨LinearEquiv.ofLinearMap (p.prod ψ)
    ((LinearMap.ker ψ).subtype.coprod (LinearMap.toSpanSingleton O M x₀)) ?_ ?_, fun x => rfl⟩
  · apply LinearMap.prod_ext
    · ext y
      · simp [p]
      · simp
    · ext
      · simp [p, hx₀]
      · simp [hx₀]
  · ext x
    simp [p]

theorem exists_equiv_comp_eq_of_surjective {O M M' : Type} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    [Module.Free O M] [Module.Finite O M] [Module.Free O M'] [Module.Finite O M']
    (h : Module.finrank O M = Module.finrank O M')
    (ψ : M →ₗ[O] O) (hψ : Function.Surjective ψ)
    (ψ' : M' →ₗ[O] O) (hψ' : Function.Surjective ψ') :
    ∃ e : M ≃ₗ[O] M', ∀ x, ψ' (e x) = ψ x := by
  obtain ⟨E, hE⟩ := exists_equiv_ker_prod ψ hψ
  obtain ⟨E', hE'⟩ := exists_equiv_ker_prod ψ' hψ'
  have hk : Module.finrank O (LinearMap.ker ψ) = Module.finrank O (LinearMap.ker ψ') := by
    have h₁ := E.finrank_eq
    have h₂ := E'.finrank_eq
    rw [Module.finrank_prod, Module.finrank_self] at h₁ h₂
    omega
  obtain ⟨k⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hk
  refine ⟨E.trans ((k.prodCongr (LinearEquiv.refl O O)).trans E'.symm), fun x => ?_⟩
  rw [← hE', ← hE]
  simp

theorem exists_form_of_covBy {O V : Type} [CommRing O] [IsLocalRing O] [AddCommGroup V]
    [Module O V] (A B : Submodule O V) [Module.Projective O B] (h : A ⋖ B) :
    ∃ ψ : B →ₗ[O] O, Function.Surjective ψ ∧
      ∀ x : B, (x : V) ∈ A ↔ ψ x ∈ IsLocalRing.maximalIdeal O := by
  have hs := (covBy_iff_quot_is_simple h.le).1 h
  obtain ⟨I, hI, ⟨f⟩⟩ := isSimpleModule_iff_quot_maximal.1 hs
  obtain rfl := IsLocalRing.eq_maximalIdeal hI
  set m := IsLocalRing.maximalIdeal O
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property m.mkQ
    (f.toLinearMap ∘ₗ (A.comap B.subtype).mkQ) m.mkQ_surjective
  have key : ∀ x, m.mkQ (ψ x) = f ((A.comap B.subtype).mkQ x) := fun x =>
    LinearMap.congr_fun hψ x
  have hmem : ∀ x : B, (x : V) ∈ A ↔ ψ x ∈ m := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero m, ← Submodule.mkQ_apply, key,
      LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.subtype_apply]
  refine ⟨ψ, ?_, hmem⟩
  obtain ⟨y, hy⟩ := f.surjective (m.mkQ 1)
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
  have hu : IsUnit (ψ x) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hx
    have h1 : m.mkQ 1 = 0 := by
      rw [← hy, ← key, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  intro r
  refine ⟨(r * hu.unit⁻¹.1) • x, ?_⟩
  rw [map_smul, smul_eq_mul, mul_assoc, hu.val_inv_mul, mul_one]

theorem exists_extend_latticeEquiv {O K V : Type} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (B B' : Submodule O V) [B.IsFullLattice K] [B'.IsLattice K] (e : B ≃ₗ[O] B') :
    ∃ g : V ≃ₗ[K] V, ∀ x : B, g x = e x := by
  have := Submodule.IsLattice.finite K B
  have := Submodule.IsLattice.free K B
  have : B'.IsFullLattice K := Submodule.IsFullLattice.of_rank_le K B' (by
    rw [← Submodule.IsFullLattice.rank_eq K B, e.rank_eq])
  let b := Module.Free.chooseBasis O B
  let c := b.map e
  let g := (b.extendOfIsFullLattice K).equiv (c.extendOfIsFullLattice K) (Equiv.refl _)
  refine ⟨g, fun x => ?_⟩
  have key : (g.toLinearMap.restrictScalars O) ∘ₗ B.subtype = B'.subtype ∘ₗ e.toLinearMap := by
    refine b.ext fun i => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe, Submodule.coe_subtype, g, c]
    rw [← Module.Basis.extendOfIsFullLattice_apply K b i, Module.Basis.equiv_apply]
    simp
  exact LinearMap.congr_fun key x

theorem exists_conj_of_covBy : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (n : ℕ) (A B A' B' : Submodule O (Fin n → K)), B.FG → B'.FG → Submodule.span K (A : Set (Fin n → K)) = ⊤ → Submodule.span K (A' : Set (Fin n → K)) = ⊤ → A ⋖ B → A' ⋖ B' → ∃ g : GL (Fin n) K, (∀ x, x ∈ A ↔ g.1 *ᵥ x ∈ A') ∧ ∀ x, x ∈ B ↔ g.1 *ᵥ x ∈ B' := by
  intro O K _ _ _ _ _ _ n A B A' B' hB hB' hA hA' h h'
  have : B.IsLattice K := Submodule.IsLattice.of_fg K hB
  have : B'.IsLattice K := Submodule.IsLattice.of_fg K hB'
  have : B.IsFullLattice K :=
    ⟨eq_top_iff.2 (hA ▸ Submodule.span_mono (show (A : Set (Fin n → K)) ⊆ B from h.le))⟩
  have : B'.IsFullLattice K :=
    ⟨eq_top_iff.2 (hA' ▸ Submodule.span_mono (show (A' : Set (Fin n → K)) ⊆ B' from h'.le))⟩
  have : Module.Free O B := Submodule.IsLattice.free K B
  have : Module.Free O B' := Submodule.IsLattice.free K B'
  have : Module.Finite O B := Submodule.IsLattice.finite K B
  have : Module.Finite O B' := Submodule.IsLattice.finite K B'
  have hr : Module.finrank O B = Module.finrank O B' := by
    rw [((Submodule.IsFullLattice.finrank_eq K B).trans (Module.finrank_fintype_fun_eq_card K)), ((Submodule.IsFullLattice.finrank_eq K B').trans (Module.finrank_fintype_fun_eq_card K))]
  obtain ⟨ψ, hψs, hψ⟩ := exists_form_of_covBy A B h
  obtain ⟨ψ', hψs', hψ'⟩ := exists_form_of_covBy A' B' h'
  obtain ⟨e, he⟩ := exists_equiv_comp_eq_of_surjective hr ψ hψs ψ' hψs'
  obtain ⟨g, hg⟩ := exists_extend_latticeEquiv (K := K) B B' e
  have hBg : ∀ x, x ∈ B ↔ g x ∈ B' := by
    intro x
    constructor
    · intro hx
      rw [show g x = e ⟨x, hx⟩ from hg ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).2
    · intro hx
      have hy : ((e.symm ⟨g x, hx⟩ : B) : Fin n → K) = x :=
        g.injective (by rw [hg]; simp)
      rw [← hy]
      exact (e.symm _).2
  have hpt : ∀ x (hx : x ∈ B), (⟨g x, (hBg x).1 hx⟩ : B') = e ⟨x, hx⟩ := fun x hx =>
    Subtype.ext (hg ⟨x, hx⟩)
  let G : GL (Fin n) K :=
    ⟨LinearMap.toMatrix' g.toLinearMap, LinearMap.toMatrix' g.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  have hG : ∀ x, G.1 *ᵥ x = g x := fun x => LinearMap.toMatrix'_mulVec _ x
  refine ⟨G, fun x => ?_, fun x => ?_⟩
  · rw [hG]
    constructor
    · intro hx
      have hxB := h.le hx
      have hgB := (hBg x).1 hxB
      rw [hψ' ⟨g x, hgB⟩, hpt x hxB, he]
      exact (hψ ⟨x, hxB⟩).1 hx
    · intro hx
      have hgB := h'.le hx
      have hxB := (hBg x).2 hgB
      rw [hψ ⟨x, hxB⟩, ← he, ← hpt x hxB]
      exact (hψ' ⟨g x, hgB⟩).1 hx
  · rw [hG]
    exact hBg x

end GlobalTheory.St.G
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIrreducibleCharpolyMemRootsBar
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem exists_irreducible_charpoly_mem_rootsBar (g : ℕ) [Fact g.Prime] (d : ℕ)
    (z : Formalism.CyclotomicNorms.Fbar g) (hz : z ≠ 0) (hd : (minpoly (ZMod g) z).natDegree = d) :
    ∃ y : Gn g d, Irreducible (y : Mt g d).charpoly ∧
      z ∈ Formalism.CyclotomicNorms.rootsBar (y : Mt g d).charpoly := by
  subst hd
  have hi : IsIntegral (ZMod g) z := Algebra.IsIntegral.isIntegral z
  let pb := IntermediateField.adjoin.powerBasis hi
  let M : Mt g (minpoly (ZMod g) z).natDegree := Algebra.leftMulMatrix pb.basis pb.gen
  have hM : M.charpoly = minpoly (ZMod g) z := by
    have h := charpoly_leftMulMatrix pb
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen] at h
    exact h
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hM]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (minpoly.coeff_zero_ne_zero hi hz)
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, ?_, ?_⟩
  · change Irreducible M.charpoly
    rw [hM]
    exact minpoly.irreducible hi
  · change z ∈ Formalism.CyclotomicNorms.rootsBar M.charpoly
    rw [hM, Formalism.CyclotomicNorms.rootsBar, mem_roots_map (minpoly.ne_zero hi), ← aeval_def]
    exact minpoly.aeval _ _

end GlobalTheory.GLm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FgOfHtNeZero
section
open NumberField

noncomputable section

namespace GlobalTheory.StepDualityCompare

open Formalism.MainNotions.S GlobalTheory.Count

theorem totallyComplex (I : AutInst) : IsTotallyComplex I.E := I.cm.cmUnram.1

theorem frm_det (I : AutInst) (x : I.GA) (w : InfinitePlace I.E) : IsUnit (frm I x w).det := by
  have hP : IsUnit (I.P (w.comap (algebraMap I.F I.E))).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit _)
  have hU : IsUnit (uMat (x.1 (w.comap (algebraMap I.F I.E)))).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  have hM : IsUnit (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E)))).det := by
    rw [Matrix.det_mul]
    exact hP.mul hU
  unfold frm
  split_ifs
  · exact hM
  · have e : ((I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E)))).map
        (starRingEnd ℂ)).det = starRingEnd ℂ
        (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E)))).det :=
      (RingHom.map_det _ _).symm
    rw [e]
    exact hM.map _

theorem least_pos (I : AutInst) (x : I.GA) (hfg : (lamX I x).FG) (h0 : lamX I x ≠ ⊥) : 0 < least I x := by
  have := totallyComplex I
  obtain ⟨-, -, -, h4, -⟩ := Formalism.HN.sizeMu I.E (Fin I.n → I.E) (Fin I.n) (bas I) (frm I x) (frm_det I x)
    (lamX I x) hfg h0
  unfold least
  rw [h4]
  exact Real.exp_pos _

private theorem fg_of_le_lamX (I : AutInst) (x : I.GA) (hfg : (lamX I x).FG)
    {S : Submodule (𝓞 I.E) (Fin I.n → I.E)} (h : S ≤ lamX I x) : S.FG := by
  have : IsNoetherian (𝓞 I.E) (lamX I x) := isNoetherian_of_fg_of_noetherian _ hfg
  have : IsNoetherian (𝓞 I.E) S := isNoetherian_of_le h
  exact Module.Finite.iff_fg.mp inferInstance

theorem htQ_pos (I : AutInst) (x : I.GA) (hfg : (lamX I x).FG) (S S' : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (hS : GlobalTheory.IndefiniteRowSideFullHecke.SaturatedPerpDuality.SatIn I x S) (hS' : S' ≤ lamX I x) (h : S ≤ S') :
    0 < Formalism.HN.htQ (bas I) (frm I x) S' S := by
  have := totallyComplex I
  obtain ⟨κ, _, _, b'', X'', hX'', -, hq⟩ := Formalism.HN.quotRealize I.E (Fin I.n → I.E) (Fin I.n) (bas I)
    (frm I x) (frm_det I x) (lamX I x) S hfg hS
  rw [(hq S' h hS').1]
  exact (Formalism.HN.plLat I.E _ κ b'' X'' hX'' _ ((fg_of_le_lamX I x hfg hS').map _)).2.2

end GlobalTheory.StepDualityCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagCoefIntegralOfLocalIntegralStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_coef_integral_of_local_integral : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : StarRing E] {S : HSpace E} {r : ℕ} (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {T : E} (F : LFlag S r T), IsFixedConv Λ g F → ∀ (j : ℕ) (x : S.V), x ∈ Xflag F j → (∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) → ∃ w : Fin r → E, x = ∑ c, w c • F.fl.e c ∧ (∀ c : Fin r, j ≤ c.val → w c = 0) ∧ ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ c, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 E, (s : E) * w c = o := by
  first | exact @GlobalTheory.FlagCoef.coef_integral_of_flag | exact GlobalTheory.FlagCoef.coef_integral_of_flag | (intros; apply GlobalTheory.FlagCoef.coef_integral_of_flag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameAdmissibleOfCongrUnitriangularStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_admissible_of_congr_unitriangular : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : StarRing E] {S : HSpace E} {r : ℕ} (Λ : Submodule (𝓞 E) S.V) (g : ℕ), g ≠ 0 → ∀ {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → M a b = 0) → (∀ a, M a a = 1) → (∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a b, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 E, (s : E) * M a b = o) → (∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a, frame F a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) → (∀ b, ModG S Λ g (frame F' b - ∑ a, M a b • frame F a)) → IsAdmissible Λ g F F' := by
  first | exact @GlobalTheory.admissible_of_congr_unitriangular | exact GlobalTheory.admissible_of_congr_unitriangular | (intros; apply GlobalTheory.admissible_of_congr_unitriangular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtOrbitTens
section
open Formalism.MainNotions.S NumberField GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

namespace GlobalTheory.TensDer

theorem hasDerivAt_orbit_tens : ∀ (B : RowsAut) (E : gInf B) (u u' : ∀ v, B.H v), (∀ v, HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v)) (u' v) 0) → (∀ v, B.σ v 1 = 1) → open Classical in HasDerivAt (orbit B E (B.tens u)) (∑ v, B.tens (Function.update u v (u' v))) 0 := by
  intro B E u u' hd h1
  classical
  obtain ⟨m, hm, -⟩ := GlobalTheory.rowsAut_tens_continuousMultilinear B
  have hfun : orbit B E (B.tens u) =
      fun t => (m.restrictScalars ℝ) (fun v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v) t) := by
    funext t
    have := B.tens_spec.2.1
    rw [ContinuousMultilinearMap.coe_restrictScalars, hm]
    unfold orbit
    rw [this]
    congr 1
  have h0 : (fun v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v) 0) = u := by
    funext v
    simp [GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit, h1]
  have hpi : HasDerivAt (fun t v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v) t) u' 0 :=
    hasDerivAt_pi.2 hd
  have hF := (m.restrictScalars ℝ).hasFDerivAt (fun v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v) 0)
  have := hF.comp_hasDerivAt (0 : ℝ) hpi
  rw [hfun]
  rw [h0, ContinuousMultilinearMap.linearDeriv_apply] at this
  simp only [ContinuousMultilinearMap.coe_restrictScalars, Function.comp_def, hm] at this ⊢
  exact this

end GlobalTheory.TensDer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HilbertSchmidtInUJLeOfSignColumnsStatement
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSchmidt_inUJ_le_of_sign_columns : ∀ (n : ℕ) (ε : Fin n → Bool) (s : Bool) (h : Matrix (Fin n) (Fin n) ℂ), inUJ ε h → hs h ≤ n + 4 * ∑ i, ∑ j ∈ univ.filter (fun j => ε j = s), ‖h i j‖ ^ 2 := by
  first | exact @GlobalTheory.hs_le_of_cols | exact GlobalTheory.hs_le_of_cols | (intros; apply GlobalTheory.hs_le_of_cols <;> assumption)
end

