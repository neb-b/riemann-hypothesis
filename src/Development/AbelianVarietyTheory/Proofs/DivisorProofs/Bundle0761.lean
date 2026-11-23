module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0741
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeterminingLattice
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.DecoClassCount


open scoped TensorProduct in
theorem exists_span_quot {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    ∃ v : Fin (Module.finrank R N) → N ⧸ (I • ⊤ : Submodule R N),
      Submodule.span R (Set.range v) = ⊤ := by
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N)
    (fun P => by
      have := P.isMaximal
      let : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
      rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
        ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]
      have h1 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
      exact h1)
  refine ⟨(TensorProduct.quotTensorEquivQuotSMul N I) ∘ b, ?_⟩
  have h1 : Submodule.span R (Set.range b) = ⊤ := by
    rw [← Submodule.restrictScalars_span R (R ⧸ I) Ideal.Quotient.mk_surjective, b.span_eq,
      Submodule.restrictScalars_top]
  have h2 := congrArg (Submodule.map (TensorProduct.quotTensorEquivQuotSMul N I).toLinearMap) h1
  rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h2
  rw [Set.range_comp]
  exact h2

theorem exists_determining {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    ∃ v : Fin (Module.finrank R N) → N, ∀ f g : N →ₗ[R] R ⧸ I, (∀ i, f (v i) = g (v i)) → f = g := by
  obtain ⟨v, hv⟩ := exists_span_quot (R := R) (N := N) I
  choose u hu using fun i => Submodule.Quotient.mk_surjective _ (v i)
  have hk : ∀ f : N →ₗ[R] R ⧸ I, (I • ⊤ : Submodule R N) ≤ LinearMap.ker f := by
    intro f
    refine Submodule.smul_le.2 fun a ha x _ => ?_
    rw [LinearMap.mem_ker, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]
  refine ⟨u, fun f g hfg => ?_⟩
  have : Submodule.liftQ _ f (hk f) = Submodule.liftQ _ g (hk g) :=
    LinearMap.ext_on_range hv fun i => by
      rw [← hu i]
      exact hfg i
  ext x
  simpa using LinearMap.congr_fun this (Submodule.Quotient.mk x)

theorem finrank_of_span_top {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (p : Submodule (𝓞 K) V)
    (h : Submodule.span K (p : Set V) = ⊤) : Module.finrank (𝓞 K) p = Module.finrank K V := by
  have : IsLocalizedModule (nonZeroDivisors (𝓞 K)) p.subtype := by
    refine ⟨fun s => ?_, fun y => ?_, fun {a b} hab => ⟨1, by simpa using hab⟩⟩
    · have := isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K
      exact IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 K)) (LinearMap.id : V →ₗ[𝓞 K] V) s
    · have hy : y ∈ Submodule.span K (p : Set V) := h ▸ Submodule.mem_top
      obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ y hy
      rw [Submodule.span_eq] at ht
      exact ⟨(⟨_, ht⟩, t), rfl⟩
  rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 K)) p.subtype le_rfl,
    IsFractionRing.finrank_right_eq (𝓞 K) K V]

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def IsLocForm (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n))
    (φ : Sp E n → 𝓞 E ⧸ P.asIdeal) : Prop :=
  (∀ x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N, ∀ y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N, φ (x + y) = φ x + φ y) ∧
  ∀ (a : 𝓞 E), ∀ x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N, φ (a • x) = Ideal.Quotient.mk P.asIdeal a * φ x


omit [StarRing E] in
theorem exists_determining_lattice (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n))
    (hN : Submodule.IsLattice E N) :
    ∃ v : Fin n → Sp E n, ∀ φ ψ, IsLocForm P N φ → IsLocForm P N ψ → (∀ i, φ (v i) = ψ (v i)) →
      ∀ x ∈ N, φ x = ψ x := by
  have : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 (Submodule.IsLattice.fg (self := hN))
  have : Module.FinitePresentation (𝓞 E) N := Module.finitePresentation_of_finite _ _
  have : Module.Flat (𝓞 E) N := inferInstance
  have : Module.Projective (𝓞 E) N := Module.Flat.projective_of_finitePresentation
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have hr : Module.finrank (𝓞 E) N ≤ n := by
    letI : Submodule.IsLattice E N := hN
    rw [← Submodule.IsLattice.finrank_span_eq_finrank E N]
    simpa using Submodule.finrank_le (Submodule.span E (N : Set (Sp E n)))
  obtain ⟨v, hv⟩ := exists_determining (R := 𝓞 E) (N := N) P.asIdeal
  have hle : N ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N := fun x hx =>
    ⟨1, P.asIdeal.primeCompl.one_mem, by simpa using hx⟩
  let lin : ∀ φ, IsLocForm P N φ → (N →ₗ[𝓞 E] 𝓞 E ⧸ P.asIdeal) := fun φ hφ =>
    { toFun := fun x => φ x
      map_add' := fun x y => hφ.1 x (hle x.2) y (hle y.2)
      map_smul' := fun a x => hφ.2 a x (hle x.2) }
  classical
  refine ⟨fun i => if hi : i.val < Module.finrank (𝓞 E) N then v ⟨i.val, hi⟩ else 0,
    fun φ ψ hφ hψ h x hx => ?_⟩
  have := hv (lin φ hφ) (lin ψ hψ) fun i => by
    change φ (v i) = ψ (v i)
    simpa using h ⟨i.val, lt_of_lt_of_le i.isLt hr⟩
  exact LinearMap.congr_fun this ⟨x, hx⟩

theorem card_fibre_le (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E n)) :
    {d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) | d.1.N = N}.Finite ∧ {d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) | d.1.N = N}.ncard ≤
      (∏ P ∈ ST, Ideal.absNorm P.asIdeal ^ n) * ∏ w ∈ SG, Ideal.absNorm w.asIdeal ^ (n ^ 2) := by
  classical
  rcases Set.eq_empty_or_nonempty {d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) | d.1.N = N} with he | ⟨d0, hd0⟩
  · rw [he]; simp
  have hlat : Submodule.IsLattice E N := by
    have := d0.2.lat
    rwa [show d0.1.N = N from hd0] at this
  choose v hv using fun P => exists_determining_lattice P N hlat
  haveI hfin : ∀ P : HeightOneSpectrum (𝓞 E), Finite (𝓞 E ⧸ P.asIdeal) := fun P =>
    Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  let Φ : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) →
      (∀ P : ST, Fin n → 𝓞 E ⧸ P.1.asIdeal) × (∀ w : SG, Fin n → Fin n → 𝓞 E ⧸ w.1.asIdeal) :=
    fun d => (fun P i => d.1.f P (v P.1 i), fun w i => d.1.be w (v w.1 i))
  have hinj : Set.InjOn Φ {d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) | d.1.N = N} := by
    intro d hd d' hd' hdd
    replace hd : d.1.N = N := hd
    replace hd' : d'.1.N = N := hd'
    have hf : ∀ e : DecoSet (E := E) (n := n) (ST := ST) (SG := SG), e.1.N = N → ∀ P : ST, IsLocForm P.1 N (e.1.f P) := by
      rintro e rfl P
      exact ⟨e.2.f_add P, e.2.f_smul P⟩
    have hb : ∀ e : DecoSet (E := E) (n := n) (ST := ST) (SG := SG), e.1.N = N → ∀ (w : SG) (j : Fin n),
        IsLocForm w.1 N fun x => e.1.be w x j := by
      rintro e rfl w j
      exact ⟨fun x hx y hy => congrFun (e.2.be_add w x hx y hy) j,
        fun a x hx => congrFun (e.2.be_smul w a x hx) j⟩
    apply Subtype.ext
    refine d.2.ext_on d'.2 (hd.trans hd'.symm) (fun P x hx => ?_) (fun w x hx => ?_)
    · exact hv P.1 _ _ (hf d hd P) (hf d' hd' P)
        (fun i => congrFun (congrFun (congrArg Prod.fst hdd) P) i) x (hd ▸ hx)
    · funext j
      exact hv w.1 _ _ (hb d hd w j) (hb d' hd' w j)
        (fun i => congrFun (congrFun (congrFun (congrArg Prod.snd hdd) w) i) j) x (hd ▸ hx)
  refine ⟨Set.Finite.of_finite_image (Set.toFinite _) hinj, ?_⟩
  have hle := Set.ncard_le_ncard_of_injOn Φ (t := Set.univ) (fun _ _ => Set.mem_univ _) hinj
    (Set.toFinite _)
  refine hle.trans (le_of_eq ?_)
  have hc : ∀ P : HeightOneSpectrum (𝓞 E), Nat.card (𝓞 E ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal :=
    fun P => by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [Set.ncard_univ, Nat.card_prod, Nat.card_pi, Nat.card_pi]
  simp only [Nat.card_fun, hc, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul, ← sq]
  rw [Finset.prod_coe_sort ST (fun P => Ideal.absNorm P.asIdeal ^ n),
    Finset.prod_coe_sort SG (fun P => Ideal.absNorm P.asIdeal ^ (n ^ 2))]

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
theorem card_classes_le : ∀ (X : Fields), X.Ok → ∀ (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 X.E))), Finite (MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF X.E n)).prod (⊥ : Subgroup (GLG (E := X.E) (n := n) (SG := SG)))) (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) ∧ (Nat.card (MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF X.E n)).prod (⊥ : Subgroup (GLG (E := X.E) (n := n) (SG := SG)))) (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) : ℝ) ≤ (3 * ((Module.finrank ℚ X.E : ℝ) ^ 2 * (n : ℝ) ^ 4 * (|(discr X.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ X.E : ℝ))) ^ 2)) ^ (3 * Module.finrank ℚ X.E * n ^ 2) * (∏ P ∈ ST, (Ideal.absNorm P.asIdeal : ℝ) ^ n) * ∏ w ∈ SG, (Ideal.absNorm w.asIdeal : ℝ) ^ (n ^ 2) := by
  intro X hX n ST SG
  classical
  have hΓ : ∀ g : UF X.E n, (g, (1 : GLG (E := X.E) (n := n) (SG := SG))) ∈
      (⊤ : Subgroup (UF X.E n)).prod (⊥ : Subgroup (GLG (E := X.E) (n := n) (SG := SG))) := fun g =>
    ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩
  refine ⟨DecoSet.finite_orbits (posStar_of_conj hX.conjE) _ hΓ, ?_⟩
  have := hX.realF
  have := hX.cplxE
  have : Algebra.IsQuadraticExtension X.F X.E := ⟨hX.rankE⟩
  have : IsCMField X.E := IsCMField.ofCMExtension X.F X.E
  have hs : ∀ x : X.E, star x = IsCMField.complexConj X.E x := by
    intro x
    let φ : X.E →+* ℂ := (IsAlgClosed.lift : X.E →ₐ[ℚ] ℂ).toRingHom
    apply φ.injective
    rw [hX.conjE, IsCMField.complexEmbedding_complexConj]
  obtain ⟨Rs, hR, H⟩ := GlobalTheory.exists_finset_decoSet_lattice_reps X.E hs n
  let fib : Submodule (𝓞 X.E) (Sp X.E n) → Finset (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) := fun N =>
    (card_fibre_le ST SG N).1.toFinset
  let B : ℕ := (∏ P ∈ ST, Ideal.absNorm P.asIdeal ^ n) * ∏ w ∈ SG, Ideal.absNorm w.asIdeal ^ (n ^ 2)
  have hfib : ∀ N, (fib N).card ≤ B := fun N => by
    rw [← Set.ncard_eq_toFinset_card _ (card_fibre_le ST SG N).1]
    exact (card_fibre_le ST SG N).2
  have hS : (Rs.biUnion fib).card ≤ Rs.card * B := Finset.card_biUnion_le_card_mul _ _ _ fun N _ => hfib N
  have hsurj : Function.Surjective (fun d : ↥(Rs.biUnion fib) => (Quotient.mk'' d.1 :
      MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF X.E n)).prod (⊥ : Subgroup (GLG (E := X.E) (n := n) (SG := SG))))
        (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)))) := by
    intro c
    induction c using Quotient.inductionOn' with
    | h d =>
      obtain ⟨g, hg⟩ := H ST SG d
      refine ⟨⟨(g, (1 : GLG (E := X.E) (n := n) (SG := SG))) • d, Finset.mem_biUnion.2 ⟨_, hg, ?_⟩⟩, ?_⟩
      · exact (Set.Finite.mem_toFinset _).2 rfl
      · apply Quotient.sound'
        rw [MulAction.orbitRel_apply]
        exact ⟨⟨(g, 1), hΓ g⟩, rfl⟩
  have h1 := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_eq_fintype_card (α := ↥(Rs.biUnion fib)), Fintype.card_coe] at h1
  have h2 : ((Rs.card * B : ℕ) : ℝ) = Rs.card * (∏ P ∈ ST, (Ideal.absNorm P.asIdeal : ℝ) ^ n) *
      ∏ w ∈ SG, (Ideal.absNorm w.asIdeal : ℝ) ^ (n ^ 2) := by
    simp only [B]
    push_cast
    ring
  refine (Nat.cast_le.2 (h1.trans hS)).trans (h2.le.trans ?_)
  gcongr

end GlobalTheory.DecoClassCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqOnMirabolicFin
section
noncomputable section

open Matrix Topology GlobalTheory.SmGL GlobalTheory.Whittaker

namespace GlobalTheory.JSW.KirFin

theorem mem_of_separates {X : Type} [TopologicalSpace X] [CompactSpace X] (A : Subalgebra ℂ (X → ℂ))
    (hA : ∀ a ∈ A, IsLocallyConstant a) (hs : ∀ x y, x ≠ y → ∃ a ∈ A, a x ≠ a y) {f : X → ℂ}
    (hf : IsLocallyConstant f) : f ∈ A := by
  classical
  have hind : ∀ a ∈ A, ∀ c : ℂ, (fun x => if a x = c then (1 : ℂ) else 0) ∈ A := by
    intro a ha c
    have hfin := (hA a ha).range_finite
    have e : (fun x => if a x = c then (1 : ℂ) else 0) =
        ∏ d ∈ hfin.toFinset.erase c, (c - d)⁻¹ • (a - algebraMap ℂ (X → ℂ) d) := by
      funext x
      simp only [Finset.prod_apply, Pi.smul_apply, Pi.sub_apply, Pi.algebraMap_apply, smul_eq_mul,
        Algebra.algebraMap_self, RingHom.id_apply]
      split_ifs with h
      · refine (Finset.prod_eq_one fun d hd => ?_).symm
        rw [h]
        exact inv_mul_cancel₀ (sub_ne_zero.2 (Finset.ne_of_mem_erase hd).symm)
      · exact (Finset.prod_eq_zero (i := a x) (by simp [h]) (by simp)).symm
    rw [e]
    exact A.prod_mem fun d _ => A.smul_mem (A.sub_mem ha (A.algebraMap_mem d)) _
  have hcl : ∀ a : X → ℂ, IsLocallyConstant a → IsClopen {p : X × X | a p.1 ≠ a p.2} := fun a ha => by
    have h1 : IsLocallyConstant fun p : X × X => a p.1 - a p.2 :=
      (ha.comp_continuous continuous_fst).sub (ha.comp_continuous continuous_snd)
    convert (h1.isClopen_fiber 0).compl using 1
    ext p
    simp [sub_eq_zero]
  obtain ⟨t, ht⟩ := (hcl f hf).isClosed.isCompact.elim_finite_subcover
    (fun a : A => {p : X × X | a.1 p.1 ≠ a.1 p.2}) (fun a => (hcl _ (hA _ a.2)).isOpen) (by
      intro p hp
      obtain ⟨a, ha, h⟩ := hs p.1 p.2 fun h => hp (by rw [h])
      exact Set.mem_iUnion.2 ⟨⟨a, ha⟩, h⟩)
  let T : X → (t → ℂ) := fun x a => a.1.1 x
  have hT : ∀ x y, T x = T y → f x = f y := fun x y h => by
    by_contra hne
    obtain ⟨a, ha, h'⟩ := Set.mem_iUnion₂.1 (ht (show (x, y) ∈ _ from hne))
    exact h' (congrFun h ⟨a, ha⟩)
  have hfin : (Set.range T).Finite :=
    (Set.Finite.pi' fun a : t => (hA _ a.1.2).range_finite).subset (by rintro _ ⟨x, rfl⟩ a; exact ⟨x, rfl⟩)
  let v : (t → ℂ) → ℂ := fun c => if h : c ∈ Set.range T then f h.choose else 0
  have e : f = ∑ c ∈ hfin.toFinset, v c • ∏ a : t, fun x => if a.1.1 x = c a then (1 : ℂ) else 0 := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, Finset.prod_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (T x)]
    · have hx : T x ∈ Set.range T := ⟨x, rfl⟩
      simp only [v, dif_pos hx, T, if_true, Finset.prod_const_one, mul_one]
      exact (hT _ _ hx.choose_spec).symm
    · intro c _ hc
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hc
      rw [Finset.prod_eq_zero (Finset.mem_univ a) (if_neg (Ne.symm ha)), mul_zero]
    · intro h
      exact (h (hfin.mem_toFinset.mpr ⟨x, rfl⟩)).elim
  rw [e]
  exact A.sum_mem fun c _ => A.smul_mem (A.prod_mem fun a _ => hind _ a.1.2 _) _

variable {F : Type} [NormedField F]

theorem isEmbedding_coe {n : Type} [Fintype n] [DecidableEq n] : IsEmbedding (fun g : GL n F => g.val) := by
  refine Units.isEmbedding_val_mk' (f := fun A : Matrix n n F => A⁻¹) (fun A hA => ?_) fun u => by simp
  refine (continuousAt_matrix_inv A ?_).continuousWithinAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero

variable {m : ℕ}

def lr (g : GL (Fin (m + 1)) F) : Fin (m + 1) → F := g.val (Fin.last m)

theorem lr_mul (g h : GL (Fin (m + 1)) F) : lr (g * h) = lr g ᵥ* h.val := rfl

theorem lr_mul_congr {a b : GL (Fin (m + 1)) F} (h : lr a = lr b) (c : GL (Fin (m + 1)) F) :
    lr (a * c) = lr (b * c) := by rw [lr_mul, lr_mul, h]

theorem continuous_lr : Continuous (lr : GL (Fin (m + 1)) F → _) :=
  continuous_pi fun j => Units.continuous_val.matrix_elem (Fin.last m) j

theorem lr_eq_iff {g : GL (Fin (m + 1)) F} :
    lr g = lr 1 ↔ ∀ j, g.val (Fin.last m) j = if j = Fin.last m then 1 else 0 := by
  simp [lr, funext_iff, Matrix.one_apply, eq_comm]

theorem lr_of_mem {u : GL (Fin (m + 1)) F} (hu : u ∈ unipB F (Fin (m + 1))) : lr u = lr 1 := by
  rw [mem_unipB] at hu
  refine lr_eq_iff.2 fun j => ?_
  split_ifs with h
  · rw [h]; exact hu.2 _
  · exact hu.1 _ _ (Fin.lt_last_iff_ne_last.2 h)

def mirM (A : Matrix (Fin m) (Fin m) F) (x : Fin m → F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
  Matrix.of fun i j => Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j) (fun i => Fin.lastCases (x i) (fun j => A i j) j) i

section
variable (A : Matrix (Fin m) (Fin m) F) (x : Fin m → F)
@[simp] theorem mirM_cc (i j : Fin m) : mirM A x i.castSucc j.castSucc = A i j := by simp [mirM]
@[simp] theorem mirM_cl (i : Fin m) : mirM A x i.castSucc (Fin.last m) = x i := by simp [mirM]
@[simp] theorem mirM_lc (j : Fin m) : mirM A x (Fin.last m) j.castSucc = 0 := by simp [mirM]
@[simp] theorem mirM_ll : mirM A x (Fin.last m) (Fin.last m) = 1 := by simp [mirM]
end

theorem mirM_mul (A B : Matrix (Fin m) (Fin m) F) (x y : Fin m → F) :
    mirM A x * mirM B y = mirM (A * B) (A *ᵥ y + x) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, mulVec, dotProduct]

theorem mirM_one : mirM (1 : Matrix (Fin m) (Fin m) F) 0 = 1 := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

theorem continuous_mirM {Y : Type} [TopologicalSpace Y] {A : Y → Matrix (Fin m) (Fin m) F} {x : Y → Fin m → F}
    (hA : Continuous A) (hx : Continuous x) : Continuous fun y => mirM (A y) (x y) := by
  refine continuous_matrix fun i j => ?_
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp only [mirM_cc, mirM_cl, mirM_lc, mirM_ll]
  exacts [continuous_const, continuous_const, (continuous_apply _).comp hx, hA.matrix_elem _ _]

def mir (h : GL (Fin m) F) (x : Fin m → F) : GL (Fin (m + 1)) F :=
  ⟨mirM h.val x, mirM (h⁻¹).val (-((h⁻¹).val *ᵥ x)), by
    rw [mirM_mul, mulVec_neg, mulVec_mulVec, Units.mul_inv, one_mulVec, neg_add_cancel, mirM_one], by
    rw [mirM_mul, Units.inv_mul, add_neg_cancel, mirM_one]⟩

@[simp] theorem mir_val (h : GL (Fin m) F) (x : Fin m → F) : (mir h x).val = mirM h.val x := rfl

theorem mir_mul (g h : GL (Fin m) F) (x y : Fin m → F) : mir g x * mir h y = mir (g * h) (g.val *ᵥ y + x) :=
  Units.ext (mirM_mul _ _ _ _)

theorem mir_one : mir (1 : GL (Fin m) F) 0 = 1 := Units.ext mirM_one

theorem mir_eq (h : GL (Fin m) F) (x : Fin m → F) : mir h x = mir 1 x * mir h 0 := by simp [mir_mul]

def cor : GL (Fin m) F →* GL (Fin (m + 1)) F where
  toFun h := mir h 0
  map_one' := mir_one
  map_mul' g h := by simp [mir_mul]

theorem continuous_cor : Continuous (cor : GL (Fin m) F → _) :=
  isEmbedding_coe.continuous_iff.2 (continuous_mirM Units.continuous_val continuous_const)

theorem continuous_col : Continuous fun x : Fin m → F => mir 1 x :=
  isEmbedding_coe.continuous_iff.2 (continuous_mirM continuous_const continuous_id)

theorem lr_mir (h : GL (Fin m) F) (x : Fin m → F) : lr (mir h x) = lr 1 := by
  funext j
  induction j using Fin.lastCases <;> simp [lr, Matrix.one_apply, (Fin.castSucc_ne_last _).symm]

theorem eq_mirabolicMatrix_of_lastRow_eq {p : GL (Fin (m + 1)) F} (hp : lr p = lr 1) :
    p.val = mirM (p.val.submatrix Fin.castSucc Fin.castSucc) fun i => p.val i.castSucc (Fin.last m) := by
  rw [lr_eq_iff] at hp
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp [hp, Fin.castSucc_ne_last]

theorem exists_mir {p : GL (Fin (m + 1)) F} (hp : lr p = lr 1) : ∃ h x, p = mir h x := by
  have hq : lr p⁻¹ = lr 1 := by
    have := lr_mul_congr hp p⁻¹
    rw [mul_inv_cancel, one_mul] at this
    exact this.symm
  have h1 : p.val.submatrix Fin.castSucc Fin.castSucc * (p⁻¹).val.submatrix Fin.castSucc Fin.castSucc = 1 := by
    have h2 := p.mul_inv
    rw [eq_mirabolicMatrix_of_lastRow_eq hp, eq_mirabolicMatrix_of_lastRow_eq hq, mirM_mul] at h2
    ext i j
    have := congrFun (congrFun h2 i.castSucc) j.castSucc
    rw [mirM_cc] at this
    rw [this]
    simp [Matrix.one_apply]
  exact ⟨⟨_, _, h1, mul_eq_one_comm.1 h1⟩, _, Units.ext (eq_mirabolicMatrix_of_lastRow_eq hp)⟩

theorem mir_mem_iff {u : GL (Fin m) F} {x : Fin m → F} : mir u x ∈ unipB F (Fin (m + 1)) ↔ u ∈ unipB F (Fin m) := by
  rw [mem_unipB, mem_unipB]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j h => by simpa using h1 i.castSucc j.castSucc (by simpa using h), fun i => by simpa using h2 i.castSucc⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · exact absurd hij (lt_irrefl _)
      · simp
      · exact absurd hij (not_lt.2 (Fin.le_last _))
      · simpa using h1 _ _ (by simpa using hij)
    · induction i using Fin.lastCases <;> simp [h2]

theorem superDiag_mir (u : GL (Fin (m + 1)) F) (x : Fin (m + 1) → F) :
    superDiag (mir u x) = superDiag u + x (Fin.last m) := by
  unfold superDiag
  simp only [Finset.sum_filter]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.sum_univ_castSucc (n := m + 1), mir_val, mirM_cc, mirM_cl, mirM_lc, mirM_ll, Fin.val_castSucc,
    Fin.val_last, Finset.sum_add_distrib]
  have : ∀ i : Fin (m + 1), (m = i.val) ↔ i = Fin.last m := fun i => by simp [Fin.ext_iff, eq_comm]
  simp [this]

theorem superDiag_one' : superDiag (1 : GL (Fin m) F) = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => ?_
  rw [Finset.mem_filter] at hj
  exact Matrix.one_apply_ne fun h => by simp [h] at hj

theorem isCompact_blocks {C : Set (GL (Fin (m + 1)) F)} (hC : IsCompact C) :
    IsCompact {h : GL (Fin m) F | ∃ x, mir h x ∈ C} := by
  rw [isEmbedding_coe.isInducing.isCompact_iff]
  have h1 : IsCompact (C ∩ {p | lr p = lr 1}) := hC.inter_right (isClosed_eq continuous_lr continuous_const)
  convert h1.image (f := fun p : GL (Fin (m + 1)) F => p.val.submatrix Fin.castSucc Fin.castSucc)
    (Units.continuous_val.matrix_submatrix _ _) using 1
  ext A
  constructor
  · rintro ⟨h, ⟨x, hx⟩, rfl⟩
    exact ⟨mir h x, ⟨hx, lr_mir h x⟩, by ext i j; simp⟩
  · rintro ⟨p, ⟨hp, hp'⟩, rfl⟩
    obtain ⟨h, x, rfl⟩ := exists_mir hp'
    exact ⟨h, ⟨x, hp⟩, by ext i j; simp⟩

def Eqv (ψ : AddChar F ℂ) {n : ℕ} (W : GL (Fin n) F → ℂ) : Prop :=
  ∀ u ∈ unipB F (Fin n), ∀ g, W (u * g) = ψ (superDiag u) * W g

theorem Eqv.apply_mir {ψ : AddChar F ℂ} {W : GL (Fin (m + 2)) F → ℂ} (h : Eqv ψ W) (g : GL (Fin (m + 1)) F)
    (x : Fin (m + 1) → F) : W (mir g x) = ψ (x (Fin.last m)) * W (cor g) := by
  rw [mir_eq, h _ (mir_mem_iff.2 (one_mem _)), superDiag_mir, superDiag_one', zero_add]
  rfl

theorem Eqv.res {ψ : AddChar F ℂ} {W : GL (Fin (m + 2)) F → ℂ} (h : Eqv ψ W) :
    Eqv ψ fun x : GL (Fin (m + 1)) F => W (cor x) := fun u hu g => by
  simp only [map_mul]
  rw [h (cor u) (mir_mem_iff.2 hu)]
  change ψ (superDiag (mir u 0)) * _ = _
  rw [superDiag_mir, Pi.zero_apply, add_zero]

end GlobalTheory.JSW.KirFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImmersedClosedOpenIntersection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem GlobalTheory.HomFixMat.exists_immersed_locus : ∀ (Y : Scheme.{0}) [IsNoetherian Y] (Z₁ Z₂ : Scheme.{0}) (ι₁ : Z₁ ⟶ Y) (ι₂ : Z₂ ⟶ Y) (U : Y.Opens), IsClosedImmersion ι₁ → IsClosedImmersion ι₂ → ∃ (W : Scheme.{0}) (j : W ⟶ Y), IsImmersion j ∧ QuasiCompact j ∧ IsLocallyNoetherian W ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Y), ((∃ w : T ⟶ Z₁, w ≫ ι₁ = g) ∧ (∃ w : T ⟶ Z₂, w ≫ ι₂ = g) ∧ ∀ τ, g τ ∈ U) ↔ ∃ w : T ⟶ W, w ≫ j = g := by
  intro Y _ Z₁ Z₂ ι₁ ι₂ U h₁ h₂
  let p : pullback ι₁ ι₂ ⟶ Y := pullback.fst ι₁ ι₂ ≫ ι₁
  let V : (pullback ι₁ ι₂).Opens := p ⁻¹ᵁ U
  let j : V.toScheme ⟶ Y := V.ι ≫ p
  have hj : IsImmersion j := IsImmersion.comp _ _
  have hW : IsLocallyNoetherian V.toScheme := LocallyOfFiniteType.isLocallyNoetherian j
  have hN : TopologicalSpace.NoetherianSpace V.toScheme :=
    (IsPreimmersion.isEmbedding j).isInducing.noetherianSpace
  refine ⟨V.toScheme, j, hj, quasiCompact_of_noetherianSpace_source j, hW, ?_⟩
  intro T g
  constructor
  · rintro ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩, hU⟩
    let f : T ⟶ pullback ι₁ ι₂ := pullback.lift w₁ w₂ (hw₁.trans hw₂.symm)
    have hf : f ≫ p = g := by
      simp only [f, p]; rw [← Category.assoc, pullback.lift_fst]; exact hw₁
    have hr : Set.range f ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨τ, rfl⟩
      show p (f τ) ∈ U
      rw [← Scheme.Hom.comp_apply, hf]
      exact hU τ
    refine ⟨IsOpenImmersion.lift V.ι f hr, ?_⟩
    simp only [j, ← Category.assoc, IsOpenImmersion.lift_fac, hf]
  · rintro ⟨w, rfl⟩
    refine ⟨⟨w ≫ V.ι ≫ pullback.fst ι₁ ι₂, by simp [j, p]⟩,
      ⟨w ≫ V.ι ≫ pullback.snd ι₁ ι₂, by simp [j, p, pullback.condition]⟩, ?_⟩
    intro τ
    have : V.ι (w τ) ∈ V := by
      have h := Scheme.Opens.range_ι V
      exact (Set.ext_iff.mp h (V.ι (w τ))).mp ⟨_, rfl⟩
    exact this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaRestrictFiniteAbelianUnramifiedEqOneStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_restrict_finiteAbelian_unramified_eq_one : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L) (v : HeightOneSpectrum (𝓞 K)), IsUnramifiedIn K v L → ∀ (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ σ : Formalism.ConjugateSelfDual.G K Ω, σ ∈ ReciprocityTheory.Gal.Ine (F := K) A → haveI := h.isGalois; AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) = 1 := by
  first | exact @GlobalTheory.InertiaRestrict.restrict_eq_one | exact GlobalTheory.InertiaRestrict.restrict_eq_one | (intros; apply GlobalTheory.InertiaRestrict.restrict_eq_one <;> assumption)
end

