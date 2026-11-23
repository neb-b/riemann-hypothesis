module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0385
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrPreservesHomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularTopFormPoleOrderHeightOnePrime
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem omB_top_coeff_iff_pole : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.Smooth k B → ∀ τ : DR k K →ₗ[K] K, τ (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 → ∀ (Q : Ideal B), Q.IsPrime → Q.height = 1 → ∀ (t : A) (s : B) (e : ℕ), Irreducible t → 1 ≤ e → s ∈ Q → (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) → (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e) → ∀ z : K, (∃ r : B, r ∉ Q ∧ ∃ y ∈ omB k K B d, τ y = r * z) ↔ ∃ c r : B, r ∉ Q ∧ (r : K) * s ^ (e - 1) * z = c := by
  intro k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB _ τ hτ Q hQ hQh t s e ht he hsQ hQs hts z
  obtain ⟨a₀, r₀, ha₀, hr₀, hrt⟩ := hts
  have htQ : ∀ b : B, (b : K) = algebraMap F K t → b ∈ Q := by
    intro b hb
    have h1 : r₀ * b = a₀ * s ^ e := Subtype.ext (by push_cast; rw [hb]; exact hrt)
    have h2 : r₀ * b ∈ Q := h1 ▸ Q.mul_mem_left _ (Q.pow_mem_of_mem hsQ e (by omega))
    exact (hQ.mem_or_mem h2).resolve_left hr₀
  have hcomap := GlobalTheory.T.mem_heightOne_prime_integralClosure_iff_dvd_irreducible k F K d u hu A hA B hB Q hQ hQh t ht htQ
  obtain ⟨htp, m, rfl, y, hy⟩ := GlobalTheory.T.polynomial_ring_irreducible_prime_reduction k F d u hu A hA t ht
  have hAft : Algebra.FiniteType k A := by
    subst hA
    classical
    exact (Subalgebra.fg_iff_finiteType _).1 ⟨Finset.univ.image u, by simp⟩
  have ht0 : t ≠ 0 := ht.ne_zero
  have hP : (Ideal.span {t}).IsPrime := (Ideal.span_singleton_prime ht0).2 htp
  have genA := GlobalTheory.T.exists_not_mem_smul_D_eq_sum k F K A (Ideal.span {t}) hP t (Ideal.mem_span_singleton_self t) ht0
    (fun y hy => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      exact ⟨c, 1, (Ideal.ne_top_iff_one _).1 hP.ne_top, by ring⟩) m y hy

  have memB : ∀ a : A, algebraMap F K (a : F) ∈ B := fun a => by
    rw [hB]; exact (Subalgebra.mem_restrictScalars k).2 ((integralClosure A K).algebraMap_mem a)
  let ιB : A → B := fun a => ⟨algebraMap F K (a : F), memB a⟩
  have hιQ : ∀ a : A, ιB a ∈ Q ↔ a ∈ Ideal.span {t} := fun a => by
    rw [Ideal.mem_span_singleton]; exact hcomap a (ιB a) rfl
  set du : DR k K := ExteriorAlgebra.ιMulti K (m + 1) fun j => D k K (algebraMap F K (u j)) with hdu
  have hdu0 : du ≠ 0 := fun h => by rw [h, map_zero] at hτ; exact zero_ne_one hτ
  set gA : Fin (m + 1) → Ω[K⁄k] := Fin.cons (D k K (algebraMap F K (t : F))) (fun j => D k K (algebraMap F K (y j : F))) with hgA
  obtain ⟨rA, hrA, aA, hA1⟩ := GlobalTheory.T.exterior_wedge_eq_of_localized_span A K Ω[K⁄k] (Ideal.span {t}).primeCompl (m + 1) gA (fun j => D k K (algebraMap F K (u j))) (fun i => by
    obtain ⟨r, hr, c, hc⟩ := genA ⟨u i, hA ▸ Algebra.subset_adjoin (Set.mem_range_self i)⟩
    exact ⟨r, hr, c, hc⟩)
  obtain ⟨r', hr', c', hA2⟩ := GlobalTheory.T.exterior_wedge_eq_of_localized_span A K Ω[K⁄k] (Ideal.span {t}).primeCompl (m + 1) (fun j => D k K (algebraMap F K (u j))) gA (fun i => by
    have key : ∀ v : A, ∃ c : Fin (m + 1) → A, D k K (algebraMap F K (v : F)) = ∑ l, algebraMap A K (c l) • D k K (algebraMap F K (u l)) := by
      intro v
      obtain ⟨c, hc, hc'⟩ := GlobalTheory.T.exists_D_eq_sum_smul_D_of_mem_adjoin k F K (m + 1) u (v : F) (hA ▸ v.2)
      exact ⟨fun j => ⟨c j, hA ▸ hc j⟩, hc'⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · obtain ⟨c, hc⟩ := key t
      exact ⟨1, Submonoid.one_mem _, c, by rw [map_one, one_smul]; exact hc⟩
    · obtain ⟨c, hc⟩ := key (y j)
      exact ⟨1, Submonoid.one_mem _, c, by rw [map_one, one_smul]; exact hc⟩)
  have hAeq : rA * r' = aA * c' := by
    apply FaithfulSMul.algebraMap_injective A K
    have h3 : (algebraMap A K (rA * r')) • du = (algebraMap A K (aA * c')) • du := by
      rw [map_mul, map_mul, mul_comm, mul_smul, hA1, smul_comm, hA2, smul_smul, mul_comm]
    exact smul_left_injective K hdu0 h3
  have haA : aA ∉ Ideal.span {t} := fun h => by
    have : rA * r' ∈ Ideal.span {t} := hAeq ▸ Ideal.mul_mem_right _ _ h
    rcases hP.mem_or_mem this with h4 | h4
    · exact hrA h4
    · exact hr' h4

  let y' : Fin m → B := fun j => ιB (y j)
  have hy' := GlobalTheory.T.isTranscendenceBasis_quotient_integralClosure' k F K A B hB Q hQ t hcomap m y hy y' (fun j => rfl)
  haveI := GlobalTheory.T.integralClosure_finiteType_over_adjoin k F K (m + 1) u hu A hA B hB
  have hs0 : s ≠ 0 := by
    rintro rfl
    have h5 : (r₀ : K) * algebraMap F K t = 0 := by rw [hrt]; simp [zero_pow (by omega : e ≠ 0)]
    rcases mul_eq_zero.1 h5 with h6 | h6
    · exact hr₀ (by rw [show r₀ = 0 from Subtype.ext h6]; exact Q.zero_mem)
    · exact ht0 (by
        have : (t : F) = 0 := (map_eq_zero_iff _ (algebraMap F K).injective).1 h6
        exact Subtype.ext this)
  have genB := GlobalTheory.T.exists_not_mem_smul_D_eq_sum k K K B Q hQ s hsQ hs0 hQs m y' hy'
  simp only [Algebra.algebraMap_self_apply] at genB
  obtain ⟨N, Dn, hN, hDn, hND⟩ := GlobalTheory.T.differential_relation_local_ring_bound k K B Q hQ s m (fun j => (y' j : K)) (algebraMap F K t) e he hsQ genB ⟨a₀, r₀, ha₀, hr₀, hrt⟩
  set ω : DR k K := ExteriorAlgebra.ιMulti K (m + 1) (Fin.cons (D k K (s : K)) (fun j => D k K (y' j : K)) : Fin (m + 1) → Ω[K⁄k]) with hω
  let Dt : B := Dn * ιB rA
  let Nt : B := N * ιB aA
  have hDt : Dt ∉ Q := fun h => (hQ.mem_or_mem h).elim hDn (fun h' => hrA ((hιQ rA).1 h'))
  have hNt : Nt ∉ Q := fun h => (hQ.mem_or_mem h).elim hN (fun h' => haA ((hιQ aA).1 h'))
  have hmain : (Dt : K) • du = ((Nt : K) * (s : K) ^ (e - 1)) • ω := by
    have h7 : (Dn : K) • ExteriorAlgebra.ιMulti K (m + 1) gA = ((N : K) * (s : K) ^ (e - 1)) • ω := hND
    have hA1' : (algebraMap F K (rA : F)) • du = (algebraMap F K (aA : F)) • ExteriorAlgebra.ιMulti K (m + 1) gA := hA1
    show ((Dn : K) * algebraMap F K (rA : F)) • du = ((N : K) * algebraMap F K (aA : F) * (s : K) ^ (e - 1)) • ω
    rw [mul_smul, hA1', smul_comm, h7, smul_smul]
    congr 1
    ring
  have hkey : (Dt : K) = (Nt : K) * (s : K) ^ (e - 1) * τ ω := by
    have := congrArg τ hmain
    rw [map_smul, map_smul, hτ, smul_eq_mul, smul_eq_mul, mul_one] at this
    rw [this]
  have hv0 : (Fin.cons (D k K (s : K)) (fun j => D k K (y' j : K)) : Fin (m + 1) → Ω[K⁄k]) = fun j => D k K ((Fin.cons (s : K) (fun j => (y' j : K)) : Fin (m + 1) → K) j) := by
    funext j; exact Fin.cases rfl (fun j => rfl) j
  have hωmem : ∀ b : B, (b : K) • ω ∈ omB k K B (m + 1) := fun b => by
    refine Submodule.subset_span ⟨b, b.2, Fin.cons (s : K) (fun j => (y' j : K)), fun j => Fin.cases s.2 (fun j => (y' j).2) j, ?_⟩
    rw [hω, hv0]
  have P : ∀ yy ∈ omB k K B (m + 1), ∃ c ρ : B, ρ ∉ Q ∧ (ρ : K) * (s : K) ^ (e - 1) * τ yy = c := by
      intro yy hyy
      unfold omB at hyy
      induction hyy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, hb, v, hv, rfl⟩ := hx
        obtain ⟨ρ, hρ, β, hβ⟩ := GlobalTheory.T.exterior_wedge_eq_of_localized_span B K Ω[K⁄k] Q.primeCompl (m + 1) (Fin.cons (D k K (s : K)) (fun j => D k K (y' j : K))) (fun j => D k K (v j)) (fun i => genB ⟨v i, hv i⟩)
        have hβ' : (ρ : K) • ExteriorAlgebra.ιMulti K (m + 1) (fun j => D k K (v j)) = (β : K) • ω := hβ
        have h8 := congrArg τ hβ'
        rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h8
        refine ⟨⟨b, hb⟩ * β * Dt, ρ * Nt, fun h => (hQ.mem_or_mem h).elim hρ hNt, ?_⟩
        rw [map_smul, smul_eq_mul]
        push_cast
        rw [hkey]
        linear_combination ((b : K) * (Nt : K) * (s : K) ^ (e - 1)) * h8
      | zero => exact ⟨0, 1, (Ideal.ne_top_iff_one _).1 hQ.ne_top, by simp⟩
      | add x w _ _ hx hw =>
        obtain ⟨c1, ρ1, h1, e1⟩ := hx
        obtain ⟨c2, ρ2, h2, e2⟩ := hw
        refine ⟨ρ2 * c1 + ρ1 * c2, ρ1 * ρ2, fun h => (hQ.mem_or_mem h).elim h1 h2, ?_⟩
        rw [map_add (f := _)]; push_cast
        linear_combination (ρ2 : K) * e1 + (ρ1 : K) * e2
      | smul a x _ hx =>
        obtain ⟨c, ρ, h1, e1⟩ := hx
        refine ⟨algebraMap k B a * c, ρ, h1, ?_⟩
        rw [τ.map_smul_of_tower, Algebra.smul_def]
        push_cast
        rw [← e1]
        ring
  constructor
  · rintro ⟨r, hr, yy, hyy, hτy⟩
    obtain ⟨c, ρ, hρ, hc⟩ := P yy hyy
    refine ⟨c, ρ * r, fun h => (hQ.mem_or_mem h).elim hρ hr, ?_⟩
    rw [← hc, hτy]; push_cast; ring
  · rintro ⟨c, r, hr, hc⟩
    refine ⟨Dt * r, fun h => (hQ.mem_or_mem h).elim hDt hr, ((c * Nt : B) : K) • ω, hωmem _, ?_⟩
    rw [map_smul, smul_eq_mul]
    push_cast
    rw [hkey]
    linear_combination (-((Nt : K) * τ ω)) * hc

end GlobalTheory.PD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsResolutionMapAugmentationSpec
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

section
variable {R S : Type} [CommRing R] [CommRing S]

def rcxSemi (φ : R →+* S) {K : Cx S} {J : Cx R} (m : (rcx φ).obj K ⟶ J) : SemiMap K J where
  app U s := ((m.f s).hom.app (op U)).hom.toAddMonoidHom
  nat g s a := (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ((m.f s).hom.naturality g.op)) a).symm
  comm U s t a := by
    have h := congrArg (fun k => ((k.hom.app (op U)).hom a)) (m.comm s t)
    refine Eq.trans ?_ (h.trans ?_) <;> rfl

theorem rcxSemi_app (φ : R →+* S) {K : Cx S} {J : Cx R} (m : (rcx φ).obj K ⟶ J) (U : Scheme.{0}) (s : ℤ)
    (a : Sec (K.X s) U) : (rcxSemi φ m).app U s a = Sec.map (m.f s) (show Sec ((restr φ).obj (K.X s)) U from a) := rfl

end

theorem restrMap_exists : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S), ∃ ρ : SemiMap (res S F) (res R ((restr φ).obj F)),
    ∀ (U : Scheme.{0}) (a : Sec F U),
      ρ.app U 0 (Sec.map (resι S F) a) = Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a) := by
  intro R S _ _ φ F
  obtain ⟨hKI, -, hGE, -, hι, -⟩ := _root_.GlobalTheory.EtC.ResBasic.res_basic R ((restr φ).obj F)
  obtain ⟨-, -, -, hq, hιS, -⟩ := _root_.GlobalTheory.EtC.ResBasic.res_basic S F
  have := rAug_quasiIso φ (resAug F)
  obtain ⟨m, hm⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective R ((restr φ).obj F) ((rcx φ).obj (res S F)) (res R ((restr φ).obj F))
    (rAug φ (resAug F))).1 (resAug ((restr φ).obj F))
  refine ⟨rcxSemi φ m, fun U a => ?_⟩
  rw [rcxSemi_app]
  have h1 : Sec.map (resι S F) a = Sec.map ((resAug F).f 0) (Sec.map (sglι F) a) := by
    rw [← hιS]; rfl
  have h2 := rAug_f_zero φ (resAug F) U a
  have h3 : Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a) =
      Sec.map (((rAug φ (resAug F)) ≫ m).f 0) (Sec.map (sglι ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)) := by
    rw [hm, ← hι]; rfl
  rw [h3, h1, ← h2]
  rfl

theorem restrMap_spec' : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S) (U : Scheme.{0}) (a : Sec F U), (restrMap φ F).app U 0 (Sec.map (resι S F) a) = Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a) := by
  intro R S _ _ φ F U a
  exact pick_spec (restrMap_exists R S φ F) U a

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannInequalityCofinalFunctionField
section
open scoped IntermediateField Polynomial RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

namespace RiemannCofinal

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem val_ne_zero (v : Place k F) {x : F} (hx : x ≠ 0) : v.1 x ≠ 0 :=
  (Valuation.ne_zero_iff _).2 hx

theorem ord_mul (v : Place k F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord v (x * y) = ord v x + ord v y := by
  unfold ord
  rw [map_mul, WithZero.log_mul (val_ne_zero v hx) (val_ne_zero v hy)]
  ring

theorem ord_inv (v : Place k F) (x : F) : ord v x⁻¹ = -ord v x := by
  unfold ord
  rw [map_inv₀, WithZero.log_inv]

theorem ord_pow (v : Place k F) (x : F) (n : ℕ) : ord v (x ^ n) = n * ord v x := by
  unfold ord
  rw [map_pow, WithZero.log_pow]
  simp

theorem ord_one (v : Place k F) : ord v 1 = 0 := by simp [ord]

theorem ord_le_ord (v : Place k F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (h : v.1 x ≤ v.1 y) :
    ord v y ≤ ord v x := by
  unfold ord
  have := (WithZero.log_le_log (val_ne_zero v hx) (val_ne_zero v hy)).2 h
  omega

theorem le_one_iff (v : Place k F) {x : F} (hx : x ≠ 0) : v.1 x ≤ 1 ↔ 0 ≤ ord v x := by
  unfold ord
  rw [← WithZero.log_le_log (val_ne_zero v hx) one_ne_zero, WithZero.log_one]
  constructor <;> intro <;> omega

theorem lt_one_iff (v : Place k F) {x : F} (hx : x ≠ 0) : v.1 x < 1 ↔ 0 < ord v x := by
  unfold ord
  rw [← WithZero.log_lt_log (val_ne_zero v hx) one_ne_zero, WithZero.log_one]
  constructor <;> intro <;> omega

theorem ord_prod {ι : Type} (v : Place k F) (s : Finset ι) (x : ι → F) (hx : ∀ i ∈ s, x i ≠ 0) :
    ord v (∏ i ∈ s, x i) = ∑ i ∈ s, ord v (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ord_one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ord_mul v (hx a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun i hi => hx i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hx i (Finset.mem_insert_of_mem hi)]

theorem val_algebraMap_le (v : Place k F) (c : k) : v.1 (algebraMap k F c) ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [v.2.2 c hc]

end RiemannCofinal

end GlobalTheory.Nef

namespace GlobalTheory.Nef

open RiemannCofinal

theorem riemann_cofinal : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∃ γ : ℕ, ∀ D : Place k F →₀ ℤ, ∃ D' : Place k F →₀ ℤ, D ≤ D' ∧ ∃ (n : ℕ) (f : Fin n → F), LinearIndependent k f ∧ (D'.sum fun _ m => m) - γ ≤ n ∧ ∀ (i : Fin n) (v : Place k F), -D' v ≤ ord v (f i) := by
  intro k F _ _ _ _ _ hFF
  classical
  obtain ⟨t, ht, -⟩ := id hFF
  have ht0 : t ≠ 0 := fun h => ht (h ▸ isAlgebraic_zero)
  have hti : Transcendental k t⁻¹ := fun h => ht (IsAlgebraic.inv_iff.1 h)
  have hadj : k⟮t⁻¹⟯ = k⟮t⟯ := le_antisymm
    (IntermediateField.adjoin_simple_le_iff.2 (inv_mem (IntermediateField.mem_adjoin_simple_self k t)))
    (IntermediateField.adjoin_simple_le_iff.2
      (by simpa using inv_mem (IntermediateField.mem_adjoin_simple_self k t⁻¹)))
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.Nef.exists_many_bounded_by_pow k F hFF t ht
  obtain ⟨hPfin, hPdeg⟩ := _root_.GlobalTheory.Nef.zeros_finite_sum_eq_degree k F hFF t⁻¹ hti
  rw [hadj] at hPdeg
  refine ⟨c * Module.finrank k⟮t⟯ F, fun D => ?_⟩

  have hpole : ∀ w : Place k F, ¬ w.1 t ≤ 1 ↔ w.1 t⁻¹ < 1 := by
    intro w
    rw [lt_one_iff w (inv_ne_zero ht0), ord_inv, le_one_iff w ht0]
    constructor <;> intro <;> omega

  have hres : ∀ v : Place k F, v.1 t ≤ 1 → ∃ a : k, v.1 (t - algebraMap k F a) < 1 :=
    fun v => (_root_.GlobalTheory.Nef.place_isDVR_residue k F hFF v).2 t
  obtain ⟨r, hr⟩ : ∃ r : Place k F → k, ∀ v : Place k F, v.1 t ≤ 1 → v.1 (t - algebraMap k F (r v)) < 1 :=
    ⟨fun v => if h : v.1 t ≤ 1 then (hres v h).choose else 0, fun v h => by
      simp only [dif_pos h]; exact (hres v h).choose_spec⟩
  have hlin0 : ∀ a : k, t - algebraMap k F a ≠ 0 := fun a h =>
    ht (sub_eq_zero.1 h ▸ isAlgebraic_algebraMap a)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ∑ v ∈ D.support, (D v).natAbs := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : F, h = ∏ v ∈ D.support, (t - algebraMap k F (r v)) ^ (D v).natAbs :=
    ⟨_, rfl⟩
  have hh0 : h ≠ 0 := hh ▸ Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hlin0 _)
  have hordh : ∀ w : Place k F,
      ord w h = ∑ v ∈ D.support, ((D v).natAbs : ℤ) * ord w (t - algebraMap k F (r v)) := by
    intro w
    rw [hh, ord_prod w _ _ (fun v _ => pow_ne_zero _ (hlin0 _))]
    exact Finset.sum_congr rfl fun v _ => ord_pow w _ _
  obtain ⟨hhfin, hhsum⟩ := _root_.GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero k F hFF h hh0
  obtain ⟨n, f, hli, hn, hf⟩ := hc (2 * M)
  obtain ⟨P, hP⟩ : ∃ P : Place k F → ℤ,
      P = {v : Place k F | v.1 t⁻¹ < 1}.indicator fun v => ord v t⁻¹ := ⟨_, rfl⟩
  have hPpole : ∀ w : Place k F, ¬ w.1 t ≤ 1 → P w = -ord w t := by
    intro w hw
    rw [hP, Set.indicator_of_mem (show w ∈ {v : Place k F | v.1 t⁻¹ < 1} from (hpole w).1 hw),
      ord_inv]
  have hPint : ∀ w : Place k F, w.1 t ≤ 1 → P w = 0 := by
    intro w hw
    rw [hP, Set.indicator_of_notMem (show w ∉ {v : Place k F | v.1 t⁻¹ < 1} from
      fun h' => (hpole w).2 h' hw)]
  have hPsupp : Function.support P ⊆ {v : Place k F | v.1 t⁻¹ < 1} := by
    intro w hw
    by_contra hw'
    exact hw (hPint w (by by_contra h'; exact hw' ((hpole w).1 h')))
  have hhsupp : Function.support (fun v : Place k F => ord v h) ⊆ {v : Place k F | v.1 h ≠ 1} := by
    intro v hv hv1
    exact hv (show ord v h = 0 by simp [ord, hv1])
  obtain ⟨g, hg⟩ : ∃ g : Place k F → ℤ, g = fun v => ((2 * M : ℕ) : ℤ) * P v + ord v h := ⟨_, rfl⟩
  have hgfin : (Function.support g).Finite := by
    refine (hPfin.union hhfin).subset fun v hv => ?_
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hnot
    apply hv
    have h1 : P v = 0 := by
      by_contra h'; exact hnot.1 (hPsupp h')
    have h2 : ord v h = 0 := by simp [ord, hnot.2]
    simp [hg, h1, h2]
  refine ⟨Finsupp.ofSupportFinite g hgfin, ?_, n, fun i => f i * h⁻¹, ?_, ?_, ?_⟩
  ·
    intro w
    show D w ≤ g w
    simp only [hg]
    have hDM : D w ≤ (M : ℤ) := by
      by_cases hw : w ∈ D.support
      · have h1 := Finset.single_le_sum (f := fun v => (D v).natAbs) (fun _ _ => Nat.zero_le _) hw
        have h2 : D w ≤ ((D w).natAbs : ℤ) := Int.le_natAbs
        rw [hM]
        have h3 : (((D w).natAbs : ℕ) : ℤ) ≤ ((∑ v ∈ D.support, (D v).natAbs : ℕ) : ℤ) :=
          Nat.cast_le.2 h1
        omega
      · rw [Finsupp.notMem_support_iff.1 hw]; positivity
    by_cases ht1 : w.1 t ≤ 1
    · have hnn : ∀ v, 0 ≤ ord w (t - algebraMap k F (r v)) := fun v =>
        (le_one_iff w (hlin0 _)).1
          ((Valuation.map_sub _ _ _).trans (max_le ht1 (val_algebraMap_le w _)))
      simp only [hPint w ht1, mul_zero, zero_add, hordh w]
      by_cases hw : w ∈ D.support
      · have hone : 0 < ord w (t - algebraMap k F (r w)) := (lt_one_iff w (hlin0 _)).1 (hr w ht1)
        have h2 : D w ≤ ((D w).natAbs : ℤ) := Int.le_natAbs
        have h3 := Finset.single_le_sum
          (f := fun v => ((D v).natAbs : ℤ) * ord w (t - algebraMap k F (r v)))
          (fun v _ => mul_nonneg (by positivity) (hnn v)) hw
        have h4 : ((D w).natAbs : ℤ) ≤ ((D w).natAbs : ℤ) * ord w (t - algebraMap k F (r w)) := by
          nlinarith
        omega
      · rw [Finsupp.notMem_support_iff.1 hw]
        exact Finset.sum_nonneg fun v _ => mul_nonneg (by positivity) (hnn v)
    · have hge : ∀ v, ord w t ≤ ord w (t - algebraMap k F (r v)) := fun v =>
        ord_le_ord w (hlin0 _) ht0 ((Valuation.map_sub _ _ _).trans
          (max_le le_rfl ((val_algebraMap_le w _).trans (le_of_lt (not_le.1 ht1)))))
      have hsum : (M : ℤ) * ord w t ≤ ord w h := by
        rw [hordh, hM]
        push_cast
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hge v) (by positivity)
      have hneg : ord w t < 0 := by
        have := (le_one_iff w ht0).not.1 ht1
        omega
      rw [hPpole w ht1]
      push_cast
      have hM0 : (0 : ℤ) ≤ M := by positivity
      nlinarith
  ·
    exact hli.map' (LinearMap.mulRight k h⁻¹)
      (LinearMap.ker_eq_bot.2 (mul_left_injective₀ (inv_ne_zero hh0)))
  ·
    have hsub : Function.support g ⊆ ↑(Finsupp.ofSupportFinite g hgfin).support := by
      intro v hv
      exact Finsupp.mem_support_iff.2 hv
    have hdeg : ((Finsupp.ofSupportFinite g hgfin).sum fun _ m => m) =
        ((2 * M : ℕ) : ℤ) * Module.finrank k⟮t⟯ F := by
      have h1 : ((Finsupp.ofSupportFinite g hgfin).sum fun _ m => m) = ∑ᶠ v, g v := by
        rw [finsum_eq_sum_of_support_subset g hsub]
        rfl
      have hPsum : ∑ᶠ v, P v = Module.finrank k⟮t⟯ F := by
        rw [finsum_mem_def] at hPdeg
        rw [hP]; exact hPdeg
      rw [h1, hg]
      rw [finsum_add_distrib
        ((hPfin.subset hPsupp).subset fun v hv h0 => hv (by simp [h0]))
        (hhfin.subset hhsupp), ← mul_finsum, hhsum, hPsum, add_zero]
    rw [hdeg]
    push_cast
    calc ((2 * M : ℕ) : ℤ) * Module.finrank k⟮t⟯ F - c * Module.finrank k⟮t⟯ F
        = (((2 * M : ℕ) : ℤ) - c) * Module.finrank k⟮t⟯ F := by ring
      _ ≤ n := hn
  ·
    intro i w
    have hfi : f i ≠ 0 := hli.ne_zero i
    show -(g w) ≤ ord w (f i * h⁻¹)
    rw [ord_mul w hfi (inv_ne_zero hh0), ord_inv, hg]
    have key : -(((2 * M : ℕ) : ℤ) * P w) ≤ ord w (f i) := by
      by_cases ht1 : w.1 t ≤ 1
      · have h1 : w.1 (f i) ≤ 1 := by simpa [max_eq_left ht1] using hf i w
        rw [hPint w ht1]
        simpa using (le_one_iff w hfi).1 h1
      · have h1 : w.1 (f i) ≤ w.1 (t ^ (2 * M)) := by
          rw [map_pow]; simpa [max_eq_right (le_of_lt (not_le.1 ht1))] using hf i w
        have := ord_le_ord w hfi (pow_ne_zero _ ht0) h1
        rw [ord_pow] at this
        rw [hPpole w ht1]
        push_cast at this ⊢
        linarith
    simp only
    linarith

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsComplexExactEtaleLocallyOfNoClassesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionsComplex_exact_etaleLocally_of_no_classes : ∀ (R : Type) [CommRing R] (M : Cx R) (U : Scheme.{0}), (∀ n, Subsingleton (CohomologyClass ((chains R).obj (sch.obj U)) M n)) → ∀ (n : ℤ) (b : Sec (M.X n) U), Sec.map (M.d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec (M.X (n - 1)) V, Sec.map (M.d (n - 1) n) a = Sec.res g b := by
  first | (exact @GlobalTheory.EtC.sch_loc_exact) | (exact GlobalTheory.EtC.sch_loc_exact) | (intros; apply GlobalTheory.EtC.sch_loc_exact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRegularFormsFiniteProjectiveSmoothStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_regularForms_finite_projective_smooth : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] [Algebra.Smooth k B] (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → Module.Finite B (Submodule.span B ((omB k K B p).comap (e.restrictScalars k) : Set W)) ∧ Module.Projective B (Submodule.span B ((omB k K B p).comap (e.restrictScalars k) : Set W)) := by
  first | (exact @GlobalTheory.PD.span_omB_comap_finite_projective) | (exact GlobalTheory.PD.span_omB_comap_finite_projective) | (intros; apply GlobalTheory.PD.span_omB_comap_finite_projective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistGeneratorTmulOrderLocallyStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistGenerator_tmul_order_locally : ∀ (q : ℕ) [NeZero q] (i j : ℤ) (W : Scheme.{0}) (ζ : Prim q Γ(W, ⊤)) (c : ℕ), c • (twGen i ζ ⊗ₜ[ULift.{1} (ZMod q)] twGen j ζ) = 0 → Loc W fun V _ => Nonempty V → q ∣ c := by
  first | (exact @GlobalTheory.TwMulOrder.tw_mul_order) | (exact GlobalTheory.TwMulOrder.tw_mul_order) | (intros; apply GlobalTheory.TwMulOrder.tw_mul_order  <;> assumption)
end

