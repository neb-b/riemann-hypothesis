module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocG
public import Mathlib
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0002
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral

@[expose] public section

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.ExistsHomOfBasis
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

theorem norm_le_one_iff_val {F C : Type} [Field F] [NumberField F] [NormedField C] (φ : F →+* C)
    (w : HeightOneSpectrum (𝓞 F)) (h1 : ∀ x : 𝓞 F, ‖φ (x : F)‖ ≤ 1)
    (h2 : ∀ x : 𝓞 F, x ∈ w.asIdeal ↔ ‖φ (x : F)‖ < 1) (x : F) : ‖φ x‖ ≤ 1 ↔ w.valuation F x ≤ 1 := by
  have hu : ∀ d : 𝓞 F, d ∉ w.asIdeal → ‖φ (d : F)‖ = 1 := fun d hd =>
    le_antisymm (h1 d) (not_lt.mp fun h => hd ((h2 d).mpr h))
  have key : ∀ y : F, w.valuation F y ≤ 1 → ∃ n : 𝓞 F, ‖φ y‖ = ‖φ (n : F)‖ ∧
      w.valuation F y = w.valuation F (n : F) := fun y hy => by
    obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer y hy
    have hd : w.valuation F (algebraMap (𝓞 F) F d) = 1 := w.valuation_eq_one_iff_notMem.mpr d.2
    refine ⟨n, ?_, ?_⟩
    · have := congrArg (fun t => ‖φ t‖) h
      simp only [map_mul, norm_mul] at this
      rwa [show ‖φ (algebraMap (𝓞 F) F d)‖ = 1 from hu _ d.2, mul_one] at this
    · have := congrArg (w.valuation F) h
      rwa [map_mul, hd, mul_one] at this
  refine ⟨fun h => not_lt.mp fun hlt => ?_, fun h => ?_⟩
  · have hx : x ≠ 0 := by rintro rfl; simp at hlt
    have hi : w.valuation F x⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hlt
    obtain ⟨n, e1, e2⟩ := key _ hi.le
    have hn : n ∈ w.asIdeal := (w.valuation_lt_one_iff_mem n).mp (e2 ▸ hi)
    have := (h2 n).mp hn
    rw [← e1, map_inv₀, norm_inv, inv_lt_one₀ (norm_pos_iff.mpr ((map_ne_zero φ).mpr hx))] at this
    exact absurd h (not_le.mpr this)
  · obtain ⟨n, e1, -⟩ := key x h
    rw [e1]; exact h1 n

theorem resChar_mem' (D : D7) (w : D.what₂.places.Pl) :
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  have hp := D.what₂.places.resChar_prime w
  have hne : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h := D.what₂.places.val_resChar w
  rw [D.val_eq w _ hne] at h
  have h1 : vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) :=
    WithTop.coe_injective h
  have h2 : (0 : ℤ) < D.what₂.places.ramIdx w := by exact_mod_cast D.what₂.places.ramIdx_pos w
  rw [← (D.plEq w).valuation_lt_one_iff_mem (K := D.what₂.LL)]
  show (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL _) < 1
  have hv := (Valuation.ne_zero_iff ((D.plEq w).valuation D.what₂.LL)).mpr hne
  rw [map_natCast, ← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  unfold vAdd at h1
  omega

theorem mem_intW_iff (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    x ∈ intW D.what₂.places w ↔ (D.plEq w).valuation D.what₂.LL x ≤ 1 := by
  show (0 : WithTop ℤ) ≤ D.what₂.places.val w x ↔ _
  by_cases hx : x = 0
  · subst hx; simp
  · have hv := (Valuation.ne_zero_iff ((D.plEq w).valuation D.what₂.LL)).mpr hx
    rw [D.val_eq w x hx, ← WithTop.coe_zero, WithTop.coe_le_coe, vAdd, neg_nonneg]
    conv_rhs => rw [← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_le_exp]

theorem exists_lamExt {K : Type} [Field K] [NumberField K] (e : K →+* ℂ) {C : Type} [Field C] [IsAlgClosed C]
    (f : K →+* C) : ∃ lam : (algebraicClosure ℚ ℂ) →+* C, ∀ x : K, ∃ hx : e x ∈ algebraicClosure ℚ ℂ,
      f x = lam ⟨e x, hx⟩ := by
  have hmem : ∀ x : K, e x ∈ algebraicClosure ℚ ℂ := fun x =>
    (mem_algebraicClosure_iff).mpr ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom e.toRatAlgHom)
  let j : K →+* algebraicClosure ℚ ℂ := e.codRestrict (algebraicClosure ℚ ℂ).toSubring hmem
  let _ : Algebra K (algebraicClosure ℚ ℂ) := j.toAlgebra
  let _ : Algebra K C := f.toAlgebra
  have h0 : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have : Algebra.IsAlgebraic K (algebraicClosure ℚ ℂ) := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let l : algebraicClosure ℚ ℂ →ₐ[K] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨l.toRingHom, fun x => ⟨hmem x, (l.commutes x).symm⟩⟩

theorem exists_placeEmb (D : D7) (w : D.what₂.places.Pl) [Fact (D.what₂.places.resChar w).Prime] :
    ∃ (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w])
      (iL : D.what₂.LL →+* ℂ_[D.what₂.places.resChar w]),
      (∀ x, ∃ hx : D.what₂.embLL x ∈ algebraicClosure ℚ ℂ, iL x = lam ⟨D.what₂.embLL x, hx⟩) ∧
      ∀ x, x ∈ intW D.what₂.places w ↔ ‖iL x‖ ≤ 1 := by
  obtain ⟨φ, hφ⟩ := LB.exists_embAt (l := D.what₂.places.resChar w) (D.plEq w) (resChar_mem' D w)
  let iL := (algebraMap (PadicAlgCl (D.what₂.places.resChar w)) ℂ_[D.what₂.places.resChar w]).comp φ
  have hn : ∀ x, ‖iL x‖ = ‖φ x‖ := fun x => PadicComplex.norm_extends _ (φ x)
  obtain ⟨lam, hl⟩ := exists_lamExt D.what₂.embLL iL
  refine ⟨lam, iL, hl, fun x => ?_⟩
  rw [mem_intW_iff, hn]
  refine (norm_le_one_iff_val φ _ (fun y => ?_) hφ x).symm
  have hi : IsIntegral ℤ (φ (y : D.what₂.LL)) := (RingOfIntegers.isIntegral_coe y).map φ.toIntAlgHom
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl (D.what₂.places.resChar w)))
    ).isIntegral_iff_v_le_one.mp hi.tower_top
  exact_mod_cast (show ‖φ (y : D.what₂.LL)‖₊ ≤ 1 from h2)

end Formalism.BasicNotions.Examples₂
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.PlOver
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.PlOver

open NumberField IsDedekindDomain

variable (D : D7)

theorem liesOver_of_mem {L : Type} [Field L] [NumberField L] {p : ℕ} [Fact p.Prime] (P : Ideal (𝓞 L)) [hP : P.IsPrime]
    (h : ((p : ℕ) : 𝓞 L) ∈ P) : P.LiesOver (Ideal.span {(p : ℤ)}) := by
  have := Int.ideal_span_isMaximal_of_prime p
  refine ⟨?_⟩
  refine Ideal.IsMaximal.eq_of_le inferInstance ?_ ?_
  · exact (Ideal.IsPrime.under ℤ P).ne_top
  · rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
    simpa using h

theorem mem_of_liesOver {L : Type} [Field L] [NumberField L] {p : ℕ} (P : Ideal (𝓞 L))
    [h : P.LiesOver (Ideal.span {(p : ℤ)})] : ((p : ℕ) : 𝓞 L) ∈ P := by
  have h1 : (p : ℤ) ∈ P.under ℤ := by rw [← h.over]; exact Ideal.mem_span_singleton_self _
  rw [Ideal.under_def, Ideal.mem_comap] at h1
  simpa using h1

theorem prime_unique {L : Type} [Field L] [NumberField L] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (P : Ideal (𝓞 L))
    [hP : P.IsPrime] (hp' : ((p : ℕ) : 𝓞 L) ∈ P) (hq' : ((q : ℕ) : 𝓞 L) ∈ P) : p = q := by
  by_contra hne
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hne)
  obtain ⟨a, b, hab⟩ := hc
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : (1 : 𝓞 L) = (a : 𝓞 L) * ((p : ℕ) : 𝓞 L) + (b : 𝓞 L) * ((q : ℕ) : 𝓞 L) := by
    have := congrArg (Int.cast : ℤ → 𝓞 L) hab.symm
    push_cast at this
    exact this
  rw [h1]
  exact P.add_mem (P.mul_mem_left _ hp') (P.mul_mem_left _ hq')

theorem resChar_mem (w : D.what₂.places.Pl) :
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  have hq := D.what₂.places.resChar_prime w
  have hne : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have h1 := D.val_eq w _ hne
  rw [D.what₂.places.val_resChar] at h1
  have h2 : ((D.what₂.places.ramIdx w : ℕ) : ℤ) =
      vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by exact_mod_cast h1
  have h3 : 0 < vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
    rw [← h2]; exact_mod_cast D.what₂.places.ramIdx_pos w
  unfold vAdd at h3
  have hlt : (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) < 1 := by
    by_contra h
    push_neg at h
    have hv0 : (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr hne
    have h4 := (WithZero.log_le_log one_ne_zero hv0).mpr h
    rw [WithZero.log_one] at h4
    omega
  refine (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.what₂.LL) _ _).mp ?_
  first
    | exact hlt
    | (simpa using hlt)
    | (convert hlt using 2; exact map_natCast _ _)

theorem resChar_eq_iff (p : ℕ) [hp : Fact p.Prime] (w : D.what₂.places.Pl) :
    D.what₂.places.resChar w = p ↔ ((p : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  have := (D.plEq w).isPrime
  constructor
  · rintro rfl; exact resChar_mem D w
  · intro h; exact prime_unique (D.what₂.places.resChar_prime w) hp.out _ (resChar_mem D w) h

theorem span_ne_bot (p : ℕ) [hp : Fact p.Prime] : Ideal.span {(p : ℤ)} ≠ ⊥ := by
  simp [hp.out.ne_zero]

theorem exists_over (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 D.what₂.LL))
    (hP : P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 D.what₂.LL)) :
    ∃ w : {w : D.what₂.places.Pl // D.what₂.places.resChar w = p}, (D.plEq w.1).asIdeal = P := by
  obtain ⟨hPp, hPl⟩ := hP
  have hb : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (span_ne_bot p) P
  refine ⟨⟨D.plEq.symm ⟨P, hPp, hb⟩, ?_⟩, by simp⟩
  rw [resChar_eq_iff]
  simpa using mem_of_liesOver (p := p) P

theorem plNe (p : ℕ) [Fact p.Prime] : Nonempty {w : D.what₂.places.Pl // D.what₂.places.resChar w = p} := by
  have := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨P, hP⟩ := Ideal.nonempty_primesOver (S := 𝓞 D.what₂.LL) (Ideal.span {(p : ℤ)})
  exact ⟨(exists_over D p P hP).choose⟩

end Formalism.BasicNotions.Examples₂.PlOver
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.RelDet
section
open NumberField

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open Formalism.BasicNotions

section RelDet

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem smulLat_one {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) :
    SDLat.smulLat (1 : Matrix (Fin N) (Fin N) E) L = L := by
  unfold SDLat.smulLat
  rw [Matrix.toLin'_one]
  exact Submodule.map_id L

theorem smulLat_mul {N : ℕ} (A B : Matrix (Fin N) (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E)) :
    SDLat.smulLat (A * B) L = SDLat.smulLat A (SDLat.smulLat B L) := by
  unfold SDLat.smulLat
  rw [← Submodule.map_comp, Matrix.toLin'_mul]
  rfl

def orbRel (N : ℕ) : Setoid (SDLat E N) where
  r L L' := ∃ γ : Matrix.unitaryGroup (Fin N) E, L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) E) L.1
  iseqv := by
    refine ⟨fun L => ⟨1, ?_⟩, fun {L L'} ⟨γ, h⟩ => ⟨γ⁻¹, ?_⟩, fun {L L' L''} ⟨γ, h⟩ ⟨γ', h'⟩ => ⟨γ' * γ, ?_⟩⟩
    · exact (smulLat_one L.1).symm
    · rw [h, ← smulLat_mul]
      have : ((γ⁻¹ : Matrix.unitaryGroup (Fin N) E) : Matrix (Fin N) (Fin N) E) *
          (γ : Matrix (Fin N) (Fin N) E) = 1 := by
        rw [← Submonoid.coe_mul, inv_mul_cancel]; rfl
      rw [this, smulLat_one]
    · rw [h', h, ← smulLat_mul]; rfl

def orbRep {N : ℕ} (L : SDLat E N) : SDLat E N := (Quotient.mk (orbRel N) L).out

theorem orbRep_rel {N : ℕ} (L : SDLat E N) : (orbRel N) (orbRep L) L := Quotient.mk_out (s := orbRel N) L

theorem orbRep_eq {N : ℕ} {L L' : SDLat E N} (h : (orbRel N) L L') : orbRep L = orbRep L' := by
  unfold orbRep
  rw [Quotient.sound h]

def orbGam {N : ℕ} (L : SDLat E N) : Matrix.unitaryGroup (Fin N) E := Classical.choose (orbRep_rel L)

theorem orbGam_spec {N : ℕ} (L : SDLat E N) :
    L.1 = SDLat.smulLat ((orbGam L : Matrix.unitaryGroup (Fin N) E) : Matrix (Fin N) (Fin N) E) (orbRep L).1 :=
  Classical.choose_spec (orbRep_rel L)

def detU {N : ℕ} (γ : Matrix.unitaryGroup (Fin N) E) : unitary E :=
  ⟨(γ : Matrix (Fin N) (Fin N) E).det, Matrix.det_of_mem_unitary γ.2⟩

theorem detU_mul {N : ℕ} (γ δ : Matrix.unitaryGroup (Fin N) E) : detU (γ * δ) = detU γ * detU δ := by
  apply Subtype.ext
  show ((γ * δ : Matrix.unitaryGroup (Fin N) E) : Matrix (Fin N) (Fin N) E).det = _
  rw [Submonoid.coe_mul, Matrix.det_mul]
  rfl

variable {Tau : Type} [Fintype Tau] (emb : Tau → (E →+* ℂ))

def inverseEmbeddingProduct : unitary E →* ℂˣ :=
  (∏ τ : Tau, (Units.map (emb τ).toMonoidHom).comp Unitary.toUnits)⁻¹

theorem inverseEmbeddingProduct_apply (z : unitary E) : ((inverseEmbeddingProduct emb z : ℂˣ) : ℂ) = ∏ τ : Tau, (emb τ (z : E))⁻¹ := by
  simp [inverseEmbeddingProduct]

def potGen {N : ℕ} (L : SDLat E N) : ℂˣ := inverseEmbeddingProduct emb (detU (orbGam L))

def relDetGen (N : ℕ) (L L' : SDLat E N) : ℂˣ := (potGen emb L)⁻¹ * potGen emb L'

theorem relDetGen_self (N : ℕ) (L : SDLat E N) : relDetGen emb N L L = 1 := by
  simp [relDetGen]

theorem relDetGen_mul (N : ℕ) (L L' L'' : SDLat E N) :
    relDetGen emb N L L' * relDetGen emb N L' L'' = relDetGen emb N L L'' := by
  simp only [relDetGen]
  group

theorem inverseEmbeddingProduct_stabilizer_det (hstar : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x))
    (hmu : ∀ x : E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → ∏ τ : Tau, emb τ x = 1)
    {N : ℕ} (δ : Matrix.unitaryGroup (Fin N) E) (L : SDLat E N)
    (hδ : SDLat.smulLat (δ : Matrix (Fin N) (Fin N) E) L.1 = L.1) : inverseEmbeddingProduct emb (detU δ) = 1 := by
  apply Units.ext
  rw [inverseEmbeddingProduct_apply, Units.val_one, Finset.prod_inv_distrib, inv_eq_one]
  apply hmu
  refine det_root_of_unity_of_stab hstar (δ : Matrix (Fin N) (Fin N) E) (Matrix.det_of_mem_unitary δ.2)
    L.1 L.2.1 L.2.2.1 ?_
  intro x hx
  have : (δ : Matrix (Fin N) (Fin N) E).mulVec x ∈ SDLat.smulLat (δ : Matrix (Fin N) (Fin N) E) L.1 :=
    ⟨x, hx, by simp [Matrix.toLin'_apply]⟩
  rwa [hδ] at this

theorem relDetGen_smul (hstar : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x))
    (hmu : ∀ x : E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → ∏ τ : Tau, emb τ x = 1)
    (N : ℕ) (L L' : SDLat E N) (γ : Matrix.unitaryGroup (Fin N) E)
    (h : L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) E) L.1) :
    relDetGen emb N L L' = inverseEmbeddingProduct emb ⟨(γ : Matrix (Fin N) (Fin N) E).det, Matrix.det_of_mem_unitary γ.2⟩ := by
  have hrel : (orbRel N) L L' := ⟨γ, h⟩
  have hrep : orbRep L' = orbRep L := (orbRep_eq hrel).symm
  set r := orbRep L with hr
  set gL := orbGam L
  set gL' := orbGam L'
  have hL : L.1 = SDLat.smulLat (gL : Matrix (Fin N) (Fin N) E) r.1 := orbGam_spec L
  have hL' : L'.1 = SDLat.smulLat (gL' : Matrix (Fin N) (Fin N) E) r.1 := by
    have := orbGam_spec L'; rwa [hrep] at this
  set δ : Matrix.unitaryGroup (Fin N) E := (γ * gL)⁻¹ * gL'
  have hδ : SDLat.smulLat (δ : Matrix (Fin N) (Fin N) E) r.1 = r.1 := by
    have e1 : SDLat.smulLat ((γ * gL : Matrix.unitaryGroup (Fin N) E) : Matrix (Fin N) (Fin N) E) r.1 =
        SDLat.smulLat (gL' : Matrix (Fin N) (Fin N) E) r.1 := by
      rw [Submonoid.coe_mul, smulLat_mul, ← hL, ← h, hL']
    show SDLat.smulLat (((γ * gL)⁻¹ * gL' : Matrix.unitaryGroup (Fin N) E) : Matrix (Fin N) (Fin N) E) r.1 = r.1
    rw [Submonoid.coe_mul, smulLat_mul, ← e1, ← smulLat_mul, ← Submonoid.coe_mul, inv_mul_cancel]
    exact smulLat_one r.1
  have hs := inverseEmbeddingProduct_stabilizer_det emb hstar hmu δ r hδ
  have hg : gL' = (γ * gL) * δ := by
    show gL' = (γ * gL) * ((γ * gL)⁻¹ * gL')
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have : potGen emb L' = inverseEmbeddingProduct emb (detU γ) * potGen emb L := by
    simp only [potGen]
    rw [show orbGam L' = gL' from rfl, hg, detU_mul, detU_mul, map_mul, map_mul, hs, mul_one, mul_comm]
  simp only [relDetGen, this]
  rw [mul_comm (inverseEmbeddingProduct emb (detU γ)), ← mul_assoc, inv_mul_cancel, one_mul]
  rfl

end RelDet

section Host

variable {R : Ranks} (H : Host R) {Tau : Type} [Fintype Tau] (eTau : Tau ≃ ↥(R.Psi))

def embTau : Tau → (H.E →+* ℂ) := fun τ => H.emb ((eTau τ : R.Psi) : R.GG)

theorem prod_embTau_eq_one_of_torsion : ∀ x : H.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → ∏ τ : Tau, embTau H eTau τ x = 1 :=
  fun _ hx => UpperTheory.Mu.prod_emb H eTau hx

def exampleInverseEmbeddingProduct : letI := H.cmStar; unitary H.E →* ℂˣ := letI := H.cmStar; inverseEmbeddingProduct (embTau H eTau)

theorem exampleCharacter_unitary_product : letI := H.cmStar; ∀ z : unitary H.E,
    (((MonoidHom.id ℂˣ) (exampleInverseEmbeddingProduct H eTau z) : ℂˣ) : ℂ) =
      ∏ τ : Tau, (H.emb ((eTau τ : R.Psi) : R.GG) (z : H.E))⁻¹ := by
  let _ := H.cmStar
  intro z
  exact inverseEmbeddingProduct_apply (embTau H eTau) z

def relDetExample : letI := H.cmStar; ∀ N, SDLat H.E N → SDLat H.E N → ℂˣ :=
  letI := H.cmStar; relDetGen (embTau H eTau)

theorem relDetExample_self : letI := H.cmStar; ∀ N L, relDetExample H eTau N L L = 1 := by
  let _ := H.cmStar
  exact relDetGen_self (embTau H eTau)

theorem relDetExample_mul : letI := H.cmStar; ∀ N L L' L'',
    relDetExample H eTau N L L' * relDetExample H eTau N L' L'' = relDetExample H eTau N L L'' := by
  let _ := H.cmStar
  exact relDetGen_mul (embTau H eTau)

theorem relDetExample_smul : letI := H.cmStar; ∀ N (L L' : SDLat H.E N) (γ : Matrix.unitaryGroup (Fin N) H.E),
    L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1 →
      relDetExample H eTau N L L' = exampleInverseEmbeddingProduct H eTau
        ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩ := by
  let _ := H.cmStar
  exact relDetGen_smul (embTau H eTau) (emb_star H) (prod_embTau_eq_one_of_torsion H eTau)

end Host

end Formalism.BasicNotions.Examples₂
end
end

