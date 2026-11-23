module

public import Formalism.LocalToGlobal.Columns.Bundle0030
public import Formalism.LocalToGlobal.Columns.TwQLev
public import Formalism.LocalToGlobal.Columns.XtLamGvSCongr

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.TwQBOpen
section
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV

section Div

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}


set_option maxHeartbeats 2000000 in
theorem qbK_of_div {c : v.adicCompletion F} (hc : c ∈ v.adicCompletionIntegers F) (hc1 : Valued.v c < 1)
    {k : GL (Fin n) (v.adicCompletion F)} (hk : qbDiv c ((k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) - 1)) : k ∈ qbK c := by
  classical
  let O := v.adicCompletionIntegers F
  have hkint : qbInt (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := fun i j => by
    obtain ⟨z, hz, e⟩ := hk i j
    have : (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j = c * z + (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j := by
      rw [← e, Matrix.sub_apply, sub_add_cancel]
    rw [this]
    exact Subring.add_mem _ (Subring.mul_mem _ hc hz) (qbInt_one i j)
  let kO : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, hkint i j⟩
  have hres : (IsLocalRing.residue O).mapMatrix kO = 1 := by
    ext i j
    obtain ⟨z, hz, e⟩ := hk i j
    have h2 : IsLocalRing.residue O (kO i j - (1 : Matrix (Fin n) (Fin n) O) i j) = 0 := by
      apply glo_res_zero v
      show Valued.v ((k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j -
        (((1 : Matrix (Fin n) (Fin n) O) i j : O) : v.adicCompletion F)) < 1
      have e1 : (((1 : Matrix (Fin n) (Fin n) O) i j : O) : v.adicCompletion F) = (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j := by
        rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> rfl
      rw [e1, ← Matrix.sub_apply, e, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hz)) hc1
    rw [map_sub, sub_eq_zero] at h2
    show IsLocalRing.residue O (kO i j) = (1 : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O)) i j
    rw [h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : IsUnit kO.det := by
    have h1 : IsLocalRing.residue O kO.det = 1 := by rw [RingHom.map_det, hres, Matrix.det_one]
    by_contra h
    have h2 : kO.det ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 h
    rw [← IsLocalRing.residue_eq_zero_iff] at h2
    rw [h2] at h1
    exact zero_ne_one h1
  have hinv : kO * kO⁻¹ = 1 := Matrix.mul_nonsing_inv kO hdet
  have hmap : (O.subtype).mapMatrix kO = (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := rfl
  have hk1 : (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * (O.subtype).mapMatrix kO⁻¹ = 1 := by
    rw [← hmap, ← map_mul, hinv, map_one]
  have hkinv : ((k⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = (O.subtype).mapMatrix kO⁻¹ := by
    have := congrArg (fun M => ((k⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * M) hk1
    simp only [mul_one] at this
    rw [← this, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  refine ⟨hkint, fun i j => ?_, hk⟩
  rw [hkinv]
  exact (kO⁻¹ i j).2

end Div

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

theorem qsp_locL_entry {z : Fin n → E ⊗[F] v.adicCompletion F} (hz : z ∈ Formalism.L2.Herm.locL v (stdLat E n)) (i : Fin n) :
    z i ∈ Formalism.BasicNotions.intV E v := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hy i trivial)
    show inclE (F := F) (v.adicCompletion F) (y i) ∈ _
    rw [← hr]
    exact Formalism.MainNotions.Gaps.LG.sc_left_mem v r
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact Subring.add_mem _ hx hy
  | smul a x _ hx => exact Subring.mul_mem _ a.2 hx

theorem qsp_single_locL (j : Fin n) :
    (Pi.single j 1 : Fin n → E ⊗[F] v.adicCompletion F) ∈ Formalism.L2.Herm.locL v (stdLat E n) := by
  classical
  refine Submodule.subset_span ⟨Pi.single j 1, fun l _ => ?_, funext fun i => ?_⟩
  · rw [Pi.single_apply]
    show (if l = j then (1 : E) else 0) ∈ (1 : Submodule (𝓞 E) E)
    by_cases h : l = j
    · rw [if_pos h]; exact Submodule.one_le.1 le_rfl
    · rw [if_neg h]; exact zero_mem _
  · show inclE (F := F) (v.adicCompletion F) ((Pi.single j (1 : E) : Fin n → E) i) = _
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs <;> simp

end Lat

section Open

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
  (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {Q : Finset (Pl E)} (Θ : LevQFam E K n Q)
  (hQ : ∀ P : Q, conjPrime₂ P.1 ≠ P.1) (hΘ : ThetaOpen Θ)


set_option maxHeartbeats 2000000 in
theorem qbDF_spec (P : Q) : ∃ D : 𝓞 F, D ≠ 0 ∧ D ∈ (underPl F P.1).asIdeal ∧ ∃ w ∈ ((qv F P.1).adicCompletionIntegers F),
    algebraMap (𝓞 F) ((qv F P.1).adicCompletion F) D = qbF hc hQ P (qbD hc Θ hQ hΘ P) * w := by
  obtain ⟨b, hb⟩ := qsp_norm_mem hc (qbPi hc hQ P)
  have hbP : b ∈ (underPl F P.1).asIdeal := by
    show algebraMap (𝓞 F) (𝓞 E) b ∈ P.1.asIdeal
    rw [hb]; exact Ideal.mul_mem_right _ _ (qbPi_spec hc hQ P).1
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, mul_eq_zero] at hb
    rcases hb with h | h
    · exact qbPi_ne hc hQ P h
    · exact (qbPi_spec hc hQ P).2.1 (by rw [h]; exact zero_mem _)
  have hNpos := (qbN_spec Θ hΘ P).1
  refine ⟨b ^ qbN Θ hΘ P, pow_ne_zero _ hb0, Ideal.pow_mem_of_mem _ hbP _ hNpos,
    qbF hc hQ P (algebraMap (𝓞 E) E (cO E (qbPi hc hQ P))) ^ qbN Θ hΘ P,
    Subring.pow_mem _ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (qbF_int hc hQ P _)) _, ?_⟩
  have hbE : algebraMap (𝓞 F) ((qv F P.1).adicCompletion F) b =
      qbF hc hQ P ((qbPi hc hQ P : 𝓞 E) : E) * qbF hc hQ P (algebraMap (𝓞 E) E (cO E (qbPi hc hQ P))) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F ((qv F P.1).adicCompletion F), ← qsp_sp_F hc P.1 _ (qbSp hc hQ P),
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, hb, map_mul, map_mul]
  rw [map_pow, hbE, mul_pow, map_pow]

theorem qbF_d_int (P : Q) : qbF hc hQ P (qbD hc Θ hQ hΘ P) ∈ (qv F P.1).adicCompletionIntegers F := by
  rw [map_pow]
  exact Subring.pow_mem _ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (qbF_int hc hQ P _)) _

theorem qbF_d_lt (P : Q) : Valued.v (qbF hc hQ P (qbD hc Θ hQ hΘ P)) < 1 := by
  rw [map_pow, map_pow]
  exact pow_lt_one₀ zero_le ((qbF_P hc hQ P _).2 (qbPi_spec hc hQ P).1) (Nat.pos_iff_ne_zero.1 (qbN_spec Θ hΘ P).1)

theorem qbU_of_K (P : Q) {k : GL (Fin n) ((qv F P.1).adicCompletion F)} (hk : k ∈ qbK (qbF hc hQ P (qbD hc Θ hQ hΘ P))) :
    k ∈ (qbLoc hc Θ hQ hΘ).U P :=
  ⟨hk.1, hk.2.1, 1, (Θ P).H.one_mem, by simpa using hk⟩

def qbDF (P : Q) : 𝓞 F := Classical.choose (qbDF_spec hc Θ hQ hΘ P)

theorem qbDF_prop (P : Q) : qbDF hc Θ hQ hΘ P ≠ 0 ∧ qbDF hc Θ hQ hΘ P ∈ (underPl F P.1).asIdeal ∧
    ∃ w ∈ ((qv F P.1).adicCompletionIntegers F),
      algebraMap (𝓞 F) ((qv F P.1).adicCompletion F) (qbDF hc Θ hQ hΘ P) = qbF hc hQ P (qbD hc Θ hQ hΘ P) * w :=
  Classical.choose_spec (qbDF_spec hc Θ hQ hΘ P)


set_option maxHeartbeats 4000000 in
theorem qbOpen : QOpen (qbLoc hc Θ hQ hΘ) := by
  refine { princ := ?_, glob := ?_ }
  · intro P
    classical
    obtain ⟨hD0, -, w, hw, hDw⟩ := qbDF_prop hc Θ hQ hΘ P
    refine ⟨Ideal.absNorm (Ideal.span {qbDF hc Θ hQ hΘ P}), Nat.pos_of_ne_zero fun h => hD0 ?_, fun x _ hy => ?_⟩
    · rw [Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] at h; exact h
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {qbDF hc Θ hQ hΘ P}))
    apply qbU_of_K hc Θ hQ hΘ P
    apply qbK_of_div (qbF_d_int hc Θ hQ hΘ P) (qbF_d_lt hc Θ hQ hΘ P)
    intro i j
    obtain ⟨z, hz, e⟩ := hy _ (qsp_single_locL (qv F P.1) j)
    have e1 := congrFun e i
    rw [Pi.sub_apply, Pi.smul_apply, Matrix.mulVec_single_one, Matrix.col_apply, smul_eq_mul] at e1
    set f : E ⊗[F] (qv F P.1).adicCompletion F →+* (qv F P.1).adicCompletion F :=
      (RingHom.fst _ _).comp ((qbLoc hc Θ hQ hΘ).sp P).toRingHom with hf
    have e2 := congrArg f e1
    rw [map_sub, map_mul, map_natCast] at e2
    refine ⟨algebraMap (𝓞 F) _ t * w * f (z i), Subring.mul_mem _ (Subring.mul_mem _ (glo_algMap_int _ t) hw)
      ((((qbLoc hc Θ hQ hΘ).sp_int P (z i)).1 (qsp_locL_entry _ hz i)).1), ?_⟩
    have e3 : ((Ideal.absNorm (Ideal.span {qbDF hc Θ hQ hΘ P}) : ℕ) : (qv F P.1).adicCompletion F) =
        algebraMap (𝓞 F) _ t * (qbF hc hQ P (qbD hc Θ hQ hΘ P) * w) := by
      rw [← hDw, ← map_mul, ht, map_natCast]
    have e4 : f ((Pi.single j (1 : E ⊗[F] (qv F P.1).adicCompletion F) : Fin n → E ⊗[F] (qv F P.1).adicCompletion F) i) =
        (1 : Matrix (Fin n) (Fin n) ((qv F P.1).adicCompletion F)) i j := by
      rw [Pi.single_apply, Matrix.one_apply]; split_ifs <;> simp
    show f ((x : Matrix (Fin n) (Fin n) _) i j) - (1 : Matrix (Fin n) (Fin n) _) i j = _
    rw [← e4, e2, e3]
    ring
  · classical
    refine ⟨∏ P ∈ Q.attach, algebraMap (𝓞 F) (𝓞 E) (qbDF hc Θ hQ hΘ P), ?_, fun u _ sa hu P => ?_⟩
    · refine Finset.prod_ne_zero_iff.2 fun P _ h => (qbDF_prop hc Θ hQ hΘ P).1 ?_
      have hinj : Function.Injective (algebraMap (𝓞 F) E) := by
        rw [IsScalarTower.algebraMap_eq (𝓞 F) F E]
        exact (algebraMap F E).injective.comp (IsFractionRing.injective (𝓞 F) F)
      exact hinj (by rw [IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, h, map_zero, map_zero])
    obtain ⟨-, -, w, hw, hDw⟩ := qbDF_prop hc Θ hQ hΘ P
    apply qbU_of_K hc Θ hQ hΘ P
    apply qbK_of_div (qbF_d_int hc Θ hQ hΘ P) (qbF_d_lt hc Θ hQ hΘ P)
    intro i j
    set f : E ⊗[F] (qv F P.1).adicCompletion F →+* (qv F P.1).adicCompletion F :=
      (RingHom.fst _ _).comp ((qbLoc hc Θ hQ hΘ).sp P).toRingHom with hf
    have hφ : ∀ P' : Q, f (inclE (F := F) ((qv F P.1).adicCompletion F) (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) (qbDF hc Θ hQ hΘ P')))) =
        algebraMap (𝓞 F) _ (qbDF hc Θ hQ hΘ P') := fun P' => by
      show qbF hc hQ P _ = _
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E, qsp_sp_F hc P.1 _ (qbSp hc hQ P),
        ← IsScalarTower.algebraMap_apply]
    have hprod : f (inclE (F := F) ((qv F P.1).adicCompletion F) (algebraMap (𝓞 E) E
        (∏ P' ∈ Q.attach, algebraMap (𝓞 F) (𝓞 E) (qbDF hc Θ hQ hΘ P')))) =
        qbF hc hQ P (qbD hc Θ hQ hΘ P) * (w * ∏ P' ∈ Q.attach.erase P, algebraMap (𝓞 F) _ (qbDF hc Θ hQ hΘ P')) := by
      rw [map_prod, map_prod, map_prod]
      simp only [hφ]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_attach Q P), hDw, mul_assoc]
    refine ⟨w * (∏ P' ∈ Q.attach.erase P, algebraMap (𝓞 F) _ (qbDF hc Θ hQ hΘ P')) * f (prV (E := E) (qv F P.1) (sa i j : E ⊗[F] Formalism.L2.Herm.Af F)),
      Subring.mul_mem _ (Subring.mul_mem _ hw (Subring.prod_mem _ fun P' _ => glo_algMap_int _ _))
        ((((qbLoc hc Θ hQ hΘ).sp_int P _).1 (afsplit_prV_int (qv F P.1) _ (sa i j).2)).1), ?_⟩
    show f (prV (E := E) (qv F P.1) ((u : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j)) - (1 : Matrix (Fin n) (Fin n) _) i j = _
    rw [hu i j, map_add (f := _), map_add (f := _), map_mul, map_mul]
    have e4 : f (prV (E := E) (qv F P.1) ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j)) = (1 : Matrix (Fin n) (Fin n) _) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [e4, add_sub_cancel_left]
    show f (prV (E := E) (qv F P.1) (inclE (F := F) (Formalism.L2.Herm.Af F) _)) * _ = _
    rw [afsplit_prV_inclE, hprod]
    ring

end Open

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.XtIntAtQpow
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Loc1

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem xtEntB {q k₀ c' n' n : ℕ} (hc' : c' = 0) (x : HomE E (n' + c') (n + 0)) {p p' : ℕ} (hp : p < n) (hp' : p' < n') :
    LocE.entB q k₀ c' n' 0 n (fun i => i + 1) (fun i => i + 1) x p p' = x (Loc.eN E (n' + c') p') ⟨p, by omega⟩ := by
  subst hc'
  have hf : ∀ m s, LocE.fIdx k₀ 0 m s = s := by
    intro m s
    unfold LocE.fIdx
    split_ifs <;> omega
  simp [LocE.entB, hf, LocE.scE, Loc.atN, hp, hp']

theorem xtRes {c' n' p' : ℕ} (hp' : p' < n') :
    LinearMap.funLeft E E (Fin.castAdd c') (Loc.eN E (n' + c') p') = (Pi.single (⟨p', hp'⟩ : Fin n') (1 : E) : Sp E n') := by
  funext l
  simp [LinearMap.funLeft_apply, Loc.eN, Pi.single_apply, Fin.ext_iff]

theorem xtIntAt_qpow (q k : ℕ) : IntAt P ((q : E) ^ k) := by
  refine ⟨(q : 𝓞 E) ^ k, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
  simp


open Classical in
theorem xtLocal {q : ℕ} (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {k₀ c' n' n N : ℕ} (hc' : c' = 0)
    (Φ : Loc.SF E K (n' + c') (n + 0))
    (hcongr : ∀ x x' : HomE E (n' + c') (n + 0), (∀ p p', p < n + 0 → p' < n' → ∃ d, IntAt P d ∧
      LocE.entB q k₀ c' n' 0 n (fun i => i + 1) (fun i => i + 1) x' p p' =
        LocE.entB q k₀ c' n' 0 n (fun i => i + 1) (fun i => i + 1) x p p' + q * d) → Φ x' = Φ x)
    (hint : ∀ x : HomE E (n' + c') (n + 0), Φ x ≠ 0 → ∀ p p', p < n + 0 → p' < n' →
      IntAt P (LocE.entB q k₀ c' n' 0 n (fun i => i + 1) (fun i => i + 1) x p p'))
    (ψ : E → K) (D : ℕ) (hD : 1 ≤ D)
    (psi_add : ∀ x y : E, IntAt P ((q : E) ^ D * x) → IntAt P ((q : E) ^ D * y) → ψ (x + y) = ψ x * ψ y)
    (psi_int : ∀ x : E, IntAt P x → ψ x = 1) (ε : ℤ)
    (prX : Sp E N →ₗ[E] Sp E (n + 0)) (lastN : Sp E N →ₗ[E] E)
    (hsplit : ∀ a : Sp E N, (∀ i, IntAt P (a i)) ↔ (∀ i, IntAt P (prX a i)) ∧ IntAt P (lastN a))
    (zA : HomE E n' N) (zB : HomE E n' (n + 0)) (ηB : Sp E n' →ₗ[E] E)
    (H : ∀ j : Fin n', ((∀ i, IntAt P (zA (Pi.single j 1) i)) ↔ (∀ i, IntAt P (zB (Pi.single j 1) i)) ∧ IntAt P (ηB (Pi.single j 1))) ∧
      ((∀ i, IntAt P (zA (Pi.single j 1) i)) → (∀ i, redP P (prX (zA (Pi.single j 1)) i) = redP P (zB (Pi.single j 1) i)) ∧
        redP P (lastN (zA (Pi.single j 1))) = redP P (ηB (Pi.single j 1))))
    (y' : Sp E n') (hy : ∀ j, IntAt P ((q : E) * y' j)) :
    Φ (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd c')) *
        (if ∀ i : Fin n', IntAt P ((lastN ∘ₗ zA) (Pi.single i 1)) then ψ ((ε : E) * (lastN ∘ₗ zA) y') else 0) =
      Φ (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd c')) *
        (if ∀ i : Fin n', IntAt P (ηB (Pi.single i 1)) then ψ ((ε : E) * ηB y') else 0) := by
  subst hc'
  have hone : IntAt P (-1 : E) :=
    ⟨-1, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  have hneg : ∀ z : E, IntAt P z → IntAt P (-z) := fun z hz => by
    rw [← neg_one_mul]
    exact hone.mul hz
  have hqI : IntAt P (q : E) := by simpa using xtIntAt_qpow (P := P) q 1
  have hεI : IntAt P (ε : E) :=
    ⟨ε, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  have hq0 : (q : E) ≠ 0 := by
    intro h0
    apply hu
    have h1 : ((q : ℕ) : 𝓞 E) = 0 := by
      apply IsFractionRing.injective (𝓞 E) E
      rw [map_natCast, h0, map_zero]
    rw [h1]
    exact Submodule.zero_mem _
  have diff : ∀ a b : E, IntAt P a → IntAt P b → redP P b = redP P a →
      IntAt P ((b - a) / (q : E)) := by
    intro a b ha hb hab
    have hba : IntAt P (b - a) := by
      rw [sub_eq_add_neg]
      exact hb.add (hneg a ha)
    have hr0 : redP P (b - a) = 0 := by
      have h1 := reduction_add hba ha
      rw [sub_add_cancel, hab] at h1
      exact (add_eq_right.1 h1.symm)
    exact ciIntAt_div hq hu hba hr0
  have eX : ∀ p p' (hp : p < n) (hp' : p' < n'),
      LocE.entB q k₀ 0 n' 0 n (fun i => i + 1) (fun i => i + 1)
        (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) p p' =
        prX (zA (Pi.single ⟨p', hp'⟩ 1)) ⟨p, by omega⟩ := by
    intro p p' hp hp'
    rw [xtEntB rfl _ hp hp']
    simp only [LinearMap.comp_apply]
    rw [xtRes hp']
  have eY : ∀ p p' (hp : p < n) (hp' : p' < n'),
      LocE.entB q k₀ 0 n' 0 n (fun i => i + 1) (fun i => i + 1)
        (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) p p' =
        zB (Pi.single ⟨p', hp'⟩ 1) ⟨p, by omega⟩ := by
    intro p p' hp hp'
    rw [xtEntB rfl _ hp hp']
    simp only [LinearMap.comp_apply]
    rw [xtRes hp']
  have hexp : ∀ L : Sp E n' →ₗ[E] E, L y' = ∑ j, y' j * L (Pi.single j 1) := by
    intro L
    conv_lhs => rw [show y' = ∑ j, y' j • (Pi.single j (1 : E) : Sp E n') by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul, smul_eq_mul]
  by_cases hall : ∀ j : Fin n', ∀ i, IntAt P (zA (Pi.single j 1) i)
  · have hB := fun j => (H j).1.1 (hall j)
    have hl := fun j => ((hsplit _).1 (hall j)).2
    have hpr := fun j => ((hsplit _).1 (hall j)).1
    have hres := fun j => (H j).2 (hall j)
    rw [if_pos (show ∀ i : Fin n', IntAt P ((lastN ∘ₗ zA) (Pi.single i 1)) from fun i => hl i),
      if_pos (show ∀ i : Fin n', IntAt P (ηB (Pi.single i 1)) from fun i => (hB i).2)]
    have hΦ : Φ (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) =
        Φ (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) := by
      apply hcongr
      intro p p' hp hp'
      have hpn : p < n := by omega
      rw [eX p p' hpn hp', eY p p' hpn hp']
      refine ⟨_, diff _ _ ((hB ⟨p', hp'⟩).1 ⟨p, by omega⟩) (hpr ⟨p', hp'⟩ ⟨p, by omega⟩)
        ((hres ⟨p', hp'⟩).1 ⟨p, by omega⟩), ?_⟩
      field_simp
      try ring
    rw [hΦ]
    congr 1
    have hΔ : IntAt P ((lastN ∘ₗ zA) y' - ηB y') := by
      rw [hexp (lastN ∘ₗ zA), hexp ηB, ← Finset.sum_sub_distrib]
      refine ciIntAt_sum _ _ fun j _ => ?_
      have e : y' j * (lastN ∘ₗ zA) (Pi.single j 1) - y' j * ηB (Pi.single j 1) =
          ((q : E) * y' j) * (((lastN ∘ₗ zA) (Pi.single j 1) - ηB (Pi.single j 1)) / (q : E)) := by
        field_simp
        try ring
      rw [e]
      exact (hy j).mul (diff _ _ (hB j).2 (hl j) (hres j).2)
    have hqη : IntAt P ((q : E) * ηB y') := by
      rw [hexp ηB, Finset.mul_sum]
      refine ciIntAt_sum _ _ fun j _ => ?_
      rw [← mul_assoc]
      exact (hy j).mul (hB j).2
    have hD' : D = (D - 1) + 1 := by omega
    have h1 : IntAt P ((q : E) ^ D * ((ε : E) * ηB y')) := by
      have e : (q : E) ^ D * ((ε : E) * ηB y') = (ε : E) * (q : E) ^ (D - 1) * ((q : E) * ηB y') := by
        conv_lhs => rw [hD', pow_succ]
        ring
      rw [e]
      exact (hεI.mul (xtIntAt_qpow q (D - 1))).mul hqη
    have h2 : IntAt P ((q : E) ^ D * ((ε : E) * ((lastN ∘ₗ zA) y' - ηB y'))) := by
      rw [← mul_assoc, mul_comm ((q : E) ^ D), mul_assoc]
      exact hεI.mul ((xtIntAt_qpow q D).mul hΔ)
    have e : (ε : E) * (lastN ∘ₗ zA) y' = (ε : E) * ηB y' + (ε : E) * ((lastN ∘ₗ zA) y' - ηB y') := by
      ring
    rw [e, psi_add _ _ h1 h2, psi_int _ (hεI.mul hΔ), mul_one]
  · push_neg at hall
    obtain ⟨j, i, hji⟩ := hall
    have hnA : ¬ ∀ i, IntAt P (zA (Pi.single j 1) i) := fun h => hji (h i)
    have hnB : ¬ ((∀ i, IntAt P (zB (Pi.single j 1) i)) ∧ IntAt P (ηB (Pi.single j 1))) :=
      fun h => hnA ((H j).1.2 h)
    have hnS : ¬ ((∀ i, IntAt P (prX (zA (Pi.single j 1)) i)) ∧ IntAt P (lastN (zA (Pi.single j 1)))) :=
      fun h => hnA ((hsplit _).2 h)
    have L0 : Φ (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) *
        (if ∀ i : Fin n', IntAt P ((lastN ∘ₗ zA) (Pi.single i 1)) then
          ψ ((ε : E) * (lastN ∘ₗ zA) y') else 0) = 0 := by
      by_cases hl : IntAt P (lastN (zA (Pi.single j 1)))
      · have hpx : ¬ ∀ i, IntAt P (prX (zA (Pi.single j 1)) i) := fun h => hnS ⟨h, hl⟩
        push_neg at hpx
        obtain ⟨p, hp⟩ := hpx
        have h0 : Φ (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) = 0 := by
          by_contra h0
          have h3 := hint _ h0 p.1 j.1 p.2 j.2
          rw [eX p.1 j.1 (by omega) j.2] at h3
          exact hp h3
        rw [h0, zero_mul]
      · rw [if_neg (fun h => hl (h j)), mul_zero]
    have R0 : Φ (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) *
        (if ∀ i : Fin n', IntAt P (ηB (Pi.single i 1)) then ψ ((ε : E) * ηB y') else 0) = 0 := by
      by_cases hl : IntAt P (ηB (Pi.single j 1))
      · have hpx : ¬ ∀ i, IntAt P (zB (Pi.single j 1) i) := fun h => hnB ⟨h, hl⟩
        push_neg at hpx
        obtain ⟨p, hp⟩ := hpx
        have h0 : Φ (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) = 0 := by
          by_contra h0
          have h3 := hint _ h0 p.1 j.1 p.2 j.2
          rw [eY p.1 j.1 (by omega) j.2] at h3
          exact hp h3
        rw [h0, zero_mul]
      · rw [if_neg (fun h => hl (h j)), mul_zero]
    rw [L0, R0]

end Loc1

end Formalism.L2.Col
end
end

