module

public import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0003
public import Formalism.LocalToGlobal.GlobalTheory.GL6.ComplementSmulLocalExtensionMatrix

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.AdmissibleOfSplitAndRoundTrips
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open NumberField IsDedekindDomain Formalism.UG Classical Matrix Formalism.BasicNotions Formalism.L2.Forms
open scoped TensorProduct

section Prime

theorem subgroup_prime_card_eq_top {G : Type} [AddCommGroup G] {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p)
    (H : AddSubgroup G) {y : G} (hy : y ∈ H) (hy0 : y ≠ 0) : H = ⊤ := by
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact hp.ne_zero)
  have hd : Nat.card H ∣ p := hG ▸ AddSubgroup.card_addSubgroup_dvd_card H
  rcases (Nat.dvd_prime hp).1 hd with h | h
  · exact absurd (AddSubgroup.mem_bot.1 ((AddSubgroup.eq_bot_of_card_eq H h) ▸ hy)) hy0
  · exact AddSubgroup.eq_top_of_card_eq H (h.trans hG.symm)

theorem idempotent_action_prime_card {O : Type} [Ring O] {G : Type} [AddCommGroup G] [Module O G] {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p) {e : O} (he : e * e = e) : (∀ y : G, e • y = 0) ∨ (∀ y : G, e • y = y) := by
  by_cases h : ∀ y : G, e • y = 0
  · exact Or.inl h
  · obtain ⟨y0, hy0⟩ := not_forall.1 h
    right
    have htop := subgroup_prime_card_eq_top hp hG (DistribSMul.toAddMonoidHom G e).range ⟨y0, rfl⟩ hy0
    intro y
    have hy : y ∈ (DistribSMul.toAddMonoidHom G e).range := by rw [htop]; exact AddSubgroup.mem_top y
    obtain ⟨z, hz⟩ := AddMonoidHom.mem_range.1 hy
    rw [← hz]
    show e • e • z = e • z
    rw [smul_smul, he]

theorem unit_lift_int_prime_field {K : Type} [Field K] [Fintype K] {p : ℕ} (hp : p.Prime) (hK : Fintype.card K = p) (a : Kˣ) :
    ∃ k : ℤ, (k : K) = a ∧ ¬ (p : ℤ) ∣ k := by
  have hG : Nat.card K = p := by rw [Nat.card_eq_fintype_card, hK]
  have htop := subgroup_prime_card_eq_top hp hG (AddSubgroup.zmultiples (1 : K)) (AddSubgroup.mem_zmultiples 1) one_ne_zero
  have ha : (a : K) ∈ AddSubgroup.zmultiples (1 : K) := by rw [htop]; exact AddSubgroup.mem_top _
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 ha
  rw [zsmul_one] at hk
  refine ⟨k, hk, fun ⟨m, hm⟩ => a.ne_zero ?_⟩
  have hp0 : (p : K) = 0 := by
    have := card_nsmul_eq_zero' (G := K) (x := 1)
    rwa [hG, nsmul_eq_mul, mul_one] at this
  rw [← hk, hm, Int.cast_mul, Int.cast_natCast, hp0, zero_mul]

end Prime

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem int_not_mem_prime_over (v : HeightOneSpectrum (𝓞 F)) {T : ℕ} (hT : T.Prime) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {k : ℤ} (hk : ¬ (T : ℤ) ∣ k) : (k : 𝓞 F) ∉ v.asIdeal := by
  intro hkv
  have h1 : ¬ T ∣ k.natAbs := fun h => hk (Int.natCast_dvd.2 h)
  have h2 : Nat.Coprime T k.natAbs := (Nat.Prime.coprime_iff_not_dvd hT).2 h1
  have hcop : IsCoprime k (T : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact h2.symm
  obtain ⟨a, b, hab⟩ := hcop
  have hmem : ((a * k + b * (T : ℤ) : ℤ) : 𝓞 F) ∈ v.asIdeal := by
    push_cast
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hkv) (Ideal.mul_mem_left _ _ hv)
  rw [hab, Int.cast_one] at hmem
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hmem)

theorem valuation_int_not_mem_eq_one (v : HeightOneSpectrum (𝓞 F)) {k : ℤ} (hk : (k : 𝓞 F) ∉ v.asIdeal) :
    Valued.v (k : v.adicCompletion F) = 1 := by
  have h := v.valuedAdicCompletion_eq_valuation (K := F) (k : 𝓞 F)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hk] at h
  simpa using h

variable {n : ℕ} {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem scalar_mem_lattice_stabiliser {A : Type} [CommRing A] {S : Subring A} (Λ : Submodule S (Fin n → A))
    (g : GL (Fin n) A) (μ μ' : A) (hμ : μ ∈ S) (hμ' : μ' ∈ S) (h1 : μ' * μ = 1)
    (hg : ∀ x, (g : Matrix (Fin n) (Fin n) A) *ᵥ x = μ • x) : g ∈ stabGL Λ := by
  intro x
  rw [hg]
  constructor
  · intro hx
    exact Λ.smul_mem (⟨μ, hμ⟩ : S) hx
  · intro hx
    have h := Λ.smul_mem (⟨μ', hμ'⟩ : S) hx
    change μ' • μ • x ∈ Λ at h
    rwa [smul_smul, h1, one_smul] at h

theorem local_diamond_of_idempotent (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : ℤ) (c c' e : E ⊗[F] v.adicCompletion F)
    (hc : c ∈ intV E v) (hc' : c' ∈ intV E v) (he : e ∈ intV E v) (hee : e * e = e)
    (hσ : sigR σ (v.adicCompletion F) e = 1 - e) (hσc : sigR σ (v.adicCompletion F) c = c)
    (hσc' : sigR σ (v.adicCompletion F) c' = c') (hcc : c * c' = 1)
    (hkc : (k : E ⊗[F] v.adicCompletion F) * c = 1)
    (hact : ∀ y : S.fM v hv, (⟨e, he⟩ : intV E v) • y = y) : IsLocalDiamond S v hv k := by
  set μ : E ⊗[F] v.adicCompletion F := c * e + c' * (1 - e) with hμdef
  set μ' : E ⊗[F] v.adicCompletion F := c * (1 - e) + c' * e with hμ'def
  have hμμ' : μ * μ' = 1 := by
    rw [hμdef, hμ'def]
    linear_combination (-c ^ 2 + 2 * c * c' - c' ^ 2) * hee + hcc
  have hμ'μ : μ' * μ = 1 := by rw [mul_comm]; exact hμμ'
  have hσμ : sigR σ (v.adicCompletion F) μ = μ' := by
    rw [hμdef, hμ'def, map_add (f := _), map_mul, map_mul, map_sub, map_one, hσ, hσc, hσc']
    ring
  have hμO : μ ∈ intV E v :=
    add_mem (mul_mem hc he) (mul_mem hc' (sub_mem (one_mem _) he))
  have hμ'O : μ' ∈ intV E v :=
    add_mem (mul_mem hc (sub_mem (one_mem _) he)) (mul_mem hc' he)
  let M : GL (Fin n) (E ⊗[F] v.adicCompletion F) :=
    ⟨μ • (1 : Matrix (Fin n) (Fin n) _), μ' • (1 : Matrix (Fin n) (Fin n) _),
      by rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, hμμ', one_smul],
      by rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, hμ'μ, one_smul]⟩
  have hmv : ∀ x : Fin n → E ⊗[F] v.adicCompletion F, (M : Matrix (Fin n) (Fin n) _) *ᵥ x = μ • x := by
    intro x
    show (μ • (1 : Matrix (Fin n) (Fin n) _)) *ᵥ x = μ • x
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  have hcT : cT (sigR σ (v.adicCompletion F)) (μ • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))) =
      μ' • (1 : Matrix (Fin n) (Fin n) _) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [cT, hσμ]
    · simp [cT, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
  have hU : M ∈ UPts σ J (v.adicCompletion F) := by
    show cT (sigR σ (v.adicCompletion F)) (μ • (1 : Matrix (Fin n) (Fin n) _)) *
        J.map (inclE (F := F) (v.adicCompletion F)) * (μ • (1 : Matrix (Fin n) (Fin n) _)) =
      J.map (inclE (F := F) (v.adicCompletion F))
    rw [hcT, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hμ'μ,
      one_smul]
  have hL : M ∈ levelVL σ J v S.Lb := by
    show M ∈ UJ _ _ ⊓ stabGL _
    exact Subgroup.mem_inf.2 ⟨hU, scalar_mem_lattice_stabiliser _ M μ μ' hμO hμ'O hμ'μ hmv⟩
  have hg : M ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) :=
    scalar_mem_lattice_stabiliser _ M μ μ' hμO hμ'O hμ'μ hmv
  refine ⟨M, hL, hg, fun x => ?_⟩
  have hx : (⟨(M : Matrix (Fin n) (Fin n) _) *ᵥ x.1, (hg x.1).1 x.2⟩ : latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) = (⟨μ, hμO⟩ : intV E v) • x := by
    apply Subtype.ext
    exact (hmv x.1).trans rfl
  rw [hx, map_smul]
  set y := S.fT v hv x
  have hsplit : (⟨μ, hμO⟩ : intV E v) = ⟨c, hc⟩ * ⟨e, he⟩ + ⟨c', hc'⟩ * (1 - ⟨e, he⟩) := Subtype.ext rfl
  have h1e : (1 - (⟨e, he⟩ : intV E v)) • y = 0 := by rw [sub_smul, one_smul, hact y, sub_self]
  have hkO : ((k : intV E v)) * ⟨c, hc⟩ = 1 := by
    apply Subtype.ext
    simpa using hkc
  rw [hsplit, add_smul, mul_smul, mul_smul, h1e, smul_zero, add_zero, hact y, ← Int.cast_smul_eq_zsmul (intV E v),
    smul_smul, hkO, one_smul]

theorem local_diamond_of_split_idempotent (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) (hT : T.Prime) (k : ℤ) (hk : ¬ (T : ℤ) ∣ k) (e : E ⊗[F] v.adicCompletion F)
    (he : e ∈ intV E v) (hee : e * e = e) (hσ : sigR σ (v.adicCompletion F) e = 1 - e) : IsLocalDiamond S v hv k := by
  have hval := valuation_int_not_mem_eq_one v (int_not_mem_prime_over v hT hv hk)
  have hk0 : (k : v.adicCompletion F) ≠ 0 := by
    intro h; rw [h, map_zero] at hval; exact zero_ne_one hval
  have hkI : (k : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval]
  have hkI' : (k : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval, inv_one]
  have hR : ∀ y ∈ v.adicCompletionIntegers F, ((1 : E) ⊗ₜ[F] y) ∈ intV E v := fun y hy =>
    Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  have hσR : ∀ y : v.adicCompletion F, sigR σ (v.adicCompletion F) ((1 : E) ⊗ₜ[F] y) = (1 : E) ⊗ₜ[F] y := by
    intro y; simp [sigR]
  have hcc : ((1 : E) ⊗ₜ[F] (k : v.adicCompletion F)⁻¹) * ((1 : E) ⊗ₜ[F] (k : v.adicCompletion F)) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hk0, Algebra.TensorProduct.one_def]
  have hkA : ((k : E ⊗[F] v.adicCompletion F)) = (1 : E) ⊗ₜ[F] (k : v.adicCompletion F) := by
    rw [← Algebra.TensorProduct.includeRight_apply]
    exact (map_intCast _ k).symm
  have hkc : ((k : E ⊗[F] v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] (k : v.adicCompletion F)⁻¹) = 1 := by
    rw [hkA, mul_comm, hcc]
  rcases idempotent_action_prime_card hT (S.fM_card v hv) (e := (⟨e, he⟩ : intV E v)) (Subtype.ext hee) with h0 | h1
  · have he' : 1 - e ∈ intV E v := sub_mem (one_mem _) he
    refine local_diamond_of_idempotent S v hv k _ _ (1 - e) (hR _ hkI') (hR _ hkI) he' (by linear_combination hee)
      (by rw [map_sub, map_one, hσ]) (hσR _) (hσR _) hcc hkc (fun y => ?_)
    have : (⟨1 - e, he'⟩ : intV E v) = 1 - ⟨e, he⟩ := Subtype.ext rfl
    rw [this, sub_smul, one_smul, h0 y, sub_zero]
  · exact local_diamond_of_idempotent S v hv k _ _ e (hR _ hkI') (hR _ hkI) he hee hσ (hσR _) (hσR _) hcc hkc h1

end Local

section Tied

variable {D : D7} {u : D.what₂.Word}

def SplitAtT (A : AtTTied u) : Prop :=
  ∀ v : (D.mem u).A.vT, ∃ e ∈ intV D.host.E (A.eV v).1, e * e = e ∧
    sigR (sigD D) ((A.eV v).1.adicCompletion D.host.F) e = 1 - e

theorem local_diamonds_of_split (Tf : FormsTied D u) (hs : SplitAtT Tf.atT) : LocalDiamondElementsExist Tf := by
  intro i hi v a
  obtain ⟨k, hk, hkT⟩ := unit_lift_int_prime_field (D.mem u).A.T_prime ((D.mem u).A.card_Fv v) a
  obtain ⟨e, he, hee, hσ⟩ := hs v
  exact ⟨k, hk, local_diamond_of_split_idempotent (Tf.cls i hi).lev _ _ (D.mem u).A.T_prime k hkT e he hee hσ⟩

theorem diamond_elements_of_split (Tf : FormsTied D u) (hs : SplitAtT Tf.atT) : DiamondElementsExist Tf :=
  diamond_elements_of_local Tf (local_diamonds_of_split Tf hs)

end Tied

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.FrameTranslate
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem rnd_tr_tr (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (a b : GL (Fin n) E) (ha : a ∈ UJ (σ : E →+* E) J) (hb : b ∈ UJ (σ : E →+* E) J) (y : Frames (gramC J emb)) :
    frameTranslate emb hc a ha (frameTranslate emb hc b hb y) = frameTranslate emb hc (a * b) ((UJ (σ : E →+* E) J).mul_mem ha hb) y := by
  apply Subtype.ext
  funext τ
  simp only [frameTranslate, atInf, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem rnd_tr_one (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (y : Frames (gramC J emb)) : frameTranslate emb hc 1 (UJ (σ : E →+* E) J).one_mem y = y := by
  apply Subtype.ext
  funext τ
  simp [frameTranslate, atInf]

theorem rnd_tr_congr (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    {a b : GL (Fin n) E} (hab : a = b) (ha : a ∈ UJ (σ : E →+* E) J) (hb : b ∈ UJ (σ : E →+* E) J)
    (y : Frames (gramC J emb)) : frameTranslate emb hc a ha y = frameTranslate emb hc b hb y := by
  subst hab; rfl

end Gen

section Fill

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

def RndStabTriv (S : StepLevel F E σ J T f bad) (x0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : Prop :=
  ∀ δ : GL (Fin n) E, δ ∈ UJ (σ : E →+* E) J → ∀ κ : S.U,
    bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) δ * x0.1 = x0.1 * κ.1 → δ = 1

theorem rnd_uniq (S : StepLevel F E σ J T f bad) (x0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hs : RndStabTriv S x0)
    {a b : GL (Fin n) E} (ha : a ∈ UJ (σ : E →+* E) J) (hb : b ∈ UJ (σ : E →+* E) J) {k l : S.U}
    (h : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) a * x0.1 * k.1 =
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) b * x0.1 * l.1) : a = b ∧ k = l := by
  have hδ : b⁻¹ * a ∈ UJ (σ : E →+* E) J := (UJ (σ : E →+* E) J).mul_mem ((UJ (σ : E →+* E) J).inv_mem hb) ha
  have e : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (b⁻¹ * a) * x0.1 = x0.1 * (l * k⁻¹ : S.U).1 := by
    have h' : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) a * x0.1 =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) b * x0.1 * l.1 * k.1⁻¹ := by
      rw [← h]; group
    rw [map_mul, map_inv, Subgroup.coe_mul, InvMemClass.coe_inv, mul_assoc, h']; group
  have h1 := hs _ hδ _ e
  have hab : a = b := (inv_mul_eq_one.1 h1).symm
  subst hab
  exact ⟨rfl, Subtype.ext (mul_left_cancel h)⟩


open Classical in
def rndFillG (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (x0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (h : Frames (gramC J emb) → ℂ) :
    UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ := fun x y =>
  if hx : ∃ p : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U,
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) p.1.1 * x0.1 * p.2.1 then
    (S.chi (Classical.choose hx).2 : ℂ) *
      h (frameTranslate emb hc (Classical.choose hx).1.1⁻¹ ((UJ (σ : E →+* E) J).inv_mem (Classical.choose hx).1.2) y)
  else 0

theorem rnd_fillG_eq (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (x0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hs : RndStabTriv S x0) (h : Frames (gramC J emb) → ℂ)
    (x : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (p : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U)
    (hp : x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) p.1.1 * x0.1 * p.2.1) (y : Frames (gramC J emb)) :
    rndFillG S emb hc x0 h x y =
      (S.chi p.2 : ℂ) * h (frameTranslate emb hc p.1.1⁻¹ ((UJ (σ : E →+* E) J).inv_mem p.1.2) y) := by
  have hx : ∃ p : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U,
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) p.1.1 * x0.1 * p.2.1 := ⟨p, hp⟩
  unfold rndFillG
  rw [dite_eq_left hx]
  have hq := Classical.choose_spec hx
  have hu := rnd_uniq S x0 hs (Classical.choose hx).1.2 p.1.2 (k := (Classical.choose hx).2) (l := p.2)
    (by rw [← hq, ← hp])
  have hpq : Classical.choose hx = p := Prod.ext (Subtype.ext hu.1) hu.2
  exact congrArg (fun q : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U =>
    (S.chi q.2 : ℂ) * h (frameTranslate emb hc q.1.1⁻¹ ((UJ (σ : E →+* E) J).inv_mem q.1.2) y)) hpq

theorem rnd_fillG_eq' (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (x0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hs : RndStabTriv S x0) (h : Frames (gramC J emb) → ℂ)
    (x : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (a : GL (Fin n) E) (ha : a ∈ UJ (σ : E →+* E) J) (k : S.U)
    (hp : x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) a * x0.1 * k.1) (y : Frames (gramC J emb)) :
    rndFillG S emb hc x0 h x y = (S.chi k : ℂ) * h (frameTranslate emb hc a⁻¹ ((UJ (σ : E →+* E) J).inv_mem ha) y) :=
  rnd_fillG_eq S emb hc x0 hs h x (⟨a, ha⟩, k) hp y

theorem rnd_fill_at (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (x0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hs : RndStabTriv S x0) (h : Frames (gramC J emb) → ℂ) :
    rndFillG S emb hc x0 h x0 = h := by
  funext y
  rw [rnd_fillG_eq S emb hc x0 hs h x0 (⟨1, (UJ (σ : E →+* E) J).one_mem⟩, 1) (by simp) y, map_one, Units.val_one,
    one_mul, rnd_tr_congr emb hc (inv_one) _ (UJ (σ : E →+* E) J).one_mem, rnd_tr_one]

open Classical in
theorem rnd_fill_mem (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (x0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hs : RndStabTriv S x0) (h : Frames (gramC J emb) → ℂ) :
    rndFillG S emb hc x0 h ∈ AdFun S emb := by
  intro γ hγ x x' κ hx y y' hy
  have hy' : y' = frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y := by
    apply Subtype.ext; funext τ
    show y'.1 τ = atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ
    rw [hy τ, ← Matrix.mul_assoc]
    simp only [atInf]
    rw [← Matrix.map_mul, Units.inv_mul]; simp
  by_cases h1 : ∃ p : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U,
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) p.1.1 * x0.1 * p.2.1
  · obtain ⟨p, hp⟩ := h1
    have hp' : x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ * p.1.1) * x0.1 * (p.2 * κ).1 := by
      simp only [hx, hp, map_mul, Subgroup.coe_mul]; group
    rw [rnd_fillG_eq' S emb hc x0 hs h x' (γ * p.1.1) ((UJ (σ : E →+* E) J).mul_mem hγ p.1.2) (p.2 * κ) hp' y, rnd_fillG_eq S emb hc x0 hs h x p hp y', map_mul, Units.val_mul,
      rnd_tr_congr emb hc (mul_inv_rev γ p.1.1) _
        ((UJ (σ : E →+* E) J).mul_mem ((UJ (σ : E →+* E) J).inv_mem p.1.2) ((UJ (σ : E →+* E) J).inv_mem hγ)),
      ← rnd_tr_tr, ← hy']
    ring
    · exact (UJ (σ : E →+* E) J).inv_mem p.1.2
    · exact (UJ (σ : E →+* E) J).inv_mem hγ
  · have h2 : ¬ ∃ p : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U,
        x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) p.1.1 * x0.1 * p.2.1 := by
      rintro ⟨p, hp⟩
      refine h1 ⟨(⟨γ⁻¹ * p.1.1, (UJ (σ : E →+* E) J).mul_mem ((UJ (σ : E →+* E) J).inv_mem hγ) p.1.2⟩, p.2 * κ⁻¹), ?_⟩
      have : x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ⁻¹ * x'.1 * κ.1⁻¹ := by rw [hx, map_inv]; group
      rw [this, hp, map_mul, map_inv, Subgroup.coe_mul, InvMemClass.coe_inv]; group
    unfold rndFillG
    rw [dite_eq_right h1, dite_eq_right h2, mul_zero]

end Fill

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.ValuationClassTranslateMem
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open Formalism.GradedWeylDivisibility (blockAct)

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem valuation_class_translate_mem (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (lam : ι → DomWeight n) (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) {V : Frames (gramC J emb) → ℂ}
    (hV : V ∈ ValC (gramC J emb) lam) :
    (fun y => V (frameTranslate emb hc γ hγ y)) ∈ ValC (gramC J emb) lam := by
  obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.1 hV
  refine Submodule.mem_map.2 ⟨(∏ τ, (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ).det ^ shiftOf lam τ) •
    blockAct ℂ (atInf emb (γ : Matrix (Fin n) (Fin n) E)) P,
    Submodule.smul_mem _ _ (complex_span_block_action_stable lam _ hP), ?_⟩
  rw [← Formalism.L2.Col.fnOf_mul]
  funext y
  simp only [fnOf, frameTranslate, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.mul_one, Matrix.one_mul]

theorem class_rep_translate_unique (S : StepLevel F E σ J T f bad) {C : Type} (yc : C → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hinj : Function.Injective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (hstab : ∀ c (γ : GL (Fin n) E), γ ∈ UJ (σ : E →+* E) J →
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ ∈ S.U.map (MulAut.conj (yc c).1).toMonoidHom → γ = 1)
    (c1 c2 : C) (γ1 γ2 : GL (Fin n) E) (h1 : γ1 ∈ UJ (σ : E →+* E) J) (h2 : γ2 ∈ UJ (σ : E →+* E) J)
    (κ1 κ2 : S.U)
    (e : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 * (yc c1).1 * κ1.1 =
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ2 * (yc c2).1 * κ2.1) :
    c1 = c2 ∧ γ1 = γ2 ∧ κ1 = κ2 := by
  have hU : ∀ κ : S.U, κ.1 ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := fun κ => ((S.U_eq κ.1).1 κ.2).1
  set k : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨κ1.1 * κ2.1⁻¹, (UPts _ _ _).mul_mem (hU κ1) ((UPts _ _ _).inv_mem (hU κ2))⟩
  set h : UPts σ J (FiniteAdeleRing (𝓞 F) F) := yc c2 * k⁻¹ * (yc c1)⁻¹
  have hh : h.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ2⁻¹ * γ1) := by
    simp only [h, k, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    have e' : (yc c2).1 = (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ2)⁻¹ *
        (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 * (yc c1).1 * κ1.1) * κ2.1⁻¹ := by
      rw [e]; group
    rw [e']; group
  have hc : c1 = c2 := by
    apply hinj
    show (Quotient.mk'' (yc c1) : Cls S) = Quotient.mk'' (yc c2)
    refine (@DoubleCoset.eq _ _ _ _ (yc c1) (yc c2)).2 ⟨h, ?_, k, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ2⁻¹ * γ1, (UJ _ _).mul_mem ((UJ _ _).inv_mem h2) h1, hh.symm⟩)
    · exact Subgroup.mem_subgroupOf.2 (S.U.mul_mem κ1.2 (S.U.inv_mem κ2.2))
    · simp only [h]; group
  subst hc
  have hγ : γ2⁻¹ * γ1 = 1 := by
    apply hstab c1 _ ((UJ _ _).mul_mem ((UJ _ _).inv_mem h2) h1)
    refine Subgroup.mem_map.2 ⟨κ2.1 * κ1.1⁻¹, S.U.mul_mem κ2.2 (S.U.inv_mem κ1.2), ?_⟩
    show (yc c1).1 * (κ2.1 * κ1.1⁻¹) * (yc c1).1⁻¹ = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ2⁻¹ * γ1)
    rw [map_mul, map_inv]
    have e' : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ2 * (yc c1).1 * κ2.1 * κ1.1⁻¹ * (yc c1).1⁻¹ := by
      rw [← e]; group
    rw [e']; group
  have hγ' : γ1 = γ2 := by
    have := congrArg (γ2 * ·) hγ
    simpa [← mul_assoc] using this
  subst hγ'
  refine ⟨rfl, rfl, Subtype.ext ?_⟩
  have := e
  rw [mul_assoc, mul_assoc] at this
  exact mul_left_cancel (mul_left_cancel this)

theorem adelic_function_ext (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (lam : ι → DomWeight n) {C : Type}
    (yc : C → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hbij : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (hstab : ∀ c (γ : GL (Fin n) E), γ ∈ UJ (σ : E →+* E) J →
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ ∈ S.U.map (MulAut.conj (yc c).1).toMonoidHom → γ = 1)
    (φ : C → Frames (gramC J emb) → ℂ) (hφ : ∀ c, φ c ∈ ValC (gramC J emb) lam) :
    φ ∈ FiC S emb lam yc := by
  have hdec : ∀ x : UPts σ J (FiniteAdeleRing (𝓞 F) F), ∃ c, ∃ γ : GL (Fin n) E, ∃ _ : γ ∈ UJ (σ : E →+* E) J,
      ∃ κ : S.U, x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (yc c).1 * κ.1 := by
    intro x
    obtain ⟨c, hcx⟩ := hbij.2 (Quotient.mk'' x)
    obtain ⟨hh, hhH, κ, hκK, e⟩ := (@DoubleCoset.eq _ _ _ _ (yc c) x).1 hcx
    obtain ⟨g, hgU, hge⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhH)
    refine ⟨c, g, hgU, ⟨κ.1, hκK⟩, ?_⟩
    have := congrArg Subtype.val e
    simp only [Subgroup.coe_mul] at this
    rw [this, hge]
  choose cx γx hγx κx hx using hdec
  have hun := class_rep_translate_unique S yc hbij.1 hstab
  refine Submodule.mem_map.2 ⟨fun x y => (S.chi (κx x) : ℂ) *
    φ (cx x) (frameTranslate emb hc (γx x)⁻¹ ((UJ _ _).inv_mem (hγx x)) y), Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  ·
    intro γ' hγ' x x' κ' hx' y y' hy
    obtain ⟨hc2, hg2, hk2⟩ := hun (cx x') (cx x) (γx x') (γ' * γx x) (hγx x') ((UJ _ _).mul_mem hγ' (hγx x))
      (κx x') (κx x * κ') (by
        rw [← hx x', hx', hx x, map_mul, Subgroup.coe_mul]; group)
    have hfr : frameTranslate emb hc (γx x')⁻¹ ((UJ _ _).inv_mem (hγx x')) y =
        frameTranslate emb hc (γx x)⁻¹ ((UJ _ _).inv_mem (hγx x)) y' := by
      apply Subtype.ext
      funext τ
      show atInf emb (((γx x')⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ =
        atInf emb (((γx x)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y'.1 τ
      rw [hy τ, hg2, _root_.mul_inv_rev]
      simp only [atInf, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    show (S.chi (κx x') : ℂ) * φ (cx x') (frameTranslate emb hc (γx x')⁻¹ ((UJ _ _).inv_mem (hγx x')) y) =
      (S.chi κ' : ℂ) * ((S.chi (κx x) : ℂ) * φ (cx x) (frameTranslate emb hc (γx x)⁻¹ ((UJ _ _).inv_mem (hγx x)) y'))
    rw [hfr, hc2, hk2, map_mul, Units.val_mul]
    ring
  · refine Submodule.mem_pi.2 fun x _ => ?_
    exact Submodule.smul_mem _ _ (valuation_class_translate_mem emb hc lam _ _ (hφ (cx x)))
  · funext c y
    obtain ⟨hc1, hg1, hk1⟩ := hun (cx (yc c)) c (γx (yc c)) 1 (hγx (yc c)) (UJ _ _).one_mem (κx (yc c)) 1 (by
      rw [← hx (yc c), map_one]; simp)
    show (S.chi (κx (yc c)) : ℂ) * φ (cx (yc c)) (frameTranslate emb hc (γx (yc c))⁻¹ ((UJ _ _).inv_mem (hγx (yc c))) y) = φ c y
    have hfr : frameTranslate emb hc (γx (yc c))⁻¹ ((UJ _ _).inv_mem (hγx (yc c))) y = y := by
      apply Subtype.ext
      funext τ
      show atInf emb (((γx (yc c))⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ = y.1 τ
      rw [hg1, inv_one]
      simp [atInf]
    rw [hfr, hc1, hk1, map_one, Units.val_one, one_mul]

end Gen

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

