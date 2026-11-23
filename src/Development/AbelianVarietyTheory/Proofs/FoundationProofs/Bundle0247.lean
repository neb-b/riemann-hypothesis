module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0234

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AugSpanOneMemOfOrthogonalThree
section
open scoped Matrix

namespace GlobalTheory.AugCore

variable {K : Type} [Field K] {Γ : Type} [Group Γ] {m : ℕ}

abbrev augSpan (S : Γ →* Matrix (Fin m) (Fin m) K) : Submodule K (Matrix (Fin m) (Fin m) K) :=
  Submodule.span K (Set.range fun g => S g - 1)

def Stable (S : Γ →* Matrix (Fin m) (Fin m) K) (P : Submodule K (Fin m → K)) : Prop :=
  ∀ g, ∀ v ∈ P, S g *ᵥ v ∈ P

theorem mul_mem_augSpan (S : Γ →* Matrix (Fin m) (Fin m) K) {A C : Matrix (Fin m) (Fin m) K}
    (hA : A ∈ augSpan S) (hC : C ∈ augSpan S) : A * C ∈ augSpan S := by
  induction hA using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    induction hC using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h, rfl⟩ := hy
      have e : (S g - 1) * (S h - 1) = (S (g * h) - 1) - (S g - 1) - (S h - 1) := by
        rw [map_mul]; noncomm_ring
      rw [e]
      exact Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩)
        (Submodule.subset_span ⟨_, rfl⟩)) (Submodule.subset_span ⟨_, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul a y _ hy => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ a hy
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [Matrix.smul_mul]; exact Submodule.smul_mem _ a hx

theorem augSpan_preserves (S : Γ →* Matrix (Fin m) (Fin m) K) {P : Submodule K (Fin m → K)}
    (hP : Stable S P) {T : Matrix (Fin m) (Fin m) K} (hT : T ∈ augSpan S) :
    ∀ v ∈ P, T *ᵥ v ∈ P := by
  induction hT using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    intro v hv
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact P.sub_mem (hP g v hv) hv
  | zero => intro v _; rw [Matrix.zero_mulVec]; exact P.zero_mem
  | add x y _ _ hx hy => intro v hv; rw [Matrix.add_mulVec]; exact P.add_mem (hx v hv) (hy v hv)
  | smul a x _ hx => intro v hv; rw [Matrix.smul_mulVec]; exact P.smul_mem a (hx v hv)

def Good (S : Γ →* Matrix (Fin m) (Fin m) K) (P : Submodule K (Fin m → K)) : Prop :=
  ∃ T ∈ augSpan S, ∀ v ∈ P, T *ᵥ v = v

theorem good_sup (S : Γ →* Matrix (Fin m) (Fin m) K) {L P : Submodule K (Fin m → K)}
    (hL : Stable S L) (hP : Stable S P) (gL : Good S L) (gP : Good S P) : Good S (L ⊔ P) := by
  obtain ⟨T₁, h₁, e₁⟩ := gL
  obtain ⟨T₂, h₂, e₂⟩ := gP
  refine ⟨T₁ + T₂ - T₁ * T₂, Submodule.sub_mem _ (Submodule.add_mem _ h₁ h₂)
    (mul_mem_augSpan S h₁ h₂), ?_⟩
  intro v hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  have hTa : T₂ *ᵥ a ∈ L := augSpan_preserves S hL h₂ a ha
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_add,
    e₁ a ha, e₂ b hb, e₁ _ hTa]
  abel

theorem good_bot (S : Γ →* Matrix (Fin m) (Fin m) K) : Good S ⊥ :=
  ⟨0, Submodule.zero_mem _, fun v hv => by
    rw [(Submodule.mem_bot K).mp hv, Matrix.mulVec_zero]⟩

theorem stable_inf (S : Γ →* Matrix (Fin m) (Fin m) K) {L P : Submodule K (Fin m → K)}
    (hL : Stable S L) (hP : Stable S P) : Stable S (L ⊓ P) :=
  fun g v hv => ⟨hL g v hv.1, hP g v hv.2⟩

theorem stable_orthogonal (S : Γ →* Matrix (Fin m) (Fin m) K)
    (B : LinearMap.BilinForm K (Fin m → K))
    (hinv : ∀ g v w, B (S g *ᵥ v) (S g *ᵥ w) = B v w) {Q : Submodule K (Fin m → K)}
    (hQ : Stable S Q) : Stable S (B.orthogonal Q) := by
  intro g v hv
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv ⊢
  intro n hn
  have e : S g *ᵥ (S g⁻¹ *ᵥ n) = n := by
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]
  have := hv _ (hQ g⁻¹ n hn)
  rw [← e, hinv]
  exact this

end GlobalTheory.AugCore

namespace GlobalTheory.AugCore

variable {K : Type} [Field K] {Γ : Type} [Group Γ]

theorem inf_orthogonal_eq_bot (S : Γ →* Matrix (Fin 3) (Fin 3) K)
    (B : LinearMap.BilinForm K (Fin 3 → K)) (hB : B.Nondegenerate)
    (hiso : ∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0)
    {Q : Submodule K (Fin 3 → K)} (hQ : Stable S Q) (hQo : Stable S (B.orthogonal Q)) :
    Q ⊓ B.orthogonal Q = ⊥ := by
  set Z := Q ⊓ B.orthogonal Q with hZ
  have hZs : Stable S Z := stable_inf S hQ hQo
  have hZle : Z ≤ B.orthogonal Z := by
    intro z hz
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hz.2) n hn.1
  have h3 : Module.finrank K (Fin 3 → K) = 3 := Module.finrank_fin_fun K
  have hfo : Module.finrank K (B.orthogonal Z) = 3 - Module.finrank K Z := by
    rw [LinearMap.BilinForm.finrank_orthogonal hB, h3]
  have hmono := Submodule.finrank_mono hZle
  by_contra hne
  obtain ⟨y, hyZ, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hsp : (K ∙ y) ≤ Z := (Submodule.span_singleton_le_iff_mem y Z).mpr hyZ
  have h1 : Module.finrank K (K ∙ y) = 1 := finrank_span_singleton hy0
  have hspm := Submodule.finrank_mono hsp
  have hZ1 : Module.finrank K Z = 1 := by omega
  have heq : (K ∙ y) = Z := Submodule.eq_of_le_of_finrank_eq hsp (by rw [h1, hZ1])
  apply hiso y hy0
  · intro g
    have : S g *ᵥ y ∈ (K ∙ y) := by rw [heq]; exact hZs g y hyZ
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
    exact ⟨c, hc.symm⟩
  · exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hyZ.2) y hyZ.1

theorem sup_orthogonal_eq_top (S : Γ →* Matrix (Fin 3) (Fin 3) K)
    (B : LinearMap.BilinForm K (Fin 3 → K)) (hB : B.Nondegenerate)
    (hiso : ∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0)
    {Q : Submodule K (Fin 3 → K)} (hQ : Stable S Q) (hQo : Stable S (B.orthogonal Q)) :
    Q ⊔ B.orthogonal Q = ⊤ := by
  have h3 : Module.finrank K (Fin 3 → K) = 3 := Module.finrank_fin_fun K
  have key := Submodule.finrank_sup_add_finrank_inf_eq Q (B.orthogonal Q)
  rw [inf_orthogonal_eq_bot S B hB hiso hQ hQo, finrank_bot,
    LinearMap.BilinForm.finrank_orthogonal hB, h3] at key
  have hle := Submodule.finrank_le Q
  rw [h3] at hle
  apply Submodule.eq_top_of_finrank_eq
  rw [h3]; omega

theorem good_of_stable (S : Γ →* Matrix (Fin 3) (Fin 3) K) [IsAlgClosed K]
    (B : LinearMap.BilinForm K (Fin 3 → K)) (hB : B.Nondegenerate)
    (hinv : ∀ g v w, B (S g *ᵥ v) (S g *ᵥ w) = B v w)
    (hfix : ∀ v : Fin 3 → K, (∀ g, S g *ᵥ v = v) → v = 0)
    (hiso : ∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0) :
    ∀ n, ∀ P : Submodule K (Fin 3 → K), Stable S P → Module.finrank K P = n → Good S P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hP hn
  by_cases hirr : ∀ Q : Submodule K (Fin 3 → K), Q ≤ P → Stable S Q → Q = ⊥ ∨ Q = P
  · by_cases hbot : P = ⊥
    · rw [hbot]; exact good_bot S
    · have hnt : ∃ g, ∃ v ∈ P, S g *ᵥ v ≠ v := by
        by_contra hc
        push_neg at hc
        apply hbot
        rw [Submodule.eq_bot_iff]
        intro v hv
        exact hfix v (fun g => hc g v hv)
      exact _root_.GlobalTheory.AugSpan.exists_mem_span_sub_one_eq_id_on S P hP hirr hnt
  · push_neg at hirr
    obtain ⟨Q, hQP, hQs, hQ0, hQne⟩ := hirr
    have hQo : Stable S (B.orthogonal Q) := stable_orthogonal S B hinv hQs
    set R := P ⊓ B.orthogonal Q with hR
    have hRs : Stable S R := stable_inf S hP hQo
    have htop := sup_orthogonal_eq_top S B hB hiso hQs hQo
    have hinf := inf_orthogonal_eq_bot S B hB hiso hQs hQo
    have hQR : Q ⊔ R = P := by
      apply le_antisymm (sup_le hQP inf_le_left)
      intro v hv
      have hvt : v ∈ Q ⊔ B.orthogonal Q := by rw [htop]; trivial
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hvt
      have hbP : b ∈ P := by
        have := P.sub_mem hv (hQP ha)
        simpa using this
      exact Submodule.mem_sup.mpr ⟨a, ha, b, ⟨hbP, hb⟩, rfl⟩
    have hQlt : Module.finrank K Q < n := by
      rw [← hn]; exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hQP hQne)
    have hRne : R ≠ P := by
      intro hRP
      apply hQ0
      rw [eq_bot_iff, ← hinf]
      intro x hx
      have : x ∈ R := by rw [hRP]; exact hQP hx
      exact ⟨hx, this.2⟩
    have hRlt : Module.finrank K R < n := by
      rw [← hn]; exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left hRne)
    have g := good_sup S hQs hRs (ih _ hQlt Q hQs rfl) (ih _ hRlt R hRs rfl)
    rwa [hQR] at g

end GlobalTheory.AugCore

theorem GlobalTheory.augSpan_one_mem_of_orthogonal_three : ∀ {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {Γ : Type} [Group Γ] (S : Γ →* Matrix (Fin 3) (Fin 3) K) (B : LinearMap.BilinForm K (Fin 3 → K)), B.Nondegenerate → B.IsSymm → (∀ g v w, B (S g *ᵥ v) (S g *ᵥ w) = B v w) → (∀ v : Fin 3 → K, (∀ g, S g *ᵥ v = v) → v = 0) → (∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0) → (1 : Matrix (Fin 3) (Fin 3) K) ∈ Submodule.span K (Set.range fun g => S g - 1) := by
  intro K _ _ _ Γ _ S B hB _ hinv hfix hiso
  obtain ⟨T, hT, hTv⟩ := GlobalTheory.AugCore.good_of_stable S B hB hinv hfix hiso _ ⊤
    (fun _ _ _ => trivial) rfl
  have e : T = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec]
    exact hTv v trivial
  exact (congrArg (· ∈ Submodule.span K (Set.range fun g => S g - 1)) e).mp hT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardParitySignLengthOfEq
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.NearerNeighbour

theorem exists_step {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (N : Submodule R M)
    [Finite (M ⧸ N)] (hN : N ≠ ⊤) :
    ∃ (P : Ideal R) (x : M), P.IsMaximal ∧ x ∉ N ∧ (∀ p ∈ P, p • x ∈ N) ∧
      (Module.length R (M ⧸ (N ⊔ Submodule.span R {x}))).toNat + 1 = (Module.length R (M ⧸ N)).toNat := by
  haveI : Nontrivial (M ⧸ N) := Submodule.Quotient.nontrivial_iff.2 hN
  haveI : IsArtinian R (M ⧸ N) := isArtinian_of_finite
  haveI : IsNoetherian R (M ⧸ N) := isNoetherian_of_finite R _
  obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule R (M ⧸ N))
  haveI hs : IsSimpleModule R S := isSimpleModule_iff_isAtom.2 hS
  obtain ⟨P, hP, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hs
  obtain ⟨x, hx⟩ := N.mkQ_surjective (e.symm 1 : S)
  have h0 : N.mkQ x ≠ 0 := by
    rw [hx]
    intro h
    have h1 : e.symm 1 = 0 := Subtype.ext h
    rw [LinearEquiv.map_eq_zero_iff] at h1
    exact hP.ne_top (Ideal.Quotient.zero_eq_one_iff.1 h1.symm)
  have hmap : (N ⊔ Submodule.span R {x}).map N.mkQ = S := by
    rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, Submodule.map_span, Set.image_singleton]
    refine (hS.le_iff.1 ?_).resolve_left ?_
    · rw [Submodule.span_singleton_le_iff_mem, hx]; exact (e.symm 1).2
    · rwa [Submodule.span_singleton_eq_bot]
  refine ⟨P, x, hP, fun h => h0 ((Submodule.Quotient.mk_eq_zero N).2 h), fun p hp => ?_, ?_⟩
  · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_smul, hx, ← Submodule.coe_smul, ← map_smul]
    have : p • (1 : R ⧸ P) = 0 := by
      rw [← Algebra.algebraMap_eq_smul_one]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hp
    rw [this, map_zero]; rfl
  · have h1 := Module.length_eq_add_of_exact S.subtype S.mkQ S.injective_subtype S.mkQ_surjective
      (LinearMap.exact_subtype_mkQ S)
    have h2 := (Submodule.quotientQuotientEquivQuotient N (N ⊔ Submodule.span R {x}) le_sup_left).length_eq
    rw [hmap] at h2
    have h3 : Module.length R ((M ⧸ N) ⧸ S) ≠ ⊤ := Module.length_ne_top
    rw [← h2, h1, Module.length_eq_one R S, ENat.toNat_add (by simp) h3, add_comm]
    simp

theorem exists_prime_mem {K : Type*} [Field K] [NumberField K] (P : Ideal (𝓞 K)) (hP : P.IsMaximal) :
    ∃ q : ℕ, q.Prime ∧ (q : 𝓞 K) ∈ P := by
  have hb : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  haveI : Finite (𝓞 K ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hb
  letI := Ideal.Quotient.field P
  refine ⟨ringChar (𝓞 K ⧸ P), CharP.prime_ringChar _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem exists_int_smul_mem {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V)
    (hL : Submodule.span K (L : Set V) = ⊤) (y : V) : ∃ m : ℤ, m ≠ 0 ∧ m • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.IntegerScalarIntegral.main
  | exact _root_.GlobalTheory.IntegerScalarIntegral.main
  | (apply _root_.GlobalTheory.IntegerScalarIntegral.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegerScalarIntegral.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegerScalarIntegral.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegerScalarIntegral.main ..)

theorem exists_nearer : ∀ (D : D7) (n : ℕ) (L₀ L : Lat D n), SD D L₀ → SD D L → L₀ ≠ L → ∃ (P : Ideal (𝓞 D.host.E)) (q : ℕ) (x : Fin n → D.host.E), P.IsMaximal ∧ q.Prime ∧ (q : 𝓞 D.host.E) ∈ P ∧ x ∈ L₀ ∧ NbD D P L x ∧ lenQ D L₀ (nbr D L x) + 1 = lenQ D L₀ L := by
  intro D n L₀ L h₀ h hne
  obtain ⟨fg₀, -, d₀⟩ := (sd_iff D L₀).1 h₀
  obtain ⟨-, sp, d⟩ := (sd_iff D L).1 h
  have hN : Submodule.comap L₀.subtype L ≠ ⊤ := by
    intro ht
    have hle : L₀ ≤ L := Submodule.comap_subtype_eq_top.1 ht
    exact hne (le_antisymm hle fun y hy => (d₀ y).2 fun x hx => (d y).1 hy x (hle hx))
  haveI : Module.Finite (𝓞 D.host.E) L₀ := Module.Finite.iff_fg.2 fg₀
  haveI : Module.Finite ℤ (L₀ ⧸ Submodule.comap L₀.subtype L) :=
    Module.Finite.trans (𝓞 D.host.E) _
  haveI : Finite (L₀ ⧸ Submodule.comap L₀.subtype L) := Module.finite_of_fg_torsion _ fun z => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨m, hm, hy⟩ := exists_int_smul_mem L sp y.1
    refine ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩, ?_⟩
    change m • (Submodule.mkQ (Submodule.comap L₀.subtype L) y) = 0
    rw [← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hy
  obtain ⟨P, x, hP, hx, hPx, hlen⟩ := exists_step _ hN
  obtain ⟨q, hq, hqP⟩ := exists_prime_mem P hP
  refine ⟨P, q, x.1, hP, hq, hqP, x.2, ⟨hx, hPx, (d₀ x.1).1 x.2 x.1 x.2⟩, ?_⟩
  have key : Submodule.comap L₀.subtype (nbr D L x.1) =
      Submodule.comap L₀.subtype L ⊔ Submodule.span (𝓞 D.host.E) {x} := by
    apply le_antisymm
    · intro y hy
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
      refine Submodule.mem_sup.2 ⟨y - c • x, ?_, c • x, Submodule.mem_span_singleton.2 ⟨c, rfl⟩, sub_add_cancel _ _⟩
      have : L₀.subtype (y - c • x) = a := by
        rw [map_sub, ← hab, map_smul]; exact add_sub_cancel_right _ _
      rw [Submodule.mem_comap, this]
      exact ha.1
    · refine sup_le (fun y hy => ?_) ?_
      · exact Submodule.mem_sup_left (S := nbM D L x.1) ⟨hy, (d₀ y.1).1 y.2 x.1 x.2⟩
      · rw [Submodule.span_singleton_le_iff_mem]
        exact Submodule.mem_sup_right (S := nbM D L x.1) (Submodule.mem_span_singleton_self _)
  unfold lenQ
  rw [key]
  exact hlen

end GlobalTheory.NearerNeighbour
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedStandardAdelicLatticeProperties
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators Pointwise

namespace GlobalTheory.CompletedLattice

variable (D : D7)

theorem moves_one (N : ℕ) : Moves D ((1 : GA D N) : GL (Fin N) (AE D)) (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
  rw [← h2]
  exact (h1 1).1

theorem pt_injective (cc : Ideal (𝓞 D.host.K)) {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ}
    {z z' : Matrix (Fin N') (Fin N) D.host.E}
    (h : pt D (tor0 D cc δ) δ z = pt D (tor0 D cc δ) δ z') : z = z' := by
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  refine Matrix.ext fun i j => ?_
  have h1 : δ * embT D τ (z i j) = δ * embT D τ (z' i j) := congrFun (congrFun (congrFun h τ) i) j
  exact (embT D τ).injective (mul_left_cancel₀ hδ h1)

theorem exists_mul_IhE_mem (cc : Ideal (𝓞 D.host.K)) :
    ∃ m : ℕ, 0 < m ∧ ∀ y ∈ IhE D cc, (m : AE D) * y ∈ OhE D := by
  have hb : D.host.𝔟 ≠ ⊥ := by
    intro h
    have h1 := D.host.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1
  have hB : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
    rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
  refine ⟨Ideal.absNorm D.host.𝔟, Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]), fun y hy => ?_⟩
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, -, a, ha, s, hs, rfl⟩ := hy
    rw [FractionalIdeal.mem_coe] at ha
    unfold Host.AA0 at ha
    rw [FractionalIdeal.mem_inv_iff hB] at ha
    have h1 := ha _ (FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.absNorm_mem D.host.𝔟))
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [map_natCast] at hr
    have h2 : inc D (r : D.host.E) ∈ OhE D := (AdLattice.incl_mem_iff (F := ℚ) _).2 ⟨r, rfl⟩
    have h3 : inc D ((c : D.host.K) : D.host.E) ∈ OhE D :=
      (AdLattice.incl_mem_iff (F := ℚ) _).2 ⟨algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c, rfl⟩
    have h4 : (Ideal.absNorm D.host.𝔟 : AE D) * (inc D ((((c : D.host.K) : D.host.E)) * a) * s) =
        inc D ((c : D.host.K) : D.host.E) * (inc D (r : D.host.E) * s) := by
      have : (r : D.host.E) = a * (Ideal.absNorm D.host.𝔟 : D.host.E) := hr
      rw [this, map_mul, map_mul, map_natCast]
      ring
    rw [h4]
    exact mul_mem h3 (mul_mem h2 hs)
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem completed_lattice : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ z : Matrix (Fin N') (Fin N) D.host.E, z.map (inc D) ∈ latA D cc N N' ↔ pt D (tor0 D cc δ) δ z ∈ La0 D (tor0 D cc δ) N N') ∧ (∀ x ∈ La0 D (tor0 D cc δ) N N', ∃ z, x = pt D (tor0 D cc δ) δ z) ∧ (∀ (ζ : XA D N N') (m : ℕ), 0 < m → ∃ z : Matrix (Fin N') (Fin N) D.host.E, ∃ a ∈ latA D cc N N', z.map (inc D) = ζ + m • a) ∧ (∀ ζ : XA D N N', ∃ m : ℕ, 0 < m ∧ m • ζ ∈ latA D cc N N') ∧ (∃ m : ℕ, 0 < m ∧ ∀ y ∈ IhE D cc, (m : AE D) * y ∈ OhE D) ∧ (∃ m : ℕ, 0 < m ∧ ∀ s ∈ OhE D, (m : AE D) * s ∈ IhE D cc) := by
  intro D hg cc δ hc N N'
  have hcc : cc ≠ ⊥ := hc.1.1
  have hδ : δ ≠ 0 := (GlobalTheory.CurveLattice.lattice_of_curve D hg cc δ hc).2.1
  have hn : 0 < Ideal.absNorm cc := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have hA := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hg cc δ hcc N N' 1 1 _ _ (moves_one D N) (moves_one D N')
  have hB := GlobalTheory.NormSum.pt_mem_La_of_adelic D hg cc δ hcc N N' 1 1 _ _ (moves_one D N) (moves_one D N')
  simp only [OneMemClass.coe_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] at hA hB
  refine ⟨fun z => ⟨fun h => hB z h, fun h => ?_⟩, fun x hx => ?_, fun ζ m hm => ?_, fun ζ => ?_,
    exists_mul_IhE_mem D cc, _, hn, GlobalTheory.AdelicApprox.absNorm_mul_mem_IhE D cc⟩
  · obtain ⟨z', h1, h2⟩ := hA _ h
    rw [pt_injective D cc hδ h1]
    exact h2
  · obtain ⟨z, h1, -⟩ := hA x hx
    exact ⟨z, h1⟩
  · choose e t ht h using fun (i : Fin N') (j : Fin N) => (GlobalTheory.AdelicApprox.approx_mod_ideal D cc hcc).1 (ζ i j) m hm
    refine ⟨Matrix.of e, Matrix.of t, ht, ?_⟩
    ext i j
    rw [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul, Matrix.of_apply, Matrix.of_apply, ← h]
    ring
  · choose n hn0 h using fun k : Fin N' × Fin N => GlobalTheory.AdelicApprox.exists_denom D (ζ k.1 k.2)
    refine ⟨Ideal.absNorm cc * ∏ k, n k, Nat.mul_pos hn (Finset.prod_pos fun k _ => hn0 k), fun i j => ?_⟩
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ (i, j))
    have h1 := GlobalTheory.AdelicApprox.absNorm_mul_mem_IhE D cc _ (mul_mem (natCast_mem (OhE D) c) (h (i, j)))
    rw [Matrix.smul_apply, nsmul_eq_mul, hc]
    convert h1 using 1
    push_cast
    ring

end GlobalTheory.CompletedLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMatrixProjectionSelfDualLattices
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.LatticeProjection

theorem isLocalizedModule_subtype {O E V : Type*} [CommRing O] [IsDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
    (B : Submodule O V) (hB : Submodule.span E (B : Set V) = ⊤) :
    IsLocalizedModule (nonZeroDivisors O) B.subtype := by
  refine ⟨fun s => ?_, fun v => ?_, fun {x y} h => ⟨1, by rw [Subtype.ext h]⟩⟩
  · exact (isLocalizedModule_id (nonZeroDivisors O) V E).map_units s
  · have hv : v ∈ Submodule.span E (B : Set V) := hB ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) E (B : Set V) v hv
    rw [Submodule.span_eq] at ht
    exact ⟨(⟨t • v, ht⟩, t), rfl⟩

theorem exists_linear_projection {O E V : Type*} [CommRing O] [IsDedekindDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
    (L₁ L₃ : Submodule O V) (h₁ : L₁.FG) (h₃ : L₃.FG)
    (hB : Submodule.span E ((L₁ ⊔ L₃ : Submodule O V) : Set V) = ⊤) :
    ∃ π : V →ₗ[E] V, ∀ v ∈ L₁ ⊔ L₃, π v ∈ L₁ ∧ v - π v ∈ L₃ := by
  set B := L₁ ⊔ L₃ with hBdef
  haveI : Module.Finite O B := Module.Finite.iff_fg.2 (h₁.sup h₃)
  haveI : Module.IsTorsionFree O V := Module.IsTorsionFree.trans_faithfulSMul O E V
  haveI : Module.FinitePresentation O B := Module.finitePresentation_of_finite O B
  haveI : Module.Flat O B := inferInstance
  haveI : Module.Projective O B := Module.Flat.projective_of_finitePresentation
  let p : (L₁ × L₃) →ₗ[O] B := LinearMap.coprod (Submodule.inclusion le_sup_left) (Submodule.inclusion le_sup_right)
  have hp : Function.Surjective p := by
    rintro ⟨v, hv⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p LinearMap.id hp
  let f : B →ₗ[O] V := L₁.subtype ∘ₗ LinearMap.fst O L₁ L₃ ∘ₗ s
  haveI := isLocalizedModule_subtype (E := E) B hB
  have hu := (isLocalizedModule_id (nonZeroDivisors O) V E).map_units
  let g : V →ₗ[O] V := IsLocalizedModule.lift (nonZeroDivisors O) B.subtype f hu
  refine ⟨g.extendScalarsOfIsLocalization (nonZeroDivisors O) E, fun v hv => ?_⟩
  have hg : g v = ((s ⟨v, hv⟩).1 : V) := IsLocalizedModule.lift_apply (nonZeroDivisors O) B.subtype f hu ⟨v, hv⟩
  have hsum : ((s ⟨v, hv⟩).1 : V) + ((s ⟨v, hv⟩).2 : V) = v :=
    congrArg Subtype.val (LinearMap.congr_fun hs ⟨v, hv⟩)
  rw [LinearMap.extendScalarsOfIsLocalization_apply', hg]
  refine ⟨(s ⟨v, hv⟩).1.2, ?_⟩
  rw [sub_eq_of_eq_add' hsum.symm]
  exact (s ⟨v, hv⟩).2.2

theorem exists_matrix_projection : ∀ (D : D7) (n : ℕ) (L₁ L₃ : Lat D n), SD D L₁ → SD D L₃ →
    ∃ π : Matrix (Fin n) (Fin n) D.host.E, (∀ v ∈ L₁ ⊔ L₃, π.mulVec v ∈ L₁) ∧ (∀ v ∈ L₃, π.mulVec v ∈ L₃) ∧
      ∀ v ∈ L₁, v - π.mulVec v ∈ L₃ := by
  intro D n L₁ L₃ h₁ h₃
  obtain ⟨f₁, s₁, -⟩ := (sd_iff D L₁).1 h₁
  obtain ⟨f₃, -, -⟩ := (sd_iff D L₃).1 h₃
  obtain ⟨π, hπ⟩ := exists_linear_projection (E := D.host.E) L₁ L₃ f₁ f₃
    (top_le_iff.1 (s₁ ▸ Submodule.span_mono (fun x hx => Submodule.mem_sup_left hx)))
  refine ⟨LinearMap.toMatrix' π, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩ <;>
    rw [LinearMap.toMatrix'_mulVec]
  · exact (hπ v hv).1
  · simpa using L₃.sub_mem hv (hπ v (Submodule.mem_sup_right hv)).2
  · exact (hπ v (Submodule.mem_sup_left hv)).2

end GlobalTheory.LatticeProjection
end
end

