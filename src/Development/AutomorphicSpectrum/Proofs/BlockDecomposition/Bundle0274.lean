module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsAffineOpenPreimageEqOfIsNilpotent
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0021

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningVeryAmpleOpensExist
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem basicOpen_rs {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) :
    X.basicOpen (rs X h f) = V ⊓ X.basicOpen f :=
  Scheme.basicOpen_res X f (homOfLE h).op

theorem mem_nonzeroLocus_iff {X : Scheme.{0}} {H : LB X} (s : LB.Sec H) (x : X) :
    x ∈ nonzeroLocus s ↔ ∃ k, x ∈ X.basicOpen (s.f k) :=
  TopologicalSpace.Opens.mem_iSup

theorem basicOpen_eq_inf_nonzeroLocus {X : Scheme.{0}} {H : LB X} (a b : LB.Sec H)
    (r : Γ(X, nonzeroLocus a))
    (hr : ∀ k, rs X (inf_le_right : nonzeroLocus a ⊓ H.U k ≤ H.U k) (b.f k) =
      rs X (inf_le_left : nonzeroLocus a ⊓ H.U k ≤ nonzeroLocus a) r *
        rs X (inf_le_right : nonzeroLocus a ⊓ H.U k ≤ H.U k) (a.f k)) :
    X.basicOpen r = nonzeroLocus a ⊓ nonzeroLocus b := by
  have key : ∀ (k : H.ι) (x : X), x ∈ nonzeroLocus a → x ∈ H.U k →
      (x ∈ X.basicOpen (b.f k) ↔ x ∈ X.basicOpen r ∧ x ∈ X.basicOpen (a.f k)) := by
    intro k x hxa hxk
    have h := congrArg X.basicOpen (hr k)
    rw [Scheme.basicOpen_mul, basicOpen_rs, basicOpen_rs, basicOpen_rs] at h
    have hx : x ∈ nonzeroLocus a ⊓ H.U k := ⟨hxa, hxk⟩
    constructor
    · intro hb
      have : x ∈ (nonzeroLocus a ⊓ H.U k) ⊓ X.basicOpen (b.f k) := ⟨hx, hb⟩
      rw [h] at this
      exact ⟨this.1.2, this.2.2⟩
    · rintro ⟨h₁, h₂⟩
      have : x ∈ (nonzeroLocus a ⊓ H.U k ⊓ X.basicOpen r) ⊓
          (nonzeroLocus a ⊓ H.U k ⊓ X.basicOpen (a.f k)) := ⟨⟨hx, h₁⟩, ⟨hx, h₂⟩⟩
      rw [← h] at this
      exact this.2
  apply le_antisymm
  · intro x hx
    have hxa : x ∈ nonzeroLocus a := X.basicOpen_le r hx
    obtain ⟨k, hk⟩ := (mem_nonzeroLocus_iff a x).1 hxa
    exact ⟨hxa, (mem_nonzeroLocus_iff b x).2
      ⟨k, (key k x hxa (X.basicOpen_le _ hk)).2 ⟨hx, hk⟩⟩⟩
  · rintro x ⟨hxa, hxb⟩
    obtain ⟨k, hk⟩ := (mem_nonzeroLocus_iff b x).1 hxb
    exact ((key k x hxa (X.basicOpen_le _ hk)).1 hk).1

theorem exists_basicOpen_eq_inf_iInf {X : Scheme.{0}} {H : LB X} {m : ℕ}
    (s : Fin (m + 1) → LB.Sec H) (i : Fin (m + 1))
    (hi : ∀ j, ∃ r : Γ(X, nonzeroLocus (s i)),
      X.basicOpen r = nonzeroLocus (s i) ⊓ nonzeroLocus (s j))
    (S : Finset (Fin (m + 1))) :
    ∃ f : Γ(X, nonzeroLocus (s i)),
      X.basicOpen f = nonzeroLocus (s i) ⊓ ⨅ j ∈ S, nonzeroLocus (s j) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert j S _ ih =>
    obtain ⟨f, hf⟩ := ih
    obtain ⟨r, hr⟩ := hi j
    refine ⟨f * r, ?_⟩
    rw [Scheme.basicOpen_mul, hf, hr, Finset.iInf_insert]
    ext x
    simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe]
    tauto

theorem isAffineOpen_iInf_nonzeroLocus {X : Scheme.{0}} {R : Type} [CommRing R]
    {f : X ⟶ Spec (CommRingCat.of R)} {H : LB X} {m : ℕ} {s : Fin (m + 1) → LB.Sec H}
    (h : VeryAmpleBy f H s) {S : Finset (Fin (m + 1))} (hS : S.Nonempty) :
    IsAffineOpen (⨅ i ∈ S, nonzeroLocus (s i)) := by
  obtain ⟨i, hi⟩ := hS
  obtain ⟨hA, r, hr, -⟩ := h.2 i
  obtain ⟨g, hg⟩ := exists_basicOpen_eq_inf_iInf s i
    (fun j => ⟨r j, basicOpen_eq_inf_nonzeroLocus (s i) (s j) (r j) (hr j)⟩) S
  have e : ⨅ j ∈ S, nonzeroLocus (s j) = X.basicOpen g := by
    rw [hg]
    exact (inf_eq_right.2 (iInf₂_le i hi)).symm
  rw [e]
  exact hA.basicOpen g

theorem surjective_spec_of_nilpotent_ker {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A')
    (hg : Function.Surjective g) (hn : IsNilpotent (RingHom.ker g)) :
    Surjective (Spec.map (CommRingCat.ofHom g)) := by
  refine ⟨fun (x : PrimeSpectrum A) ↦ ?_⟩
  have : x ∈ Set.range (PrimeSpectrum.comap g) := by
    rw [_root_.range_comap_of_surjective _ _ hg]
    obtain ⟨n, hn⟩ := hn
    intro a ha
    apply x.isPrime.mem_of_pow_mem n
    have : a ^ n ∈ RingHom.ker g ^ n := Ideal.pow_mem_pow ha n
    rw [hn] at this
    rw [show a ^ n = 0 from this]
    exact zero_mem _
  exact this

theorem isNilpotent_ker_factor {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1)))) := by
  refine ⟨2, ?_⟩
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, ← pow_mul]
  change _ = ⊥
  rw [eq_bot_iff, ← Ideal.map_quotient_self (I ^ (e + 1 + 1))]
  exact Ideal.map_mono (Ideal.pow_le_pow_right (by omega))

theorem exists_orderIso_opens {X X' : Scheme.{0}} (β : X ⟶ X') [IsClosedImmersion β]
    [Surjective β] : ∃ Φ : X.Opens ≃o X'.Opens, ∀ U, β ⁻¹ᵁ Φ U = U := by
  let h : X ≃ₜ X' := (β.isClosedEmbedding.isEmbedding).toHomeomorphOfSurjective β.surjective
  refine ⟨h.opensCongr, fun U => ?_⟩
  ext x
  have e : h.symm (β x) = x := h.symm_apply_apply x
  simp [h] at e ⊢
  rw [e]

theorem exists_orderIso_opens_tower (X : ℕ → Scheme.{0}) (β : ∀ e, X e ⟶ X (e + 1))
    [∀ e, IsClosedImmersion (β e)] [∀ e, Surjective (β e)] :
    ∃ G : ∀ e, (X 0).Opens ≃o (X e).Opens, (∀ U, G 0 U = U) ∧
      ∀ e U, β e ⁻¹ᵁ G (e + 1) U = G e U := by
  choose Φ hΦ using fun e => exists_orderIso_opens (β e)
  let G : ∀ e, (X 0).Opens ≃o (X e).Opens := fun e =>
    Nat.rec (OrderIso.refl _) (fun e G => G.trans (Φ e)) e
  exact ⟨G, fun _ => rfl, fun e U => hΦ e (G e U)⟩

theorem exists_basicOpens_of_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H : LB (Y 0).left) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → VeryAmpleBy (Y 0).hom H s → ∃ D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens, (∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) ∧ (∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) ∧ (∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) ∧ (∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) ∧ (∀ e, ⨆ i, D e {i} = ⊤) ∧ (∀ e S, S.Nonempty → IsAffineOpen (D e S)) := by
  intro R _ I Y β hβ H m s _ hV
  have hg := fun e => Ideal.Quotient.factor_surjective
    (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))
  have hci : ∀ e, IsClosedImmersion (β e) := fun e =>
    have : IsClosedImmersion (thickTrans R I e) := .spec_of_surjective _ (hg e)
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hβ e).flip this
  have hsu : ∀ e, Surjective (β e) := fun e =>
    have : Surjective (thickTrans R I e) :=
      surjective_spec_of_nilpotent_ker _ (hg e) (isNilpotent_ker_factor I e)
    MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip this
  obtain ⟨G, hG0, hG⟩ := exists_orderIso_opens_tower (fun e => (Y e).left) β
  have hinj : ∀ e (U V : (Y (e + 1)).left.Opens), β e ⁻¹ᵁ U = β e ⁻¹ᵁ V → U = V := by
    intro e U V h
    ext x
    obtain ⟨y, rfl⟩ := (β e).surjective x
    exact Set.ext_iff.1 (congrArg (fun W : (Y e).left.Opens => (W : Set _)) h) y
  refine ⟨fun e S => G e (⨅ i ∈ S, nonzeroLocus (s i)), fun S => hG0 _, fun e S => hG e _,
    fun e S S' h => (G e).monotone (biInf_mono h), fun e S j => ?_, fun e => ?_, ?_⟩
  · beta_reduce
    rw [← map_inf, Finset.iInf_insert, Finset.iInf_singleton, inf_comm]
  · beta_reduce
    simp only [Finset.iInf_singleton]
    rw [← OrderIso.map_iSup, hV.1, OrderIso.map_top]
  · intro e S hS
    beta_reduce
    induction e with
    | zero =>
      rw [hG0]
      exact isAffineOpen_iInf_nonzeroLocus hV hS
    | succ e ih =>
      obtain ⟨D, hD, he⟩ := GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent
        _ _ _ (hg e) (isNilpotent_ker_factor I e) _ _ (Y (e + 1)).hom (Y e).hom (β e) (hβ e) _ ih
      rwa [hinj e _ _ (he.trans (hG e _).symm)] at hD

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightedSumDecompositionDenominators
section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Integral

def IntW (l K : ℕ) {r : ℕ} (v : (Fin r → ℕ) → ℚ) : Prop :=
  ∀ m, ∃ z : ℤ, (l : ℚ) ^ K * v m = z

theorem IntW.succ {l K r : ℕ} {v : (Fin r → ℕ) → ℚ} (h : IntW l K v) : IntW l (K + 1) v := by
  intro m
  obtain ⟨z, hz⟩ := h m
  refine ⟨l * z, ?_⟩
  push_cast
  rw [← hz, pow_succ]
  ring

theorem IntW.mono {l K K' r : ℕ} {v : (Fin r → ℕ) → ℚ} (h : IntW l K v) (hK : K ≤ K') :
    IntW l K' v := by
  induction K', hK using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact ih.succ

theorem IntW.neg_one_pow_mul {l K r : ℕ} {v : (Fin r → ℕ) → ℚ} (h : IntW l K v) (c : ℕ) :
    IntW l K (fun m => (-1 : ℚ) ^ c * v m) := by
  intro m
  obtain ⟨z, hz⟩ := h m
  refine ⟨(-1) ^ c * z, ?_⟩
  push_cast
  rw [← hz]
  ring

theorem int_sum {α : Type} (s : Finset α) (q : ℚ) (f : α → ℚ)
    (h : ∀ a ∈ s, ∃ z : ℤ, q * f a = z) : ∃ z : ℤ, q * ∑ a ∈ s, f a = z := by
  classical
  choose! g hg using h
  refine ⟨∑ a ∈ s, g a, ?_⟩
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl hg

theorem partialSum_int {l K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (h : IntW l K v) :
    IntW l K (partialSum i v) :=
  fun m => int_sum _ _ _ fun k _ => h _

theorem intW_partialSumMean {l K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l) (h : IntW l K v) :
    IntW l (K + 1) (meanP l i v) := by
  intro m
  have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne'
  obtain ⟨z, hz⟩ := int_sum (Finset.range l) ((l : ℚ) ^ K)
    (fun k => partialSum i v (Function.update m i k)) (fun k _ => partialSum_int h _)
  refine ⟨z, ?_⟩
  rw [← hz, meanP, pow_succ]
  field_simp

theorem aop_int {l K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l) (h : IntW l K v) :
    IntW l (K + 1) (Aop l i v) := by
  intro m
  obtain ⟨a, ha⟩ := (partialSum_int (i := i) h).succ (m + Pi.single i 1)
  obtain ⟨b, hb⟩ := intW_partialSumMean (i := i) hl h m
  refine ⟨a - b, ?_⟩
  push_cast
  rw [← ha, ← hb, Aop]
  ring

theorem bop_int {l K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l) (h : IntW l K v) :
    IntW l (K + 1) (Bop l i v) := by
  intro m
  by_cases h0 : m i = 0
  · simpa [Bop, h0] using intW_partialSumMean (i := i) hl h m
  · exact ⟨0, by simp [Bop, h0]⟩

theorem iterate_int {l K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l) (h : IntW l K v)
    (c : ℕ) : IntW l (K + c) ((Aop l i)^[c] v) := by
  induction c with
  | zero => simpa using h
  | succ c ih =>
    rw [Function.iterate_succ_apply']
    exact aop_int hl ih

theorem uW_int {l N K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l) (h : IntW l K v)
    (c : Fin (N + 1)) : IntW l (K + (N + 1)) (OneVar.uW l N i v c) := by
  unfold OneVar.uW
  split_ifs with hc
  · have h1 : IntW l (K + c + 1) (Bop l i ((Aop l i)^[c] v)) := bop_int hl (iterate_int hl h c)
    exact (h1.mono (by omega)).neg_one_pow_mul _
  · exact ((iterate_int hl h N).mono (by omega)).neg_one_pow_mul _

theorem abel_oneVar_uW (r l N : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (hl : 0 < l) (hg : GoodAt l i v)
    (hb : BddW v) :
    (∀ c : Fin (N + 1), BddW (OneVar.uW l N i v c)) ∧
    (∀ c : Fin (N + 1), (c : ℕ) = N ∨ ∀ m, m i ≠ 0 → OneVar.uW l N i v c m = 0) ∧
    (∀ (c : Fin (N + 1)) k, k ≠ i → GoodAt l k v → GoodAt l k (OneVar.uW l N i v c)) ∧
    (∀ (c : Fin (N + 1)) k, k ≠ i → (∀ m, m k ≠ 0 → v m = 0) → ∀ m, m k ≠ 0 → OneVar.uW l N i v c m = 0) ∧
    ∀ g : (Fin r → ℕ) → ℂ, Summable g →
      ∑' m, (v m : ℂ) * g m =
        ∑ c : Fin (N + 1), ∑' m, (OneVar.uW l N i v c m : ℂ) * DL (List.replicate (c : ℕ) i) g m := by
  refine ⟨fun c => ?_, fun c => ?_, fun c k hk hgk => ?_, fun c k hk hsk => ?_, fun g hs => ?_⟩
  · unfold OneVar.uW
    beta_reduce
    split_ifs with h
    · have hc := OneVar.iterate_good_bdd hl hg hb c
      exact OneVar.bddW_sign _ (@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.aop_props r l i _ hl hc.1 hc.2).2.1
    · exact OneVar.bddW_sign _ (OneVar.iterate_good_bdd hl hg hb N).2
  · by_cases h : (c : ℕ) < N
    · refine Or.inr fun m hm => ?_
      simp [OneVar.uW, h, Bop, hm]
    · exact Or.inl (by have := c.isLt; omega)
  · unfold OneVar.uW
    beta_reduce
    split_ifs with h
    · exact OneVar.goodAt_smul _ ((@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar.otherVar_main r l i k _ hk).1 (OneVar.iterate_good_other hk hgk c)).2
    · exact OneVar.goodAt_smul _ (OneVar.iterate_good_other hk hgk N)
  · intro m hm
    unfold OneVar.uW
    beta_reduce
    split_ifs with h
    · simp [((@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar.otherVar_main r l i k _ hk).2 (OneVar.iterate_supp_other hk hsk c)).2 m hm]
    · simp [OneVar.iterate_supp_other hk hsk N m hm]
  · rw [OneVar.tsum_iterate hl hg hb hs N, Fin.sum_univ_castSucc, Finset.sum_range]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => ?_
      have hc : (c : ℕ) < N := c.isLt
      rw [← tsum_mul_left]
      refine tsum_congr fun m => ?_
      simp [OneVar.uW, hc, mul_assoc]
    · rw [← tsum_mul_left]
      refine tsum_congr fun m => ?_
      simp [OneVar.uW, mul_assoc]

theorem expansion_on_finset_int (r l N : ℕ) (w : (Fin r → ℕ) → ℚ) (hl : 0 < l) (hw : GoodWeight l w)
    (hz : ∀ m, ∃ z : ℤ, w m = z) (I : Finset (Fin r)) :
    ∃ (Q : Type) (_ : Fintype Q) (cs : Q → List (Fin r)) (u : Q → (Fin r → ℕ) → ℚ) (K : ℕ),
      (∀ q, BddW (u q)) ∧ (∀ q i, i ∉ I → GoodAt l i (u q) ∧ (cs q).count i = 0) ∧
      (∀ q i, i ∈ I → (cs q).count i = N ∨ ∀ m, m i ≠ 0 → u q m = 0) ∧
      (∀ q, IntW l K (u q)) ∧
      ∀ g : (Fin r → ℕ) → ℂ, Summable g →
        ∑' m, (w m : ℂ) * g m = ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) g m := by
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨Unit, inferInstance, fun _ => [], fun _ => w, 0,
      fun _ => GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.bddW_of_periodic r l w hl (fun i m => hw.1 m i),
      fun _ i _ => ⟨⟨fun m => hw.1 m i, fun m => hw.2 m i⟩, by simp⟩,
      fun _ i hi => absurd hi (by simp), fun _ m => ?_, fun g _ => by simp [DL]⟩
    obtain ⟨z, hz⟩ := hz m
    exact ⟨z, by simp [hz]⟩
  | insert a I ha ih =>
    obtain ⟨Q, _, cs, u, K, hb, hg, hs, hi, hid⟩ := ih
    have hP := fun q => abel_oneVar_uW r l N a (u q) hl (hg q a ha).1 (hb q)
    have h1 := fun q => (hP q).1
    have h2 := fun q => (hP q).2.1
    have h3 := fun q => (hP q).2.2.1
    have h4 := fun q => (hP q).2.2.2.1
    have h5 := fun q => (hP q).2.2.2.2
    refine ⟨Q × Fin (N + 1), inferInstance, fun p => List.replicate (p.2 : ℕ) a ++ cs p.1,
      fun p => OneVar.uW l N a (u p.1) p.2, K + (N + 1), fun p => h1 p.1 p.2, ?_, ?_,
      fun p => uW_int hl (hi p.1) p.2, ?_⟩
    · rintro ⟨q, c⟩ k hk
      have hka : k ≠ a := fun h => hk (h ▸ Finset.mem_insert_self _ _)
      have hkI : k ∉ I := fun h => hk (Finset.mem_insert_of_mem h)
      refine ⟨h3 q c k hka (hg q k hkI).1, ?_⟩
      simp [List.count_append, List.count_replicate, (hg q k hkI).2, hka.symm]
    · rintro ⟨q, c⟩ k hk
      by_cases hka : k = a
      · subst hka
        have h0 : (cs q).count k = 0 := (hg q k ha).2
        rcases h2 q c with h | h
        · left
          simp [List.count_append, h0, h]
        · exact Or.inr h
      · have hkI : k ∈ I := (Finset.mem_insert.1 hk).resolve_left hka
        have hak : a ≠ k := fun h => hka h.symm
        rcases hs q k hkI with h | h
        · left
          simp [List.count_append, List.count_replicate, hak, h]
        · exact Or.inr (h4 q c k hka h)
    · intro g hgs
      rw [hid g hgs, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [h5 q _ (GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_DL r (cs q) g hgs)]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [DL, List.foldr_append]

theorem expansion_all_variables_int : ∀ (r l N : ℕ) (w : (Fin r → ℕ) → ℚ), 0 < l → GoodWeight l w →
    (∀ m, ∃ z : ℤ, w m = z) →
    ∃ (Q : Type) (_ : Fintype Q) (cs : Q → List (Fin r)) (u : Q → (Fin r → ℕ) → ℚ) (K : ℕ),
      (∀ q, BddW (u q)) ∧ (∀ q i, (cs q).count i = N ∨ ∀ m, m i ≠ 0 → u q m = 0) ∧
      (∀ q m, ∃ z : ℤ, (l : ℚ) ^ K * u q m = z) ∧
      ∀ g : (Fin r → ℕ) → ℂ, Summable g →
        ∑' m, (w m : ℂ) * g m = ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) g m := by
  intro r l N w hl hw hz
  obtain ⟨Q, iQ, cs, u, K, hb, -, hs, hi, hid⟩ := expansion_on_finset_int r l N w hl hw hz Finset.univ
  exact ⟨Q, iQ, cs, u, K, hb, fun q i => hs q i (Finset.mem_univ i), hi, hid⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Integral
end
end

