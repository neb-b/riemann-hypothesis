module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedLevelPatternToFramePlaces
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory.PatPlaces

theorem zPos_surj {κ τ l j p : ℕ} (hp : p < κ + l + j * τ) :
    ∃ a : Ix (Fin κ ⊕ Fin l) (Fin τ) j, zPos a = p := by
  by_cases h1 : p < κ
  · exact ⟨.inl (.inl ⟨p, h1⟩), rfl⟩
  by_cases h2 : p < κ + l
  · exact ⟨.inl (.inr ⟨p - κ, by omega⟩), by simp only [zPos]; omega⟩
  · have hτ : 0 < τ := by
      rcases Nat.eq_zero_or_pos τ with h | h
      · subst h; simp at hp; omega
      · exact h
    have hq : p - (κ + l) < τ * j := by rw [mul_comm]; omega
    refine ⟨.inr (⟨(p - (κ + l)) / τ, Nat.div_lt_of_lt_mul hq⟩, ⟨(p - (κ + l)) % τ, Nat.mod_lt _ hτ⟩), ?_⟩
    have := Nat.div_add_mod' (p - (κ + l)) τ
    simp only [zPos]; omega

theorem symIdx_cases (κ ρ i : ℕ) :
    (i < κ ∧ symIdx κ ρ i = i + ρ) ∨ (κ ≤ i ∧ i < κ + ρ ∧ symIdx κ ρ i = i - κ) ∨ (κ + ρ ≤ i ∧ symIdx κ ρ i = i) := by
  unfold symIdx; split_ifs <;> omega

theorem block_div {r τ i u : ℕ} (hu : u < τ) : (r + i * τ + u - r) / τ = i := by
  have : r + i * τ + u - r = u + τ * i := by rw [mul_comm]; omega
  rw [this, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hu, zero_add]

theorem pattern_to_places (F : Type) [Zero F] [One F] (κ ρ s τ j : ℕ) (R : ℕ → ℕ → F) :
    (∀ (a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j), ¬ FreeIx ρ a b → R (zPos a) (zPos b) = if a = b then 1 else 0) →
    ((∀ p', p' < κ + s + 1 → R p' p' = 1 ∧ ∀ p, p < κ + s + 1 + j * τ → p ≠ p' →
        (κ + s + 1 ≤ p ∨ symIdx κ ρ p' < symIdx κ ρ p ∨ (p' = κ + ρ ∧ p < κ)) → R p p' = 0) ∧
      (∀ p p', κ + s + 1 ≤ p' → p' < κ + s + 1 + j * τ → p < κ + s + 1 + j * τ →
        (p' - (κ + s + 1)) / τ < (p - (κ + s + 1)) / τ → R p p' = 0)) := by
  intro hR
  have key : ∀ a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j, a ≠ b → ¬ FreeIx ρ a b → R (zPos a) (zPos b) = 0 :=
    fun a b hab h => by rw [hR a b h, if_neg hab]
  refine ⟨fun p' hp' => ⟨?_, fun p hp hne hc => ?_⟩, fun p p' h1 h2 h3 h4 => ?_⟩
  · obtain ⟨b, rfl⟩ := zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p') (by omega)
    rw [hR b b ?_, if_pos rfl]
    rcases b with (i | i) | ⟨i, u⟩
    · simp [FreeIx, FreeTop]
    · simp [FreeIx, FreeTop]
    · simp only [zPos] at hp'; omega
  · obtain ⟨b, rfl⟩ := zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p') (by omega)
    obtain ⟨a, rfl⟩ := zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p) (by omega)
    refine key a b (fun h => hne (h ▸ rfl)) ?_
    have c1 := symIdx_cases κ ρ (zPos a)
    have c2 := symIdx_cases κ ρ (zPos b)
    rcases a with (i | i) | ⟨i, u⟩ <;> rcases b with (i' | i') | ⟨i', u'⟩ <;>
      simp only [zPos, FreeIx, FreeTop, Fin.lt_def, not_lt, not_false_eq_true] at hp' hp hne hc c1 c2 ⊢ <;> omega
  · obtain ⟨b, rfl⟩ := zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p') (by omega)
    obtain ⟨a, rfl⟩ := zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p) (by omega)
    rcases b with (i' | i') | ⟨i', u'⟩
    · simp only [zPos] at h1; omega
    · simp only [zPos] at h1; omega
    rcases a with (i | i) | ⟨i, u⟩
    · simp only [zPos] at h4; rw [show (i : ℕ) - (κ + s + 1) = 0 by omega, Nat.zero_div] at h4; exact absurd h4 (Nat.not_lt_zero _)
    · simp only [zPos] at h4; rw [show κ + (i : ℕ) - (κ + s + 1) = 0 by omega, Nat.zero_div] at h4; exact absurd h4 (Nat.not_lt_zero _)
    have e1 : κ + (s + 1) + (i' : ℕ) * τ + u' = κ + s + 1 + (i' : ℕ) * τ + u' := by omega
    have e2 : κ + (s + 1) + (i : ℕ) * τ + u = κ + s + 1 + (i : ℕ) * τ + u := by omega
    simp only [zPos] at h4
    rw [e1, e2, block_div u'.isLt, block_div u.isLt] at h4
    refine key _ _ (fun h => ?_) ?_
    · simp only [Sum.inr.injEq, Prod.mk.injEq] at h; rw [h.1] at h4; exact lt_irrefl _ h4
    · simp only [FreeIx, Fin.le_def, not_le]; exact h4

end GlobalTheory.PatPlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemStabLIff
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section

namespace GlobalTheory.StabRef

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem intAt_zero : IntAt P (0 : E) := by
  have := IntAt.coe P 0
  rwa [map_zero] at this

theorem intAt_sum {ι : Type} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) : IntAt P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (intAt_zero (P := P))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mem_locP' {n : ℕ} (L : Submodule (𝓞 E) (Sp E n)) (x : Sp E n) :
    x ∈ localization₂ P.asIdeal L ↔ ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ L := Iff.rfl

theorem mem_stdLat' {n : ℕ} (x : Sp E n) : x ∈ stdLat E n ↔ ∀ i, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x i := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]

theorem mem_locStd {n : ℕ} (x : Sp E n) : x ∈ localization₂ P.asIdeal (stdLat E n) ↔ ∀ i, IntAt P (x i) := by
  constructor
  · intro hx i
    obtain ⟨s, hs, h⟩ := (mem_locP' _ x).1 hx
    obtain ⟨r, hr⟩ := (mem_stdLat' _).1 h i
    exact ⟨r, s, hs, by rw [hr, Pi.smul_apply, Algebra.smul_def]⟩
  · intro H
    have : x = ∑ i, (Pi.single i (x i) : Sp E n) := (Finset.univ_sum_single x).symm
    rw [this]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨r, s, hs, h⟩ := H i
    refine (mem_locP' _ _).2 ⟨s, hs, ?_⟩
    have e : s • (Pi.single i (x i) : Sp E n) = Pi.single i (algebraMap (𝓞 E) E r) := by
      rw [← Pi.single_smul, Algebra.smul_def, ← h]
    rw [e]
    rw [mem_stdLat']
    intro j
    by_cases hj : j = i
    · subst hj
      exact ⟨r, by simp⟩
    · exact ⟨0, by simp [hj]⟩

theorem mem_sclLat {N : ℕ} (e : ℕ → ℤ) (v : Sp E N) :
    v ∈ LocE.sclLat P q N e ↔ ∀ l : Fin N, IntAt P (((q : E) ^ e l.1)⁻¹ * v l) := by
  unfold LocE.sclLat stdAt
  rw [Submodule.mem_comap, mem_locStd]
  simp [LinearMap.pi_apply, smul_eq_mul]

end GlobalTheory.StabRef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelCharacterByResidueCharacter
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymResidue

theorem dsum_shift {R : Type} [AddCommMonoid R] (n : ℕ) (f : ℕ → ℕ → R) :
    (∑ i : Fin n, ∑ j : Fin n, if (j : ℕ) = (i : ℕ) + 1 then f i j else 0) =
      ∑ i ∈ Finset.range (n - 1), f i (i + 1) := by
  have h1 : ∀ i : Fin n, (∑ j : Fin n, if (j : ℕ) = (i : ℕ) + 1 then f i j else 0) =
      if (i : ℕ) + 1 < n then f i ((i : ℕ) + 1) else 0 := by
    intro i
    rw [Fin.sum_univ_eq_sum_range (fun j => if j = (i : ℕ) + 1 then f i j else 0) n]
    simp [Finset.sum_ite_eq', Finset.mem_range]
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i + 1 < n then f i (i + 1) else 0) n]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem intAt_sum {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (f : ℕ → E)
    (h : ∀ i < n, IntAt P (f i)) : IntAt P (∑ i ∈ Finset.range n, f i) := by
  refine Finset.sum_induction f (IntAt P) (fun a b ha hb => IntAt.add ha hb) ?_ ?_
  · simpa using IntAt.coe P 0
  · intro i hi
    exact h i (Finset.mem_range.mp hi)

end GlobalTheory.SymResidue

open GlobalTheory.SymResidue in
theorem GlobalTheory.symLevel_lam_residue : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → ∀ (M : ℕ → ℕ → E), (∀ p p', p < κ + s + 1 → p' < κ + s + 1 → IntAt P (M p p')) → ∀ (g : S.P.J), (g : GL (Fin κ ⊕ Fin (s + 1)) k).val = Matrix.of (fun a b => ι (M (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) a) (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) b))) → ((S.P.lam g : ℂˣ) : ℂ) = σ₀ (ψ₀ (redP P (∑ i ∈ Finset.range (κ - 1), M i (i + 1) + ∑ i ∈ Finset.range (κ + s + 1 - κ - 1), M (κ + i) (κ + i + 1)))) := by
  intro E K k _ _ _ _ _ _ _ _ P q ι σ₀ ψ₀ χ s κ S hT M hM g hg
  have hent : ∀ a b, (g : GL (Fin κ ⊕ Fin (s + 1)) k).val a b =
      ι (M (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) a) (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) b)) := by
    intro a b; rw [hg]; rfl
  set A : E := ∑ i ∈ Finset.range (κ - 1), M i (i + 1) with hA
  set B : E := ∑ i ∈ Finset.range (κ + s + 1 - κ - 1), M (κ + i) (κ + i + 1) with hB
  have hAi : IntAt P A := intAt_sum P _ _ (fun i hi => hM _ _ (by omega) (by omega))
  have hBi : IntAt P B := intAt_sum P _ _ (fun i hi => hM _ _ (by omega) (by omega))
  have hsimple : GlobalTheory.RootEx.simpleSum (g : GL (Fin κ ⊕ Fin (s + 1)) k) = ι B := by
    unfold GlobalTheory.RootEx.simpleSum
    simp only [hent, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos, Sum.elim_inr]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [dsum_shift (s + 1) (fun i j => ι (M (κ + i) (κ + j))), hB, map_sum]
    have : κ + s + 1 - κ - 1 = s + 1 - 1 := by omega
    rw [this]
    rfl
  have hsuper : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum Fin.val (g : GL (Fin κ ⊕ Fin (s + 1)) k).val.toBlocks₁₁ = ι A := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, hent, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos, Sum.elim_inl]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [dsum_shift κ (fun i j => ι (M i j)), hA, map_sum]
  have hdiv : ∀ X : E, ((S.ϖ⁻¹ : kˣ) : k) * ι X = ι (X / (q : E)) := by
    intro X
    rw [Units.val_inv_eq_inv_val, hT.compl.unif, ← map_inv₀, ← map_mul, div_eq_inv_mul]
  rw [S.sym.2 g, hsimple, hsuper, hdiv, hdiv, hT.psi B hBi, hT.psi A hAi, ← map_mul,
    ← AddChar.map_add_eq_mul, ← reduction_add hBi hAi, add_comm B A]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToLocEqMapToMatrix
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory.SymBridge

theorem toLoc_eq_map_toMatrix' {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A]
    {N : ℕ} (e : A ≃ Fin N) (x : Sp E N →ₗ[E] Sp E N) :
    toLoc ι e e x = ((LinearMap.toMatrix' x).submatrix e e).map ι := by
  ext i j
  simp only [toLoc, Matrix.map_apply, Matrix.submatrix_apply, LinearMap.toMatrix'_apply]

theorem toLoc_comp_square {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A]
    {N : ℕ} (e : A ≃ Fin N) (x y : Sp E N →ₗ[E] Sp E N) :
    toLoc ι e e (x ∘ₗ y) = toLoc ι e e x * toLoc ι e e y := by
  rw [toLoc_eq_map_toMatrix', toLoc_eq_map_toMatrix', toLoc_eq_map_toMatrix', LinearMap.toMatrix'_comp,
    ← Matrix.submatrix_mul_equiv _ _ _ e _, Matrix.map_mul]

theorem toLoc_id_square {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A]
    {N : ℕ} (e : A ≃ Fin N) :
    toLoc ι e e (LinearMap.id : Sp E N →ₗ[E] Sp E N) = 1 := by
  rw [toLoc_eq_map_toMatrix', LinearMap.toMatrix'_id, Matrix.submatrix_one_equiv,
    Matrix.map_one _ ι.map_zero ι.map_one]

end GlobalTheory.SymBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZPosIxSuccInl
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.TopAgree

def zEquiv (κ l τ j : ℕ) : Ix (Fin κ ⊕ Fin l) (Fin τ) j ≃ Fin (κ + l + j * τ) :=
  (Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv

theorem zEquiv_val {κ l τ j : ℕ} (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) : (zEquiv κ l τ j a).val = zPos a := by
  rcases a with (i | i) | ⟨i, u⟩
  · simp [zEquiv, zPos]
  · simp [zEquiv, zPos]
  · simp [zEquiv, zPos]; ring

variable {E K : Type} [Field E] [NumberField E] [Field K] {P : HeightOneSpectrum (𝓞 E)}


open Classical in
def phiM (q : ℕ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ rS r t j N : ℕ)
    (M : ℕ → ℕ → E) : K :=
  if (∀ p p', p < N → p' < r + j * t → IntAt P (M p p')) ∧
      (∀ p p', r + j * t ≤ p → p < N → p' < r + j * t → IntAt P (M p p' / (q : E))) ∧
      (∀ p', p' < r → redP P (M p' p') = 1 ∧ ∀ p, p < r + j * t → p ≠ p' →
        (r ≤ p ∨ symIdx k₀ rS p' < symIdx k₀ rS p ∨ (p' = k₀ + rS ∧ p < k₀)) → redP P (M p p') = 0) ∧
      (∀ p p', r ≤ p' → p' < r + j * t → p < r + j * t → (p' - r) / t < (p - r) / t → redP P (M p p') = 0)
  then LocE.lamGvS ψ₀ χ k₀ r t j M *
    (LocE.unitV (χ j) (Matrix.det (Matrix.of fun s s' : Fin (r + j * t) => M s.1 s'.1)))⁻¹ else 0

theorem PhiGS_eq (q : ℕ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ rS r t j c' n' c n : ℕ) (x : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)) :
    LocE.PhiGS q ψ₀ χ k₀ rS r t (j + 1) c' n' c n x =
      phiM q ψ₀ χ k₀ rS r t j (n + c) (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x) := by
  rfl

variable {k : Type} [Field k]

theorem zPos_ixSucc_inl {κ l τ j : ℕ} (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) :
    zPos (ixSucc (Fin κ ⊕ Fin l) (Fin τ) j (Sum.inl a)) = zPos a := by
  rcases a with (i | i) | ⟨i, u⟩ <;> rfl

theorem zPos_ixSucc_inr {κ l τ j : ℕ} (u : Fin τ) :
    zPos (ixSucc (Fin κ ⊕ Fin l) (Fin τ) j (Sum.inr u)) = κ + l + j * τ + u := rfl

theorem zPos_lt {κ l τ j : ℕ} (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) : zPos a < κ + l + j * τ := by
  rw [← zEquiv_val]; exact (zEquiv κ l τ j a).isLt

theorem det_of_places (ι : E →+* k) {X : Type} [Fintype X] [DecidableEq X] {n : ℕ} (f : X ≃ Fin n) (pos : X → ℕ)
    (off : ℕ) (h : ∀ x, pos x = off + (f x).val) (M : ℕ → ℕ → E) :
    Matrix.det (Matrix.of fun x y => ι (M (pos x) (pos y))) =
      ι (Matrix.det (Matrix.of fun s s' : Fin n => M (off + s.1) (off + s'.1))) := by
  rw [RingHom.map_det, ← Matrix.det_submatrix_equiv_self f]
  congr 1
  ext x y
  simp [h]

end GlobalTheory.SymBridge.TopAgree
end
end

