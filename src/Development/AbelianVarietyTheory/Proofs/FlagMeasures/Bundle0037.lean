module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelativeLatticeVolumeOfDetValuation
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LatDet

theorem card_quot_pow {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {p : R}
    (hp : Irreducible p) (k : ℕ) :
    Nat.card (R ⧸ Ideal.span {p ^ k}) = Nat.card (R ⧸ Ideal.span {p}) ^ k := by
  haveI : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp.prime
  have hq := cardQuot_pow_of_prime (P := Ideal.span {p})
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hp.ne_zero) (i := k)
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply, Ideal.span_singleton_pow] at hq
  exact hq


open Module Submodule in
theorem card_coker {R M ι : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M] [Fintype ι] (b : Basis ι R M) {p : R} (hp : Irreducible p)
    (φ : M →ₗ[R] M) (hφ : Function.Injective φ) :
    ∃ m : ℕ, Associated (LinearMap.det φ) (p ^ m) ∧
      Nat.card (M ⧸ LinearMap.range φ) = Nat.card (R ⧸ Ideal.span {p}) ^ m :=
  _root_.GlobalTheory.CardQuotientPow.main b hp φ hφ

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem resQ_ne_zero {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) : resQ ϖ ≠ 0 := by
  unfold resQ
  rw [← hϖ.maximalIdeal_eq]
  haveI : Finite (𝒪[F] ⧸ IsLocalRing.maximalIdeal 𝒪[F]) := inferInstanceAs (Finite 𝓀[F])
  exact Nat.card_pos.ne'

theorem relIndex_map {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {W : Type} [AddCommGroup W] [Module F W]
    {ι : Type} [Fintype ι] (b : Module.Basis ι F W) (ψ : W →ₗ[F] W) (a : ℤ) (u : (𝒪[F])ˣ)
    (hd : LinearMap.det ψ = (ϖ : F) ^ a * ((u : 𝒪[F]) : F)) (W0 : AddSubgroup W)
    (hW : ∀ x, x ∈ W0 ↔ ∀ i, b.repr x i ∈ 𝒪[F]) (hψ : ∀ i j, b.repr (ψ (b j)) i ∈ 𝒪[F]) :
    ∃ m : ℕ, a = m ∧ (W0.map ψ.toAddMonoidHom).relIndex W0 = resQ ϖ ^ m :=
  _root_.UpperTheory.Reformulated.B.Yzb5.relIndex_map hϖ b ψ a u hd W0 hW hψ

theorem relVol_map : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {W : Type} [AddCommGroup W] [Module F W] {ι : Type} [Fintype ι] (b : Module.Basis ι F W) (φ : W ≃ₗ[F] W) (a : ℤ) (u : (𝒪[F])ˣ), LinearMap.det (φ : W →ₗ[F] W) = (ϖ : F) ^ a * ((u : 𝒪[F]) : F) → ∀ W0 : AddSubgroup W, (∀ x, x ∈ W0 ↔ ∀ i, b.repr x i ∈ 𝒪[F]) → (W0.map φ.toAddEquiv.toAddMonoidHom).relIndex W0 ≠ 0 ∧ W0.relIndex (W0.map φ.toAddEquiv.toAddMonoidHom) ≠ 0 ∧ relVol W0 (W0.map φ.toAddEquiv.toAddMonoidHom) = (resQ ϖ : ℝ) ^ (-a) := by
  intro F _ _ _ _ ϖ hϖ W _ _ ι _ b φ a u hd W0 hW
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hq := resQ_ne_zero hϖ
  haveI := Module.Finite.of_basis b
  haveI := Module.Free.of_basis b
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors 𝒪[F])
    (fun ij : ι × ι => b.repr (φ (b ij.2)) ij.1)
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    (nonZeroDivisors.ne_zero c.2) hϖ
  set d := Module.finrank F W
  set t : F := (ϖ : F) ^ n with ht
  have htO : t ∈ 𝒪[F] := pow_mem ϖ.2 n
  have h1 : ∀ i j, b.repr ((t • (φ : W →ₗ[F] W)) (b j)) i ∈ 𝒪[F] := by
    intro i j
    obtain ⟨y, hy⟩ := hc (i, j)
    have e1 : t = ((v : 𝒪[F]) : F) * ((c : 𝒪[F]) : F) := by
      rw [ht, mul_comm]; exact_mod_cast congrArg (fun x : 𝒪[F] => (x : F)) hv.symm
    have e2 : b.repr ((t • (φ : W →ₗ[F] W)) (b j)) i = ((v : 𝒪[F]) : F) * (y : F) := by
      have hy' : (y : F) = ((c : 𝒪[F]) : F) * b.repr (φ (b j)) i := hy
      rw [hy', ← mul_assoc, ← e1]
      simp
    rw [e2]
    exact mul_mem (v : 𝒪[F]).2 y.2
  have h2 : ∀ i j, b.repr ((t • (LinearMap.id : W →ₗ[F] W)) (b j)) i ∈ 𝒪[F] := by
    intro i j
    simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    split_ifs
    · simpa using htO
    · simp
  obtain ⟨m1, hm1, i1⟩ := relIndex_map hϖ b _ (n * d + a) u (by
    rw [LinearMap.det_smul, hd, zpow_add₀ h0, ht, ← pow_mul, ← zpow_natCast, mul_assoc]
    push_cast; rfl) W0 hW h1
  obtain ⟨m2, hm2, i2⟩ := relIndex_map hϖ b _ (n * d) 1 (by
    rw [LinearMap.det_smul, LinearMap.det_id, ht, ← pow_mul, ← zpow_natCast]
    push_cast; rfl) W0 hW h2
  set A := W0.map φ.toAddEquiv.toAddMonoidHom with hA
  set B := W0.map (t • (φ : W →ₗ[F] W)).toAddMonoidHom with hB
  have hBe : B = (W0.map (t • (LinearMap.id : W →ₗ[F] W)).toAddMonoidHom).map
      φ.toAddEquiv.toAddMonoidHom := by
    rw [hB, AddSubgroup.map_map]
    congr 1
    ext x
    simp
  have i3 : B.relIndex A = resQ ϖ ^ m2 := by
    rw [hBe, hA, AddSubgroup.relIndex_map_map_of_injective _ _ φ.injective, i2]
  have hle : ∀ ψ : W →ₗ[F] W, (∀ i j, b.repr (ψ (b j)) i ∈ 𝒪[F]) →
      W0.map ψ.toAddMonoidHom ≤ W0 := by
    rintro ψ hψ _ ⟨x, hx, rfl⟩
    rw [hW]
    intro i
    have : b.repr (ψ.toAddMonoidHom x) i = ∑ j, b.repr x j * b.repr (ψ (b j)) i := by
      change b.repr (ψ x) i = _
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [← b.sum_repr x, map_sum, map_sum, Finsupp.finsetSum_apply]
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rw [this]
    exact sum_mem fun j _ => mul_mem ((hW x).1 hx j) (hψ i j)
  have hBW : B ≤ W0 := hle _ h1
  have hBA : B ≤ A := by
    rw [hBe, hA]; exact AddSubgroup.map_mono (hle _ h2)
  have t1 := AddSubgroup.relIndex_mul_relIndex B (A ⊓ W0) W0 (le_inf hBA hBW) inf_le_right
  have t2 := AddSubgroup.relIndex_mul_relIndex B (A ⊓ W0) A (le_inf hBA hBW) inf_le_left
  rw [AddSubgroup.inf_relIndex_right, i1] at t1
  rw [AddSubgroup.inf_relIndex_left, i3] at t2
  have n1 := mul_ne_zero_iff.1 (t1 ▸ pow_ne_zero m1 hq)
  have n2 := mul_ne_zero_iff.1 (t2 ▸ pow_ne_zero m2 hq)
  refine ⟨n1.2, n2.2, ?_⟩
  have hq' : (resQ ϖ : ℝ) ≠ 0 := by exact_mod_cast hq
  have c0 : (B.relIndex (A ⊓ W0) : ℝ) ≠ 0 := by exact_mod_cast n1.1
  have t1' : (B.relIndex (A ⊓ W0) : ℝ) * A.relIndex W0 = (resQ ϖ : ℝ) ^ m1 := by exact_mod_cast t1
  have t2' : (B.relIndex (A ⊓ W0) : ℝ) * W0.relIndex A = (resQ ϖ : ℝ) ^ m2 := by exact_mod_cast t2
  have ea : -a = (m2 : ℤ) - m1 := by omega
  unfold relVol
  rw [ea, zpow_sub₀ hq', zpow_natCast, zpow_natCast, ← t1', ← t2', mul_div_mul_left _ _ c0]

end GlobalTheory.HL.LatDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameOnto
open GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem mem_unipOn {n : ℕ} {A B : Submodule E (Fin n → E)} (hBA : B ≤ A)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (h1 : ∀ v ∈ A, g v - v ∈ B) (h2 : ∀ v ∈ A, g⁻¹ v - v ∈ B) :
    g ∈ unipOn A B := by
  refine ⟨fun v => ⟨fun hv => ?_, fun hv => ?_⟩, h1⟩
  · have h3 := A.add_mem (hBA (h2 _ hv)) hv
    have h4 : g⁻¹ (g v) = v := g.symm_apply_apply v
    rwa [h4, sub_add_cancel] at h3
  · simpa using A.add_mem (hBA (h1 _ hv)) hv

theorem spanTo_mono (g : Fin (r + 1) → S.V) {a b : ℕ} (h : a ≤ b) : S.spanTo g a ≤ S.spanTo g b :=
  Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)

theorem mem_spanTo (g : Fin (r + 1) → S.V) {i : Fin (r + 1)} {a : ℕ} (h : (i : ℕ) < a) :
    g i ∈ S.spanTo g a := Submodule.subset_span ⟨i, h, rfl⟩

theorem hf_spanTo (g : Fin (r + 1) → S.V) {a : ℕ} {v w : S.V} (hv : v ∈ S.spanTo g a)
    (h : ∀ i : Fin (r + 1), (i : ℕ) < a → hf L S.Hm (g i) w = 0) : hf L S.Hm v w = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨i, hi, rfl⟩ := hx; exact h i hi
  | zero => simp [hf]
  | add x y _ _ hx hy => rw [hf_add_l, hx, hy, add_zero]
  | smul c x _ hx => rw [hf_smul_l, hx, mul_zero]

theorem coords (g : Fin (r + 1) → S.V) {a : ℕ} {v : S.V} (hv : v ∈ S.spanTo g a) :
    ∃ c : Fin (r + 1) → E, (∀ i : Fin (r + 1), a ≤ (i : ℕ) → c i = 0) ∧ v = ∑ i, c i • g i := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨Pi.single i 1, fun j hj => ?_, ?_⟩
    · have hi' : (i : ℕ) < a := hi
      rw [Pi.single_eq_of_ne]
      rintro rfl
      omega
    · simp [Pi.single_apply]
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨d, hd, rfl⟩ := hy
    exact ⟨c + d, fun i hi => by simp [hc i hi, hd i hi], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul t x _ hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨t • c, fun i hi => by simp [hc i hi], by simp [Finset.smul_sum, smul_smul]⟩

variable (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (T : Fˣ)
  (gram : ∀ a b, hf L S.Hm (g a) (g b) =
    if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T else 0)
  (dual : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)

include gram in
theorem mem_perp (j : Fin (r + 1)) : g j ∈ perp L S.Hm (S.spanTo g r) := by
  intro y hy
  rw [← hf_cj L S.herm.1, hf_spanTo S g hy, map_zero]
  intro i hi
  rw [gram, if_neg]
  rintro ⟨rfl, -⟩
  simp at hi

include gram in
theorem spanTo_le_perp : S.spanTo g r ≤ perp L S.Hm (S.spanTo g r) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, -, rfl⟩
  exact mem_perp S g T gram i


include gram in
theorem exists_matrix (n : S.GLV) (hn : n ∈ S.Nof g) :
    ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧
      ∀ j, n (g j) = ∑ i, s i j • g i := by
  have key : ∀ j : Fin (r + 1), n (g j) - g j ∈ S.spanTo g j := by
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · exact hn.2.2 _ (mem_perp S g T gram _)
    · exact (Subgroup.mem_iInf.1 hn.1.2 j).2 _ (mem_spanTo S g (by simp))
  choose c hc hc' using fun j => coords S g (key j)
  refine ⟨fun i j => c j i + if i = j then 1 else 0, ⟨fun i j hij => ?_, fun i => ?_⟩, fun j => ?_⟩
  · simp [hc j i hij.le, hij.ne']
  · simp [hc i i le_rfl]
  · simp [add_smul, Finset.sum_add_distrib, ← hc' j]

include gram dual in
theorem exists_dual (j : Fin (r + 1)) : ∃ u : S.V, ∀ i, hf L S.Hm (g i) u = if i = j then 1 else 0 := by
  refine Fin.lastCases ?_ (fun j => ⟨gs j, fun i => dual i j⟩) j
  refine ⟨algebraMap F E (-(T : F)⁻¹) • g (Fin.last r), fun i => ?_⟩
  rw [hf_smul_r, gram, AlgEquiv.commutes]
  by_cases h : i = Fin.last r
  · simp [h, ← map_mul]
  · simp [h]


include gram dual in
theorem exists_step [IsNonarchimedeanLocalField F] [CharZero F] (j : Fin (r + 1)) (x : S.V)
    (hx : x ∈ S.spanTo g j) :
    ∃ n ∈ S.Nof g, n (g j) = g j + x ∧ (∀ i, i ≠ j → n (g i) = g i) ∧
      ∀ v ∈ S.spanTo g j, n v = v := by
  obtain ⟨u, hu⟩ := exists_dual S g gs T gram dual j
  have hjr : (j : ℕ) ≤ r := Nat.lt_succ_iff.1 j.2
  have hxX : x ∈ S.spanTo g r := spanTo_mono S g hjr hx
  have hlow : ∀ v ∈ S.spanTo g j, hf L S.Hm v u = 0 := fun v hv =>
    hf_spanTo S g hv fun i hi => by
      rw [hu, if_neg]
      rintro rfl
      omega
  have hux : hf L S.Hm u x = 0 := by rw [← hf_cj L S.herm.1, hlow x hx, map_zero]
  have hs : algebraMap F E 2⁻¹ * hf L S.Hm u u + L.cj (algebraMap F E 2⁻¹ * hf L S.Hm u u) =
      hf L S.Hm u u := by
    rw [map_mul, AlgEquiv.commutes, hf_cj L S.herm.1, ← add_mul, ← map_add (f := _)]
    norm_num
  obtain ⟨n, hn, h1, h2⟩ := eichler_isometry L S.Hm S.herm x u _
    (spanTo_le_perp S g T gram hxX x hxX) hux hs
  have e1 : ∀ v ∈ perp L S.Hm (S.spanTo g r), n v - v = hf L S.Hm v u • x := fun v hv => by
    rw [h1, eich, hv x hxX]; simp
  have e2 : ∀ v ∈ perp L S.Hm (S.spanTo g r), n⁻¹ v - v = -(hf L S.Hm v u • x) := fun v hv => by
    rw [h2, eich, hv x hxX, hf_neg_r]; simp
  have e3 : ∀ l : Fin r, ∀ v ∈ S.spanTo g (l + 1), hf L S.Hm v u • x ∈ S.spanTo g l := by
    intro l v hv
    by_cases h : (j : ℕ) ≤ l
    · exact Submodule.smul_mem _ _ (spanTo_mono S g h hx)
    · rw [hlow v (spanTo_mono S g (by omega) hv)]; simp
  refine ⟨n, ⟨⟨hn, Subgroup.mem_iInf.2 fun l => ?_⟩, ?_⟩, ?_, fun i hi => ?_, fun v hv => ?_⟩
  · have hl : S.spanTo g (l + 1) ≤ perp L S.Hm (S.spanTo g r) :=
      (spanTo_mono S g l.2).trans (spanTo_le_perp S g T gram)
    refine mem_unipOn (spanTo_mono S g (Nat.le_succ _)) n (fun v hv => ?_) (fun v hv => ?_)
    · rw [e1 v (hl hv)]; exact e3 l v hv
    · rw [e2 v (hl hv)]; exact Submodule.neg_mem _ (e3 l v hv)
  · refine mem_unipOn (spanTo_le_perp S g T gram) n (fun v hv => ?_) (fun v hv => ?_)
    · rw [e1 v hv]; exact Submodule.smul_mem _ _ hxX
    · rw [e2 v hv]; exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hxX)
  · have := e1 _ (mem_perp S g T gram j)
    rw [hu, if_pos rfl, one_smul] at this
    rw [← this]; abel
  · have := e1 _ (mem_perp S g T gram i)
    rw [hu, if_neg hi, zero_smul] at this
    exact sub_eq_zero.1 this
  · have := e1 _ (spanTo_le_perp S g T gram (spanTo_mono S g hjr hv))
    rw [hlow v hv, zero_smul] at this
    exact sub_eq_zero.1 this

include gram dual in
theorem exists_upto [IsNonarchimedeanLocalField F] [CharZero F] (x : Fin (r + 1) → S.V)
    (hx : ∀ j : Fin (r + 1), x j ∈ S.spanTo g j) (m : ℕ) :
    ∃ n ∈ S.Nof g, ∀ j : Fin (r + 1), n (g j) = if (j : ℕ) < m then g j + x j else g j := by
  induction m with
  | zero => exact ⟨1, one_mem _, fun j => by simp⟩
  | succ m ih =>
    obtain ⟨n, hn, h⟩ := ih
    by_cases hm : m < r + 1
    · obtain ⟨e, he, h1, h2, h3⟩ := exists_step S g gs T gram dual ⟨m, hm⟩ _ (hx ⟨m, hm⟩)
      refine ⟨e * n, mul_mem he hn, fun j => ?_⟩
      change e (n (g j)) = _
      rw [h]
      rcases lt_trichotomy (j : ℕ) m with hj | hj | hj
      · rw [if_pos hj, if_pos (by omega)]
        exact h3 _ (add_mem (mem_spanTo S g hj) (spanTo_mono S g hj.le (hx j)))
      · obtain rfl : j = ⟨m, hm⟩ := Fin.ext hj
        rw [if_neg (by simp), if_pos (by simp), h1]
      · rw [if_neg (by omega), if_neg (by omega)]
        exact h2 j fun hh => by rw [hh] at hj; simp at hj
    · refine ⟨n, hn, fun j => ?_⟩
      have := j.2
      rw [h, if_pos (by omega), if_pos (by omega)]


include gram dual in
theorem exists_elt [IsNonarchimedeanLocalField F] [CharZero F]
    (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hs : (∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) :
    ∃ n ∈ S.Nof g, ∀ j, n (g j) = ∑ i, s i j • g i := by
  have hx : ∀ j : Fin (r + 1), ∑ i ∈ Finset.univ.erase j, s i j • g i ∈ S.spanTo g j := by
    intro j
    refine Submodule.sum_mem _ fun i hi => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with h | h
    · exact Submodule.smul_mem _ _ (mem_spanTo S g h)
    · rw [hs.1 i j h]; simp
  obtain ⟨n, hn, h⟩ := exists_upto S g gs T gram dual _ hx (r + 1)
  refine ⟨n, hn, fun j => ?_⟩
  rw [h, if_pos j.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), hs.2, one_smul]

end

theorem unipotent_onto : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ n ∈ S.N, ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ ∀ j, n (S.f j) = ∑ i, s i j • S.f i) ∧ (∀ n ∈ S.N', ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ ∀ j, n (S.f' j) = ∑ i, s i j • S.f' i) ∧ ∀ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) → (∃ n ∈ S.N, ∀ j, n (S.f j) = ∑ i, s i j • S.f i) ∧ ∃ n ∈ S.N', ∀ j, n (S.f' j) = ∑ i, s i j • S.f' i := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  exact ⟨exists_matrix S S.f S.T S.gram, exists_matrix S S.f' S.T' S.gram', fun s hs =>
    ⟨exists_elt S S.f S.es S.T S.gram S.dual s hs, exists_elt S S.f' S.es' S.T' S.gram' S.dual' s hs⟩⟩

end GlobalTheory.HL.FrameOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqNormSumRepsMulIndexLe
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical ComplexConjugate

namespace GlobalTheory.HL.GaussSum

theorem sq_norm_sum_mul_index_le {G : Type*} [AddCommGroup G] [Fintype G] (Q : AddSubgroup G)
    (f : G → ℂ) (hf : ∀ u, ‖f u‖ = 1)
    (hQ : ∀ h, h ∉ Q → ∃ (v : G) (c : ℂ), c ≠ 1 ∧
      ∀ u, f (u + v + h) * conj (f (u + v)) = c * (f (u + h) * conj (f u))) :
    ‖∑ u, f u‖ ^ 2 * (Q.index : ℝ) ≤ (Fintype.card G : ℝ) ^ 2 := by
  classical
  have hzero : ∀ h, h ∉ Q → ∑ u, f (u + h) * conj (f u) = 0 := by
    intro h hh
    obtain ⟨v, c, hc, hrel⟩ := hQ h hh
    have h1 : ∑ u, f (u + h) * conj (f u) = c * ∑ u, f (u + h) * conj (f u) := by
      rw [Finset.mul_sum]
      calc ∑ u, f (u + h) * conj (f u) = ∑ u, f (u + v + h) * conj (f (u + v)) :=
            (Fintype.sum_equiv (Equiv.addRight v) (fun u => f (u + v + h) * conj (f (u + v)))
              (fun u => f (u + h) * conj (f u)) (fun u => rfl)).symm
        _ = ∑ u, c * (f (u + h) * conj (f u)) := Finset.sum_congr rfl fun u _ => hrel u
    have h2 : (1 - c) * ∑ u, f (u + h) * conj (f u) = 0 := by
      rw [sub_mul, one_mul, ← h1, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3).symm hc
    · exact h3
  have hexp : (∑ u, f u) * conj (∑ u, f u) = ∑ h, ∑ u, f (u + h) * conj (f u) := by
    calc (∑ u, f u) * conj (∑ u, f u) = ∑ w, ∑ u, f w * conj (f u) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, Finset.sum_mul_sum]
      _ = ∑ u, ∑ w, f w * conj (f u) := Finset.sum_comm
      _ = ∑ u, ∑ h, f (u + h) * conj (f u) := Finset.sum_congr rfl fun u _ =>
          (Fintype.sum_equiv (Equiv.addLeft u) (fun h => f (u + h) * conj (f u))
            (fun w => f w * conj (f u)) (fun h => rfl)).symm
      _ = ∑ h, ∑ u, f (u + h) * conj (f u) := Finset.sum_comm
  have hnorm : ‖∑ u, f u‖ ^ 2 ≤ (Fintype.card G : ℝ) * (Nat.card Q : ℝ) := by
    calc ‖∑ u, f u‖ ^ 2 = ‖(∑ u, f u) * conj (∑ u, f u)‖ := by
          rw [norm_mul, RCLike.norm_conj, sq]
      _ = ‖∑ h, ∑ u, f (u + h) * conj (f u)‖ := by rw [hexp]
      _ ≤ ∑ h, ‖∑ u, f (u + h) * conj (f u)‖ := norm_sum_le _ _
      _ ≤ ∑ h, (if h ∈ Q then (Fintype.card G : ℝ) else 0) := by
          refine Finset.sum_le_sum fun h _ => ?_
          split_ifs with hh
          · calc ‖∑ u, f (u + h) * conj (f u)‖ ≤ ∑ u, ‖f (u + h) * conj (f u)‖ :=
                  norm_sum_le _ _
              _ = ∑ _u : G, (1 : ℝ) := by simp [hf]
              _ = Fintype.card G := by simp
          · rw [hzero h hh, norm_zero]
      _ = (Fintype.card G : ℝ) * (Nat.card Q : ℝ) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
            mul_comm]
          congr 1
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hci : (Nat.card Q : ℝ) * (Q.index : ℝ) = Fintype.card G := by
    rw [← Nat.card_eq_fintype_card, ← AddSubgroup.card_mul_index (H := Q)]
    push_cast
    ring
  calc ‖∑ u, f u‖ ^ 2 * (Q.index : ℝ) ≤ (Fintype.card G : ℝ) * Nat.card Q * Q.index :=
        mul_le_mul_of_nonneg_right hnorm (Nat.cast_nonneg _)
    _ = (Fintype.card G : ℝ) ^ 2 := by rw [mul_assoc, hci, sq]

theorem sq_norm_sum_reps_mul_index_le {M : Type*} [AddCommGroup M] (P Q : AddSubgroup M)
    (hPQ : P ≤ Q) (R : Finset M) (hR : ∀ u, ∃! w, w ∈ R ∧ u - w ∈ P)
    (f : M → ℂ) (hf : ∀ u, ‖f u‖ = 1) (hP : ∀ u, ∀ p ∈ P, f (u + p) = f u)
    (hQ : ∀ h, h ∉ Q → ∃ (v : M) (c : ℂ), c ≠ 1 ∧
      ∀ u, f (u + v + h) * conj (f (u + v)) = c * (f (u + h) * conj (f u))) :
    ‖∑ u ∈ R, f u‖ ^ 2 * (Q.index : ℝ) ≤ (R.card : ℝ) ^ 2 := by
  classical
  have hsurj : ∀ x : M ⧸ P, ∃ w ∈ R, (w : M ⧸ P) = x := by
    intro x
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨w, ⟨hwR, hw⟩, -⟩ := hR u
    refine ⟨w, hwR, ?_⟩
    rw [QuotientAddGroup.eq]
    have e : -w + u = u - w := by abel
    rw [e]
    exact hw
  have hinj : ∀ w ∈ R, ∀ w' ∈ R, (w : M ⧸ P) = w' → w = w' := by
    intro w hw w' hw' h
    rw [QuotientAddGroup.eq] at h
    obtain ⟨z, -, hz⟩ := hR w
    have h1 : w = z := hz w ⟨hw, by simp⟩
    have h2 : w' = z := hz w' ⟨hw', by
      rw [show w - w' = -(-w + w') by abel]
      exact P.neg_mem h⟩
    rw [h1, h2]
  have : Finite (M ⧸ P) := by
    apply Finite.of_surjective (fun w : R => ((w : M) : M ⧸ P))
    intro x
    obtain ⟨w, hw, rfl⟩ := hsurj x
    exact ⟨⟨w, hw⟩, rfl⟩
  let : Fintype (M ⧸ P) := Fintype.ofFinite _
  have hf' : ∀ u : M, f ((u : M ⧸ P)).out = f u := by
    intro u
    have h := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (u : M ⧸ P))
    have e := hP ((u : M ⧸ P)).out _ h
    rw [add_neg_cancel_left] at e
    exact e.symm
  have h1 := GlobalTheory.HL.GaussSum.sq_norm_sum_mul_index_le (Q.map (QuotientAddGroup.mk' P))
    (fun x : M ⧸ P => f x.out) (fun x => hf _) (by
      intro h' hh'
      obtain ⟨h, rfl⟩ := QuotientAddGroup.mk_surjective h'
      have hhQ : h ∉ Q := fun hq => hh' (AddSubgroup.mem_map_of_mem _ hq)
      obtain ⟨v, c, hc, hrel⟩ := hQ h hhQ
      refine ⟨(v : M ⧸ P), c, hc, fun x => ?_⟩
      obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
      simp only [← QuotientAddGroup.mk_add, hf']
      exact hrel u)
  have hidx : (Q.map (QuotientAddGroup.mk' P)).index = Q.index :=
    AddSubgroup.index_map_eq (H := Q) (QuotientAddGroup.mk'_surjective P)
      (by rw [QuotientAddGroup.ker_mk']; exact hPQ)
  have hi1 : ∀ a ∈ R, ((a : M ⧸ P)) ∈ (Finset.univ : Finset (M ⧸ P)) :=
    fun _ _ => Finset.mem_univ _
  have hi2 : Set.InjOn (fun a : M => (a : M ⧸ P)) R := by
    intro w hw w' hw' h
    exact hinj w hw w' hw' h
  have hi3 : Set.SurjOn (fun a : M => (a : M ⧸ P)) R (↑(Finset.univ : Finset (M ⧸ P)) : Set (M ⧸ P)) := by
    intro x _
    obtain ⟨w, hw, rfl⟩ := hsurj x
    exact ⟨w, hw, rfl⟩
  have hsum : ∑ u ∈ R, f u = ∑ x : M ⧸ P, f x.out :=
    Finset.sum_nbij (fun a : M => (a : M ⧸ P)) hi1 hi2 hi3 (fun u _ => (hf' u).symm)
  have hcard : R.card = Fintype.card (M ⧸ P) := by
    rw [← Finset.card_univ]
    exact Finset.card_nbij (fun a : M => (a : M ⧸ P)) hi1 hi2 hi3
  rw [hsum, hcard, ← hidx]
  exact h1

theorem mul_conj_eq {A : Type*} [AddCommGroup A] (ψ : AddChar A ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x y : A) :
    ψ x * conj (ψ y) = ψ (x - y) := by
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, Complex.inv_def,
    Complex.normSq_eq_norm_sq, h y]
  simp

end GlobalTheory.HL.GaussSum
end

